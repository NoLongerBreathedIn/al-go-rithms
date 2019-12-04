{-# LANGUAGE TupleSections #-}
module RBMap (isCorrect, RBMap, empty, modifyLookup) where

import Data.Function (on)
import Data.Maybe
import Control.Monad (join)
import Control.Arrow ((&&&), second)

-- isRed contents l r
data RBTree a = Node Bool a (RBTree a) (RBTree a)
              | Leaf

-- parentRed rightChild parentContents sibling
data Crumb = Crumb Bool Bool a (RBTree a)

type Comp a = a -> a -> Ordering

data RBMap a b = RBMap (Comp a) (RBTree (a, b))

type TCont a = (RBTree a, [Crumb a])

tmap :: (a -> b) -> RBTree a -> RBTree b

instance Functor (RBMap a) where
  fmap f (RBMap c t) = RBMap c $ tmap (second f) t

isCorrect :: RBMap k v -> Bool
empty :: Comp k -> RBMap k v
modifyLookup :: k -> (Maybe v -> Maybe v) -> RBMap k v -> (RBMap k v, Maybe v)

empty = flip RBMap Leaf

topOut :: TCont a -> RBTree a
modify :: Maybe a -> TCont a -> TCont a
grabVal :: TCont (k, v) -> Maybe v
tlookup :: (a -> Ordering) -> RBTree a -> TCont a
modifyLookup k f (RBMap c t) = (RBMap c m, v) where
  v = grabVal t
  m = topOut $ modify ((k,) <$> f v) t
  t = tlookup (c k . fst) f

tmap _ Leaf = Leaf
tmap f (Node c o l r) = Node c (f o) (tmap f l) (tmap f r)

grabVal (Leaf, _) = Nothing
grabVal (Node _ (_, v) _ _, _) = Just v

look :: (a -> Ordering) -> TCont a -> TCont a
tlookup f = look f . (, [])

moveLeft :: TCont a -> TCont a
moveRight :: TCont a -> TCont a
moveUp :: TCont a -> TCont a
moveSib :: TCont a -> TCont a
moveDir :: Bool -> TCont a -> TCont a
moveLeft (Node c o l r, cs) = (l, Crumb c False o r : cs)
moveRight (Node c o l r, cs) = (r, Crumb c True o l : cs)
moveUp (k, (Crumb c d o s):cs) = (Node c o l r, cs) where
  (l, r) = if d then (s, k) else (k, s)
moveSib (k, (Crumb c d o s):cs) = (s, Crumb c (not d) o k : cs)
moveDir b = if b then moveRight else moveLeft

look f c@(Leaf, _) = c
look f c@(Node _ o _ _, _) = case f o of
  LT -> look f $ moveLeft c
  EQ -> c
  GT -> look f $ moveRight c

topOut (t, []) = t
topOut x = topOut $ moveUp x

deleteFocus :: TCont a -> TCont a
insertFixup :: TCont a -> TCont a

-- no new, leaf -> no change
modify Nothing c@(Leaf, _) = c

-- new, internal -> put in new contents
modify (Just o) (Node c _ l r, cs) = (Node c o l r, cs)

-- no new, internal -> delete
modify Nothing c = deleteFocus c

-- new, leaf -> insert
modify (Just o) (Leaf, c) = insertFixup (Node True o Leaf Leaf, c)

rotate :: TCont a -> TCont a
repaint :: Bool -> TCont a -> TCont a

rotate (Node cc co l r, (Crumb pc cr po s):cs) =
  (Node cc po nl nr, Crumb pc (not cr) co ns:cs)
  where (nl, nr, ns) = if cr then (s, l, r) else (r, s, l)

repaint c (Node _ o l r, cs) = (Node c o l r, cs)

-- Case 1: At root, repaint black
insertFixup c@(_, []) = repaint False c

-- Case 2: If parent is black, return
insertFixup c@(_, (Crumb False _ _ _):_) = c

-- Case 3: If uncle is red, recolor uncle, parent, grandparent,
-- and recurse on grandparent
insertFixup (n, (Crumb _ pd po s):(Crumb _ gd go (Node True uo ul ur)):cs) =
  insertFixup $ moveUp $
  moveUp (n, (Crumb False pd po s):(Crumb True gd go (Node False uo ul ur)):cs)

-- Case 4: If this direction is not parent direction, rotate here.
-- Then in any case, rotate on parent.
insertFixup c@(_, (Crumb _ pd _ _):(Crumb _ gd _ _):_) =
  rotate $ moveUp $ if pd == gd then c else rotate c

deleteFixup :: TCont a -> TCont a
moveToLast :: TCont a -> TCont a
getLastVal :: RBTree a -> a

-- If either kid is a leaf, move other kid, then fixup if was black
deleteFocus (Node c o Leaf r, cs) = (if c then id else deleteFixup) (r, cs)
deleteFocus (Node c o l Leaf, cs) = (if c then id else deleteFixup) (l, cs)
-- Else replace contents with predecessor's, then move to pred and try again.
deleteFocus (Node c o l r, cs) = deleteFocus $
  moveToLast (l, Crumb c False (getLastVal l) r : cs)

moveToLast c@(Node _ _ _ Leaf, _) = c
moveToLast c = moveToLast $ moveRight c

getLastVal (Node v _ _ Leaf) = v
getLastVal (Node _ _ _ r) = getLastVal r

-- Cases here are from a comment on the talk page on Wikipedia,
-- under 'Better deletion algorithm'. The first case matching is taken.

-- Case 1: The node is red. Color black, done.
deleteFixup (Node True o l r, cs) = (Node False o l r, cs)

-- Case 2: Node is root. Done.
deleteFixup c@(_, []) = c

-- Case 3: Sibling is red. Rotate at sibling, recurse (to cases 4-6)
deleteFixup c@(_, (Crumb _ d _ (Node True _ _ _)):_) =
  deleteFixup $ moveDir d $ rotate $ moveSib c

-- Case 4: Far nephew is red. Rotate at sibling,
-- point at far nephew (now uncle), recurse (to case 1)
deleteFixup c@(_, (Crumb _ d _ (Node _ _ (Node lnc _ _ _) (Node rnc _ _ _))):_)
  | if d then lnc else rnc = deleteFixup $ moveSib $ rotate $ moveSib c
-- Case 5: Near nephew is red. Rotate at near nephew, recurse (to case 4).
-- Here implemented by rotating at near nephew and then at sibling.
-- After moveDir d $ moveSib we are at near nephew.
-- After moveUp $ rotate we have rotated and are now at new sibling.
  | if d then rnc else lnc =
      deleteFixup $ moveSib $ rotate $ moveUp $ rotate $ moveDir d $ moveSib c
-- Case 6: Otherwise. Recolor sibling red, point at parent, recurse.
  | otherwise = deleteFixup $ moveUp $ repaint True $ moveSib c

checkBalance :: RBTree a -> Maybe Int
checkNoRR :: Bool -> RBTree a -> Bool
checkOrder :: Comp a -> RBTree a -> Maybe (Maybe (a, a))

isCorrect (RBMap f t) =
  isJust (checkBalance t) &&
  isJust (checkOrder (f `on` fst) t) &&
  checkNoRR False t

-- leaves are black
checkNoRR _ Leaf = True
-- children of red and of root should be black
checkNoRR x (Node True _ l r) = x && checkNoRR False l && checkNoRR False r
-- else go down
checkNoRR _ (Node False _ l r) = checkNoRR True l && checkNoRR True r

cBal x y | x == y = Just $ if iR then x else x + 1
         | otherwise = Nothing

-- ensure left and right subtrees are balanced, then make sure so is this
checkBalance Leaf = Just 0
checkBalance (Node iR _ l r) =
  join $ cBal iR <$> checkBalance l <*> checkBalance r

cOrd f c l r = if lc && rc then Just (Just (min, max)) else Nothing where
  (lc, min) = case l of
    Just (ll, lr) -> (f lr c == LT, ll)
    Nothing -> (True, c)
  (rc, max) = case r of
    Just (rl, rr) -> (f c rl == LT, rr)
    Nothing -> (True, c)

-- ensure left and right subtrees are ordered, then make sure so is this
checkOrder _ Leaf = Just Nothing
checkOrder f (Node _ c l r) =
  join $ cOrd f c <$> checkOrder l <*> checkOrder r
