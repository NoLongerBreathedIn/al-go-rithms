module RBTree

-- A faster implementation of RBTrees (no proofs)
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import RBTreeS

data RBTree : Bool -> Nat -> (k : Type) -> (k -> Type) -> Type where
  Lif : RBTree False Z k v
  Red : RBTree False n k v -> (m : k) -> v m ->
        RBTree False n k v -> RBTree True n k v
  Blk : RBTree lc n k v -> (m : k) -> v m ->
        RBTree rc n k v -> RBTree False (S n) k v

total rwRed : {l : RBTree False h k v} -> {l' : RBTree False h k v} ->
              {r : RBTree False h k v} -> {r' : RBTree False h k v} ->
              l = l' -> r = r' -> Red l m w r = Red l' m w r'
rwRed Refl Refl = Refl

total rwBlk : {l : RBTree lc h k v} -> {l' : RBTree lc h k v} ->
              {r : RBTree rc h k v} -> {r' : RBTree rc h k v} ->
              l = l' -> r = r' -> Blk l m w r = Blk l' m w r'
rwBlk Refl Refl = Refl

{-BEG_CLEAN-}
total cleanTree : RBTreeS c h k o b v -> RBTree c h k v
cleanTree LifS = Lif
cleanTree (RedS l m w r p) = Red (cleanTree l) m w (cleanTree r)
cleanTree (BlkS l m w r p) = Blk (cleanTree l) m w (cleanTree r)
{-END_CLEAN-}

export
record RBMap k (v : k -> Type) where
  constructor MkRBMap
  to : Comp k
  depth : Nat
  pf : TotalOrd k to
  contents : RBTree False depth k v

{-BEG_CLEAN-}
export
total clean : RBMapS k v -> RBMap k v
clean (MkRBMapS to depth bounds pf contents) =
  MkRBMap to depth pf (cleanTree contents)
{-END_CLEAN-}

export
total empty : (o : Comp k) -> TotalOrd k o -> RBMap k v
empty o p = MkRBMap o Z p Lif

{-BEG_LOOK-}
export
total lookup : (a : k) -> RBMap k v -> Maybe (v a)
{-END_LOOK-}

{-
export
total insert : (a : k) -> v a -> RBMap k v -> RBMap k v

export
total remove : k -> RBMap k v -> RBMap k v
-}

{-BEG_MAP-}
export
total mapmap : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               RBMap k v -> RBMap k v'
{-END_MAP-}

-- Theorems

{-BEG_THM-}
-- First, proof that everything commutes with clean

{-BEG_CLEAN-}
export
total cleanEmpty : (o : Comp k) -> (to : TotalOrd k o) ->
                   empty o to = clean (emptyS o to)

{-BEG_LOOK-}
export
total cleanLookup : (a : k) -> (m : RBMapS k v) ->
                    lookup a (clean m) = lookupS a m
{-END_LOOK-}

{-
export
total cleanInsert : (a : k) -> (w : v a) -> (m : RBMapS k v) ->
                    insert a w (clean m) = clean (insertS a w m)

export
total cleanRemove : (a : k) -> (m : RBMapS k v) ->
                    remove a (clean m) = clean (removeS a m)
-}

{-BEG_MAP-}
export
total cleanMapmap : {v' : k -> Type} ->
                    (f : (a : k) -> v a -> v' a) -> (m : RBMapS k v) ->
                    mapmap f (clean m) = clean (mapmapS f m)
{-END_MAP-}
{-END_CLEAN-}

-- Now the stuff we can prove without carrying the ordering around

{-BEG_LOOK-}
export
total lookupEmpty : (a : k) -> (o : Comp k) -> (t : TotalOrd k o) ->
                    lookup a (empty o t) = Nothing

{-BEG_MAP-}
export
total lookupMap : {v' : k -> Type} -> (a : k) ->
                  (f : (b : k) -> v b -> v' b) -> (m : RBMap k v) ->
                  lookup a (mapmap f m) = map (f a) (lookup a m)
{-END_LOOK-}

export
total mapmapId : (m : RBMap k v) -> mapmap (\b => id {a=v b}) m = m

export
total mapmapComp : {v' : k -> Type} -> {w : k -> Type} -> (m : RBMapS k v) ->
                   (f : (a : k) -> v a -> v' a) ->
                   (g : (a : k) -> v' a -> w a) ->
                   mapmap g (mapmap f m) = mapmap (\a => g a . f a) m

{-
export
total insertMap : {v' : k -> Type} -> (a : k) -> (w : v a) ->
                  (m : RBMap k v) ->
                  (f : (b : k) -> v b -> v' b) ->
                  insert a (f a w) (mapmap f m) = mapmap f (insert a w m)

export
total removeMap : {v' : k -> Type} -> (a : k) -> (m : RBMap k v) ->
                  (f : (b : k) -> v b -> v' b) ->
                  remove a (mapmap f m) = mapmap f (remove a m)
-}

export
total emptyMap : {v : k -> Type} -> {v' : k -> Type} ->
                 (o : Comp k) -> (p : TotalOrd k o) ->
                 (f : (b : k) -> v b -> v' b) ->
                 mapmap f (empty o p) = empty {v=v'} o p
{-END_MAP-}

{-
export
total removeEmpty : (a : k) -> (o : Comp k) -> (t : TotalOrd k o) ->
                    remove a (empty o t) = empty o t
-}
{-END_THM-}

-- Implementation

{-BEG_LOOK-}
mutual
  total lookTree : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                   RBTree c h k v -> Maybe (v a)
  total pickTree : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                   RBTree lc lh k v -> (m : k) -> v m -> RBTree rc rh k v ->
                   Maybe (v a)

{-BEG_DIMP-}
  pickTree o to a l m w r with (enh o a m)
    | LTE x = lookTree o to a l
    | EQE x = Just (replace (corff to x) w)
    | GTE x = lookTree o to a r

  lookTree o to a Lif = Nothing
  lookTree o to a (Red l m w r) = pickTree o to a l m w r
  lookTree o to a (Blk l m w r) = pickTree o to a l m w r
{-END_DIMP-}

lookup a (MkRBMap o d to t) = lookTree o to a t
{-END_LOOK-}

data RBCrumb : Bool -> Nat -> Nat -> (k : Type) -> (k -> Type) -> Type where
  Root : RBCrumb True h Z k v
  RedL : (m : k) -> v m -> RBTree False h k v ->
         RBCrumb False h d k v -> RBCrumb True h d k v
  RedR : RBTree False h k v -> (m : k) -> v m ->
         RBCrumb False h d k v -> RBCrumb True h d k v
  BlkL : (m : k) -> v m -> RBTree rc h k v ->
         RBCrumb pc (S h) d k v -> RBCrumb False h (S d) k v
  BlkR : RBTree lc h k v -> (m : k) -> v m ->
         RBCrumb pc (S h) d k v -> RBCrumb False h (S d) k v

total rwRedL : {c : RBTree False h k v} -> {c' : RBTree False h k v} ->
               {p : RBCrumb False h d k v} -> {p' : RBCrumb False h d k v} ->
               c = c' -> p = p' -> RedL m w c p = RedL m w c' p'
rwRedL Refl Refl = Refl
total rwRedR : {l : RBTree False h k v} -> {l' : RBTree False h k v} ->
               {p : RBCrumb False h d k v} -> {p' : RBCrumb False h d k v} ->
               c = c' -> p = p' -> RedR c m w p = RedR c' m w p'
rwRedR Refl Refl = Refl
total rwBlkL : {c : RBTree cc h k v} -> {c' : RBTree cc h k v} ->
               {p : RBCrumb pc (S h) d k v} -> {p' : RBCrumb pc (S h) d k v} ->
               c = c' -> p = p' -> BlkL m w c p = BlkL m w c' p'
rwBlkL Refl Refl = Refl
total rwBlkR : {c : RBTree cc h k v} -> {c' : RBTree cc h k v} ->
               {p : RBCrumb pc (S h) d k v} -> {p' : RBCrumb pc (S h) d k v} ->
               c = c' -> p = p' -> BlkR c m w p = BlkR c' m w p'
rwBlkR Refl Refl = Refl

{-BEG_CLEAN-}
total cleanCrumb : RBCrumbS c h d k o l r v -> RBCrumb c h d k v
cleanCrumb RootS = Root
cleanCrumb (RedLS m w r p f) = RedL m w (cleanTree r) (cleanCrumb p)
cleanCrumb (RedRS l m w p f) = RedR (cleanTree l) m w (cleanCrumb p)
cleanCrumb (BlkLS m w r p f) = BlkL m w (cleanTree r) (cleanCrumb p)
cleanCrumb (BlkRS l m w p f) = BlkR (cleanTree l) m w (cleanCrumb p)
{-END_CLEAN-}

total cfC : RBCrumb c h d k v -> Bool
cfC {c} cf = c
total cfPc : RBCrumb c h (S d) k v -> Bool
cfPc (RedL _ _ _ p) = cfC p
cfPc (RedR _ _ _ p) = cfC p
cfPc (BlkL _ _ _ p) = cfC p
cfPc (BlkR _ _ _ p) = cfC p

total RBZip : Bool -> Bool -> Nat -> Nat -> Nat ->
              (k : Type) -> (k -> Type) -> Type
RBZip cc pc ch ph pd k v = (RBTree cc ch k v, RBCrumb pc ph pd k v)

{-BEG_CLEAN-}
total cleanZip : RBZipS cc pc ch ph pd k o cb pl pr v ->
                 RBZip cc pc ch ph pd k v
cleanZip z = (cleanTree (child z), cleanCrumb (parnt z))
{-END_CLEAN-}

total zipUp : RBTree c h k v ->
              RBZip c True h h Z k v

zipUp t = MkRBZipS (t, Root)

{-BEG_CLEAN-}
total zipUpClean : (t : RBTreeS c h k o b v) ->
                   zipUp (cleanTree t) = cleanZip (zipUpS t)
{-END_CLEAN-}

{-BEG_MAP-}
total tmap : {v : k -> Type} -> ((a : k) -> v a -> v' a) ->
             RBTree c h k v -> RBTree c h k v'
tmap f Lif = Lif
tmap f (Red l m mv r) = Red (tmap f l) m (f m mv) (tmap f r)
tmap f (Blk l m mv r) = Blk (tmap f l) m (f m mv) (tmap f r)

mapmap f (MkRBMap to depth pf contents) =
  MkRBMap to depth pf (tmap f contents)

total cmap : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
             RBCrumb c h d k v -> RBCrumb c h d k v'
cmap f Root = Root
cmap f (RedL m w r p) = RedL m (f m w) (tmap f r) (cmap f p)
cmap f (RedR l m w p) = RedR (tmap f l) m (f m w) (cmap f p)
cmap f (BlkL m w r p) = BlkL m (f m w) (tmap f r) (cmap f p)
cmap f (BlkR l m w p) = BlkR (tmap f l) m (f m w) (cmap f p)

total zmap : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
             RBZip cc pc ch ph pd k v -> RBZip cc pc ch ph pd k v'
zmap f (t, c) = (tmap f t, cmap f c)
{-END_MAP-}

{-BEG_ZD-}
record ZipDown (cc : Bool) (pc : Bool) (h : Nat) (d : Nat)
               k (v : k -> Type) where
  constructor MkZipDown
  zipD : RBZip cc pc h h d k v
  canD : (Either (IsTrue cc) (IsPos h), Either (IsFalse cc) (IsFalse pc))

{-BEG_CLEAN-}
total cleanZipDown : ZipDownS cc pc h d k o cb pl pr v ->
                     ZipDown cc pc h d k v
cleanZipDown (MkZipDownS z c) = MkZipDown (cleanZip z) c
{-END_CLEAN-}

{-BEG_MAP-}
total zdmap : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
              ZipDown cc pc h d k v -> ZipDown cc pc h d k v'
zdmap f (MkZipDown z c) = MkZipDown (zmap f z) c
{-END_MAP-}

total zipLc : ZipDown cc pc h d k v -> Bool
total zipRc : ZipDown cc pc h d k v -> Bool

total treeLc : RBTree c h k v -> Either (IsTrue c) (IsPos h) -> Bool
total treeRc : RBTree c h k v -> Either (IsTrue c) (IsPos h) -> Bool

treeLc Lif = either void void
treeLc (Red l m w r) = const False
treeLc (Blk {lc} l m w r) = const lc
treeRc Lif = either void void
treeRc (Red l m w r) = const False
treeRc (Blk {rc} l m w r) = const rc

zipLc x = treeLc (fst (zipD x)) (fst (canD x))
zipRc x = treeRc (fst (zipD x)) (fst (canD x))
total goLeft : (z : ZipDown tc pc h d k v) ->
               RBZip (zipLc z) tc (predH tc h (fst (canD z)))
                                  (predH tc h (fst (canD z)))
                                  (succHD tc d) k v
total goRight : (z : ZipDown tc pc h d k v) ->
                RBZip (zipRc z) tc (predH tc h (fst (canD z)))
                                   (predH tc h (fst (canD z)))
                                   (succHD tc d) k v

{-BEG_CLEAN-}
total cleanLeft : (to : TotalOrd k o) ->
                  (z : ZipDownS tc pc h d k o tb pl pr v) ->
                  goLeft (cleanZipDown z) = cleanZip (goLeftS to z)
total cleanRight : (to : TotalOrd k o) ->
                   (z : ZipDownS tc pc h d k o tb pl pr v) ->
                   goRight (cleanZipDown z) = cleanZip (goRightS to z)
{-END_CLEAN-}

{-BEG_MAP-}
total mapLeft : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                (z : ZipDown tc pc h d k v) ->
                goLeft (zdmap f z) = zmap f (goLeft z)
total mapRight : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                 (z : ZipDown tc pc h d k v) ->
                 goRight (zdmap f z) = zmap f (goRight z)
{-END_MAP-}

{-BEG_DIMP-}
goLeft {pc} z with (fst (zipD z))
  goLeft z | Lif = either void void (fst (canD z))
  goLeft {pc=True} z | (Red l m w r) = either void void (snd (canD z))
  goLeft {pc=False} z | (Red l m w r) = (l, RedL m w r (snd (zipD z)))
  goLeft z | (Blk l m w r) = (l, BlkL m w r (snd (zipD z)))

goRight {pc} z with (fst (zipD z))
  goRight z | Lif = either void void (fst (canD z))
  goRight {pc=True} z | (Red l m w r) = either void void (snd (canD z))
  goRight {pc=False} z | (Red l m w r) = (r, RedR l m w (snd (zipD z)))
  goRight z | (Blk l m w r) = (r, BlkR l m w (snd (zipD z)))

{-BEG_CLEAN-}
cleanLeft to (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
cleanLeft {pc=True} to (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) =
  either void void (snd j)
cleanLeft {pc=False} to (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) = Refl
cleanLeft to (MkZipDownS (MkRBZipS (BlkS l m w r g) p q) j) = Refl

cleanRight to (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
cleanRight {pc=True} to (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) =
  either void void (snd j)
cleanRight {pc=False} to (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) = Refl
cleanRight to (MkZipDownS (MkRBZipS (BlkS l m w r g) p q) j) = Refl
{-END_CLEAN-}

{-BEG_MAP-}
mapLeft f (MkZipDown (Lif, p) q) = either void void (fst q)
mapLeft {pc=True} f (MkZipDown (Red l m w r, p) q) = either void void (snd q)
mapLeft {pc=False} f (MkZipDown (Red l m w r, p) q) = Refl
mapLeft f (MkZipDown (Blk l m w r, p) q) = Refl

mapRight f (MkZipDown (Lif, p) q) = either void void (fst q)
mapRight {pc=True} f (MkZipDown (Red l m w r, p) q) = either void void (snd q)
mapRight {pc=False} f (MkZipDown (Red l m w r, p) q) = Refl
mapRight f (MkZipDown (Blk l m w r, p) q) = Refl
{-END_MAP-}
{-END_DIMP-}
{-END_ZD-}

{-BEG_ZU-}
record ZipUp (cc : Bool) (pc : Bool) (h : Nat) (d : Nat)
             k (v : k -> Type) where
  constructor MkZipUp
  zipU : RBZip cc pc h h (S d) k v
  canU : Either (IsFalse cc) (IsFalse pc)

{-BEG_CLEAN-}
total cleanZipUp : ZipUpS cc pc h d k o cb pl pr v ->
                   ZipUp cc pc h d k v
cleanZipUp (MkZipUpS z c) = MkZipUp (cleanZip z) c
{-END_CLEAN-}

{-BEG_MAP-}
total zumap : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
              ZipUp cc pc h d k v -> ZipUp cc pc h d k v'
zumap f (MkZipUp z c) = MkZipUp (zmap f z) c
{-END_MAP-}

total zipPc : ZipUp cc tc h d k v -> Bool
zipPc = cfPc . snd . zipU

total goUp : (z : ZipUp cc tc h d k v) ->
              RBZip tc (zipPc z) (succHD tc h)
                                 (succHD tc h) (succHD (not tc) d) k v

{-BEG_CLEAN-}
total cleanUp : (to : TotalOrd k o) -> (z : ZipUpS cc tc h d k o cb pl pr v) ->
                goUp (cleanZipUp z) = cleanZip (goUpS to z)
{-END_CLEAN-}

{-BEG_MAP-}
total mapUp : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
              (z : ZipUp cc tc h d k v) ->
              goUp (zumap f z) = zmap f (goUp z)
{-END_MAP-}

{-BEG_DIMP-}
goUp {cc=True} (MkZipUp (c, RedL m w r p) q) = either void void q
goUp {cc=True} (MkZipUp (c, RedR l m w p) q) = either void void q
goUp {cc=False} (MkZipUp (c, RedL m w r p) q) = (Red c m w r, p)
goUp (MkZipUp (c, BlkL m w r p) q) = (Blk c m w r, p)
goUp {cc=False} (MkZipUp (c, RedR l m w p) q) = (Red l m w c, p)
goUp (MkZipUp (c, BlkR l m w p) q) = (Blk l m w c, p)

{-BEG_CLEAN-}
cleanUp {cc=True} to (MkZipUpS (MkRBZipS t (RedLS m w r p f) q) j) =
  either void void j
cleanUp {cc=True} to (MkZipUpS (MkRBZipS t (RedRS l m w p f) q) j) =
  either void void j
cleanUp {cc=False} to (MkZipUpS (MkRBZipS t (RedLS m w r p f) q) j) = Refl
cleanUp to (MkZipUpS (MkRBZipS t (BlkLS m w r p f) q) j) = Refl
cleanUp {cc=False} to (MkZipUpS (MkRBZipS t (RedRS l m w p f) q) j) = Refl
cleanUp to (MkZipUpS (MkRBZipS t (BlkRS l m w p f) q) j) = Refl
{-END_CLEAN-}

{-BEG_MAP-}
mapUp {cc=True} f (MkZipUp (t, RedL m w r p) q) = either void void q
mapUp {cc=True} f (MkZipUp (t, RedR l m w p) q) = either void void q
mapUp {cc=False} f (MkZipUp (t, RedL m w r p) q) = Refl
mapUp f (MkZipUp (t, BlkL m w r p) q) = Refl
mapUp {cc=False} f (MkZipUp (t, RedR l m w p) q) = Refl
mapUp f (MkZipUp (t, BlkR l m w p) q) = Refl
{-END_MAP-}
{-END_DIMP-}
{-END_ZU-}

{-
insertS a w m = ?insertS_rhs
insert a w m = ?insert_rhs
cleanInsert a m = ?cleanInsert_rhs
removeS a m = ?removeS_rhs
remove a m = ?remove_rhs
cleanRemove a m = ?cleanRemove_rhs
-}

-- Proofs

{-BEG_THM-}
{-BEG_PF-}
{-BEG_CLEAN-}
cleanEmpty o to = Refl

{-BEG_LOOK-}
mutual
  total cleanLookTree : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                        (t : RBTreeS c h k o b v) ->
                        lookTree o to a (cleanTree t) = lookTreeS o to a t
  total cleanPickTree : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                        (l : RBTreeS lc lh k o lb v) -> (m : k) -> (w : v m) ->
                        (r : RBTreeS rc rh k o rb v) ->
                        pickTree o to a (cleanTree l) m w (cleanTree r) =
                        pickTreeS o to a l m w r

  cleanPickTree o to a l m w r with (enh o a m)
    cleanPickTree o to a l m w r | LTE x = cleanLookTree o to a l
    cleanPickTree o to a l m w r | EQE x = Refl
    cleanPickTree o to a l m w r | GTE x = cleanLookTree o to a r
  
  cleanLookTree o to a LifS = Refl
  cleanLookTree o to a (RedS l m w r p) = cleanPickTree o to a l m w r
  cleanLookTree o to a (BlkS l m w r p) = cleanPickTree o to a l m w r

cleanLookup a (MkRBMapS o d b to t) = cleanLookTree o to a t
{-END_LOOK-}

{-
cleanInsert a w m = ?ci

cleanRemove a m = ?cr
-}

{-BEG_MAP-}
total cleanTmap : {v' : k -> Type} ->
                  (f : (a : k) -> v a -> v' a) -> (t : RBTreeS c h k o b v) ->
                  tmap f (cleanTree t) = cleanTree (tmapS f t)
cleanTmap f LifS = Refl
cleanTmap f (RedS l m w r p) = rwRed (cleanTmap f l) (cleanTmap f r)
cleanTmap f (BlkS l m w r p) = rwBlk (cleanTmap f l) (cleanTmap f r)

cleanMapmap f (MkRBMapS t d b p c) = cong (cleanTmap f c)
{-END_MAP-}
{-END_CLEAN-}

{-BEG_LOOK-}
lookupEmpty a o t = Refl

{-BEG_MAP-}
mutual
  total lookTmap : {v' : k -> Type} -> (o : Comp k) ->
                   (to : TotalOrd k o) -> (a : k) ->
                   (f : (b : k) -> v b -> v' b) ->
                   (t : RBTree c h k v) ->
                   lookTree o to a (tmap f t) =
                   map (f a) (lookTree o to a t)
  total pickTmap : {v' : k -> Type} -> (o : Comp k) ->
                   (to : TotalOrd k o) -> (a : k) ->
                   (f : (b : k) -> v b -> v' b) ->
                   (l : RBTree lc lh k v) ->
                   (m : k) -> (w : v m) ->
                   (r : RBTree rc rh k v) ->
                   pickTree o to a (tmap f l) m (f m w) (tmap f r) =
                   map (f a) (pickTree o to a l m w r)

  pickTmap o to a f l m w r with (enh o a m)
    | LTE x = lookTmap o to a f l
    | EQE x with (corf to x)
      pickTmap o to a f l a w r | EQE x | Refl = Refl
    | GTE x = lookTmap o to a f r

  lookTmap o to a f Lif = Refl
  lookTmap o to a f (Red l m w r) = pickTmap o to a f l m w r
  lookTmap o to a f (Blk l m w r) = pickTmap o to a f l m w r

lookupMap a f (MkRBMap o d to t) = lookTmap o to a f t
{-END_LOOK-}

total tmapId : (t : RBTree c h k v) -> tmap (\b => id {a=v b}) t = t
tmapId Lif = Refl
tmapId (Red l m w r) = rwRed (tmapId l) (tmapId r)
tmapId (Blk l m w r) = rwBlk (tmapId l) (tmapId r)

mapmapId (MkRBMap o d to t) = cong (tmapId t)

total tmapComp : {v' : k -> Type} -> {w : k -> Type} ->
                 (t : RBTree c h k v) ->
                 (f : (a : k) -> v a -> v' a) ->
                 (g : (a : k) -> v' a -> w a) ->
                 tmap g (tmap f t) = tmap (\a => g a . f a) t
tmapComp Lif f g = Refl
tmapComp (Red l m w r) f g = rwRed (tmapComp l f g) (tmapComp r f g)
tmapComp (Blk l m w r) f g = rwBlk (tmapComp l f g) (tmapComp r f g)

mapmapComp (MkRBMap o d to t) f g = cong (tmapComp t f g)

{-
insertMap a w m f = ?insMap
removeMap a m f = ?remMap
-}

emptyMap o p f = Refl
{-END_MAP-}

{-
removeEmpty a o t = ?remEmp
-}
{-END_PF-}
{-END_THM-}

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
