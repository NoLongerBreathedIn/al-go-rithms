module RBTreeS.StructsS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains the structure definitions.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import BST.StructsB
import public BST.TypesB
import RBTreeS.SizeUp
import RBTreeS.Types

public export
data RBTreeS : Bool -> Nat -> (k : Type) ->
               Comp k -> Bnds k -> (k -> Type) -> Type where
  LifS : RBTreeS False Z k o Nothing v
  RedS : RBTreeS False n k o lb v -> (m : k) -> v m ->
         RBTreeS False n k o rb v -> IsGood o lb m rb ->
         RBTreeS True n k o (boundStuff lb m rb) v
  BlkS : RBTreeS lc n k o lb v -> (m : k) -> v m ->
         RBTreeS rc n k o rb v -> IsGood o lb m rb ->
         RBTreeS False (S n) k o (boundStuff lb m rb) v

public export
total sreeLc : RBTreeS c h k o b v -> Bool
public export
total treeLb : RBTreeS c h k o b v -> Bnds k
public export
total sreeRc : RBTreeS c h k o b v -> Bool
public export
total treeRb : RBTreeS c h k o b v -> Bnds k

sreeLc LifS = False
sreeLc (RedS x m y z w) = False
sreeLc (BlkS {lc} x m y z w) = lc
treeLb LifS = Nothing
treeLb (RedS {lb} x m y z w) = lb
treeLb (BlkS {lb} x m y z w) = lb
sreeRc LifS = False
sreeRc (RedS x m y z w) = False
sreeRc (BlkS {rc} x m y z w) = rc
treeRb LifS = Nothing
treeRb (RedS {rb} x m y z w) = rb
treeRb (BlkS {rb} x m y z w) = rb

public export
total sreeK : RBTreeS c h k o b v -> Maybe k
sreeK LifS = Nothing
sreeK (RedS l m w r p) = Just m
sreeK (BlkS l m w r p) = Just m

public export
total sreeKD : (t : RBTreeS c h k o b v) -> IsFull (sreeK t) ->
               Either (IsTrue c) (IsPos h)
sreeKD LifS = Left
sreeKD (RedS l m w r p) = Left
sreeKD (BlkS l m w r p) = Right

public export
total sreeLDH : (t : RBTreeS c h k o b v) -> (xx : IsFull (sreeK t)) ->
                sizeUp (sreeLc t) (predH c h) `LT` sizeUp c h
public export
total sreeRDH : (t : RBTreeS c h k o b v) -> (xx : IsFull (sreeK t)) ->
                sizeUp (sreeRc t) (predH c h) `LT` sizeUp c h

sreeLDH LifS xx = void xx
sreeLDH (RedS l m w r p) xx = sultCol _
sreeLDH (BlkS l m w r p) xx = sultNum Z _ False _
sreeRDH LifS xx = void xx
sreeRDH (RedS l m w r p) xx = sultCol _
sreeRDH (BlkS l m w r p) xx = sultNum Z _ False _

export
total rwRedS : {l : RBTreeS False h k o lb v} ->
               {l' : RBTreeS False h k o lb v} ->
               {r : RBTreeS False h k o rb v} ->
               {r' : RBTreeS False h k o rb v} ->
               {p : IsGood o lb m rb} -> {p' : IsGood o lb m rb} ->
               l = l' -> r = r' -> RedS l m w r p = RedS l' m w r' p'
rwRedS {o} {lb} {m} {rb} {p} {p'} j k with (ssIsGood o lb m rb p p')
  rwRedS Refl Refl | Refl = Refl

export
total rwBlkS : {l : RBTreeS lc h k o lb v} -> {l' : RBTreeS lc h k o lb v} ->
               {r : RBTreeS rc h k o rb v} -> {r' : RBTreeS rc h k o rb v} ->
               {p : IsGood o lb m rb} -> {p' : IsGood o lb m rb} ->
               l = l' -> r = r' -> BlkS l m w r p = BlkS l' m w r' p'
rwBlkS {o} {lb} {m} {rb} {p} {p'} j k with (ssIsGood o lb m rb p p')
  rwBlkS Refl Refl | Refl = Refl

public export
total trB : RBTreeS c n k o b v -> Bnds k
trB {b} t = b

public export
total stripT : RBTreeS c h k o b v -> BST k o b v
stripT LifS = Leaf
stripT (RedS l m w r p) = Node (stripT l) m w (stripT r) p
stripT (BlkS l m w r p) = Node (stripT l) m w (stripT r) p

public export
data RBCrumbS : Bool -> Nat -> Nat -> (k : Type) ->
                Comp k -> Maybe k -> Maybe k -> (k -> Type) -> Type where
  RootS : RBCrumbS True h Z k o Nothing Nothing v
  RedLS : (m : k) -> v m -> RBTreeS False h k o rb v ->
          RBCrumbS False h d k o pl pr v ->
          IsGoodCrumbL o m rb pl pr -> RBCrumbS True h d k o pl (Just m) v
  RedRS : RBTreeS False h k o lb v -> (m : k) -> v m ->
          RBCrumbS False h d k o pl pr v ->
          IsGoodCrumbR o m lb pl pr -> RBCrumbS True h d k o (Just m) pr v
  BlkLS : (m : k) -> v m -> RBTreeS rc h k o rb v ->
          RBCrumbS pc (S h) d k o pl pr v ->
          IsGoodCrumbL o m rb pl pr -> RBCrumbS False h (S d) k o pl (Just m) v
  BlkRS : RBTreeS lc h k o lb v -> (m : k) -> v m ->
          RBCrumbS pc (S h) d k o pl pr v ->
          IsGoodCrumbR o m lb pl pr -> RBCrumbS False h (S d) k o (Just m) pr v

export
total rwRedLS : {c : RBTreeS False h k o cb v} ->
                {c' : RBTreeS False h k o cb v} ->
                {p : RBCrumbS False h d k o pl pr v} ->
                {p' : RBCrumbS False h d k o pl pr v} ->
                {f : IsGoodCrumbL o m cb pl pr} ->
                {f' : IsGoodCrumbL o m cb pl pr} ->
                c = c' -> p = p' -> RedLS m w c p f = RedLS m w c' p' f'
rwRedLS {o} {m} {cb} {pl} {pr} {f} {f'} j k with (ssIsGoodCrumbL o m cb pl pr
                                                                 f f')
  rwRedLS Refl Refl | Refl = Refl
export
total rwRedRS : {c : RBTreeS False h k o cb v} ->
                {c' : RBTreeS False h k o cb v} ->
                {p : RBCrumbS False h d k o pl pr v} ->
                {p' : RBCrumbS False h d k o pl pr v} ->
                {f : IsGoodCrumbR o m cb pl pr} ->
                {f' : IsGoodCrumbR o m cb pl pr} ->
                c = c' -> p = p' -> RedRS c m w p f = RedRS c' m w p' f'
rwRedRS {o} {m} {cb} {pl} {pr} {f} {f'} j k with (ssIsGoodCrumbR o m cb pl pr
                                                                 f f')
  rwRedRS Refl Refl | Refl = Refl
export
total rwBlkLS : {c : RBTreeS cc h k o cb v} ->
                {c' : RBTreeS cc h k o cb v} ->
                {p : RBCrumbS pc (S h) d k o pl pr v} ->
                {p' : RBCrumbS pc (S h) d k o pl pr v} ->
                {f : IsGoodCrumbL o m cb pl pr} ->
                {f' : IsGoodCrumbL o m cb pl pr} ->
                c = c' -> p = p' -> BlkLS m w c p f = BlkLS m w c' p' f'
rwBlkLS {o} {m} {cb} {pl} {pr} {f} {f'} j k with (ssIsGoodCrumbL o m cb pl pr
                                                                 f f')
  rwBlkLS Refl Refl | Refl = Refl
export
total rwBlkRS : {c : RBTreeS cc h k o cb v} ->
                {c' : RBTreeS cc h k o cb v} ->
                {p : RBCrumbS pc (S h) d k o pl pr v} ->
                {p' : RBCrumbS pc (S h) d k o pl pr v} ->
                {f : IsGoodCrumbR o m cb pl pr} ->
                {f' : IsGoodCrumbR o m cb pl pr} ->
                c = c' -> p = p' -> BlkRS c m w p f = BlkRS c' m w p' f'
rwBlkRS {o} {m} {cb} {pl} {pr} {f} {f'} j k with (ssIsGoodCrumbR o m cb pl pr
                                                                 f f')
  rwBlkRS Refl Refl | Refl = Refl

public export
total stripC : RBCrumbS c h d k o pl pr v -> BSC k o pl pr v
stripC RootS = Rut
stripC (RedLS m w r p q) = Lft m w (stripT r) (stripC p) q
stripC (RedRS l m w p q) = Rgt (stripT l) m w (stripC p) q
stripC (BlkLS m w r p q) = Lft m w (stripT r) (stripC p) q
stripC (BlkRS l m w p q) = Rgt (stripT l) m w (stripC p) q

public export
total crL : RBCrumbS c h d k o pl pr v -> Maybe k
crL {pl} c = pl
public export
total crR : RBCrumbS c h d k o pl pr v -> Maybe k
crR {pr} c = pr
public export
total crC : RBCrumbS c h d k o pl pr v -> Bool
crC {c} cr = c
public export
total crPl : RBCrumbS c h (S d) k o pl pr v -> Maybe k
public export
total crPr : RBCrumbS c h (S d) k o pl pr v -> Maybe k
public export
total srPc : RBCrumbS c h (S d) k o pl pr v -> Bool
public export
total srK : RBCrumbS c h d k o pl pr v -> Maybe k

crPl (RedLS _ _ _ p _) = crL p
crPl (RedRS _ _ _ p _) = crL p
crPl (BlkLS _ _ _ p _) = crL p
crPl (BlkRS _ _ _ p _) = crL p
crPr (RedLS _ _ _ p _) = crR p
crPr (RedRS _ _ _ p _) = crR p
crPr (BlkLS _ _ _ p _) = crR p
crPr (BlkRS _ _ _ p _) = crR p
srPc (RedLS _ _ _ p _) = crC p
srPc (RedRS _ _ _ p _) = crC p
srPc (BlkLS _ _ _ p _) = crC p
srPc (BlkRS _ _ _ p _) = crC p
srK (RedLS m _ _ _ _) = Just m
srK (BlkLS m _ _ _ _) = Just m
srK (RedRS _ m _ _ _) = Just m
srK (BlkRS _ m _ _ _) = Just m
srK RootS = Nothing

public export
total srKU : (cr : RBCrumbS c h d k o pl pr v) -> IsFull (srK cr) ->
             IsPos d
srKU RootS = id
srKU (RedLS _ _ _ (BlkLS _ _ _ _ _) _) = id
srKU (RedLS _ _ _ (BlkRS _ _ _ _ _) _) = id
srKU (RedRS _ _ _ (BlkLS _ _ _ _ _) _) = id
srKU (RedRS _ _ _ (BlkRS _ _ _ _ _) _) = id
srKU (BlkLS _ _ _ _ _) = id
srKU (BlkRS _ _ _ _ _) = id

public export
record RBZipS (cc : Bool) (pc : Bool) (ch : Nat) (ph : Nat) (pd : Nat)
              k (o : Comp k) (cb : Bnds k) (pl : Maybe k) (pr : Maybe k)
              (v : k -> Type) where
  constructor MkRBZipS
  child : RBTreeS cc ch k o cb v
  parnt : RBCrumbS pc ph pd k o pl pr v
  cmpat : IsGoodZip o pl pr cb

public export
total rwRBZipS : {c : RBTreeS cc ch k o cb v} ->
                 {c' : RBTreeS cc ch k o cb v} ->
                 {p : RBCrumbS pc ph pd k o pl pr v} ->
                 {p' : RBCrumbS pc ph pd k o pl pr v} ->
                 {q : IsGoodZip o pl pr cb} ->
                 {q' : IsGoodZip o pl pr cb} ->
                 c = c' -> p = p' -> MkRBZipS c p q = MkRBZipS c' p' q'
rwRBZipS {o} {pl} {pr} {cb} {q} {q'} j k with (ssIsGoodZip o pl pr cb q q')
  rwRBZipS Refl Refl | Refl = Refl

public export
total zipUpS : RBTreeS c h k o b v ->
               RBZipS c True h h Z k o b Nothing Nothing v

zipUpS {b=Nothing} t = MkRBZipS t RootS ()
zipUpS {b=Just (l,r)} t = MkRBZipS t RootS ((), ())

public export
total stripZ : RBZipS cc pc ch ph pd k o cb pl pr v ->
               BSZ k o cb pl pr v
stripZ (MkRBZipS t c p) = MkBSZ (stripT t) (stripC c) p

public export
total sipLc : RBZipS cc pc ch ph pd k o cb pl pr v -> Bool
public export
total zipLb : RBZipS cc pc ch ph pd k o cb pl pr v -> Bnds k
public export
total sipRc : RBZipS cc pc ch ph pd k o cb pl pr v -> Bool
public export
total zipRb : RBZipS cc pc ch ph pd k o cb pl pr v -> Bnds k

sipLc = sreeLc . child
zipLb = treeLb . child
sipRc = sreeRc . child
zipRb = treeRb . child

public export
total sipK : RBZipS cc pc ch ph pd k o cb pl pr v -> Maybe k
sipK = sreeK . child

public export
total sipKD : (z : RBZipS cc pc ch ph pd k o cb pl pr v) -> IsFull (sipK z) ->
              Either (IsTrue cc) (IsPos ch)
sipKD (MkRBZipS t _ _) = sreeKD t

public export
total sipLDH : (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
               (xx : IsFull (sipK z)) ->
               sizeUp (sipLc z) (predH cc ch) `LT` sizeUp cc ch
sipLDH (MkRBZipS t _ _) = sreeLDH t

public export
total sipRDH : (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
               (xx : IsFull (sipK z)) ->
               sizeUp (sipRc z) (predH cc ch) `LT` sizeUp cc ch
sipRDH (MkRBZipS t _ _) = sreeRDH t

public export
total sipJ : RBZipS cc pc ch ph pd k o cb pl pr v -> Maybe k
sipJ = srK . parnt

public export
total sipJU : (z : RBZipS cc pc ch ph pd k o cb pl pr v) -> IsFull (sipJ z) ->
              IsPos pd
sipJU (MkRBZipS _ p _) = srKU p

public export
total sipPc : RBZipS cc pc ch ph (S pd) k o cb pl pr v -> Bool
sipPc = srPc . parnt

public export
total zipPl : RBZipS cc pc ch ph (S pd) k o cb pl pr v -> Maybe k
zipPl = crPl . parnt

public export
total zipPr : RBZipS cc pc ch ph (S pd) k o cb pl pr v -> Maybe k
zipPr = crPr . parnt

public export
total zipPb : RBZipS cc pc ch ph (S pd) k o cb pl pr v -> Bnds k
zipPb {cb} z with (parnt z)
  | RedLS {rb} m _ _ _ _ = boundStuff cb m rb
  | BlkLS {rb} m _ _ _ _ = boundStuff cb m rb
  | RedRS {lb} _ m _ _ _ = boundStuff lb m cb
  | BlkRS {lb} _ m _ _ _ = boundStuff lb m cb

export
total pfOrdered : TotalOrd k o -> RBTreeS c h k o b v -> OrderedBounds o b

pfOrdered _ LifS = ()
pfOrdered to (RedS lc _ _ rc pf) =
  pfOrdered' to (pfOrdered to lc) (pfOrdered to rc) pf
pfOrdered to (BlkS lc _ _ rc pf) =
  pfOrdered' to (pfOrdered to lc) (pfOrdered to rc) pf

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
