module RBTreeS.StructsS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains the structure definitions.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import BST.StructsB

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
total sreeK : RBTreeS c h k o b v -> Maybe k
sreeK LifS = Nothing
sreeK (RedS l m w r p) = Just m
sreeK (BlkS l m w r p) = Just m

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
rwBlkS {o} {lb} {m} {rb} {p} {p'} j k = ?zzz
 {-with (ssIsGood o lb m rb p p')
  rwBlkS Refl Refl | Refl = Refl-}

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
total IsTrue : Bool -> Type
IsTrue True = ()
IsTrue False = Void

public export
total IsFalse : Bool -> Type
IsFalse True = Void
IsFalse False = ()

public export
total IsPos : Nat -> Type
IsPos Z = Void
IsPos (S _) = ()

public export
total IsZero : Nat -> Type
IsZero Z = ()
IsZero (S _) = ()

public export
total predH : (b : Bool) -> (n : Nat) -> Either (IsTrue b) (IsPos n) -> Nat
predH True n x = n
predH False (S k) x = k
predH False Z pf = either void void pf

public export
total succHD : Bool -> Nat -> Nat
succHD True = id
succHD False = S

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
total crPc : RBCrumbS c h (S d) k o pl pr v -> Bool

crPl (RedLS _ _ _ p _) = crL p
crPl (RedRS _ _ _ p _) = crL p
crPl (BlkLS _ _ _ p _) = crL p
crPl (BlkRS _ _ _ p _) = crL p
crPr (RedLS _ _ _ p _) = crR p
crPr (RedRS _ _ _ p _) = crR p
crPr (BlkLS _ _ _ p _) = crR p
crPr (BlkRS _ _ _ p _) = crR p
crPc (RedLS _ _ _ p _) = crC p
crPc (RedRS _ _ _ p _) = crC p
crPc (BlkLS _ _ _ p _) = crC p
crPc (BlkRS _ _ _ p _) = crC p

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
