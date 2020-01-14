module RBTreeS.DownS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains functions related to moving down.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import BST.MoveB
import public RBTreeS.StructsS
import RBTreeS.Types
import RBTreeS.FmapS
import RBTreeS.LookS
import RBTreeS.SizeUp

public export
record ZipDownS (cc : Bool) (pc : Bool) (h : Nat) (d : Nat)
                k (o : Comp k) (cb : Bnds k) (pl : Maybe k) (pr : Maybe k)
                (v : k -> Type) where
  constructor MkZipDownS
  zipDS : RBZipS cc pc h h d k o cb pl pr v
  canDS : (Either (IsTrue cc) (IsPos h), Either (IsFalse cc) (IsFalse pc))

public export
total zdmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipDownS cc pc h d k o cb pl pr v ->
               ZipDownS cc pc h d k o cb pl pr v'
zdmapS f (MkZipDownS z c) = MkZipDownS (zmapS f z) c

public export
total goLeftS : TotalOrd k o -> (z : ZipDownS tc pc h d k o tb pl pr v) ->
                RBZipS (sipLc (zipDS z)) tc (predH tc h) (predH tc h)
                                            (succHD tc d)
                                    k o (zipLb (zipDS z)) pl (sipK (zipDS z)) v
public export
total goRightS : TotalOrd k o -> (z : ZipDownS tc pc h d k o tb pl pr v) ->
                 RBZipS (sipRc (zipDS z)) tc (predH tc h) (predH tc h)
                                             (succHD tc d)
                                    k o (zipRb (zipDS z)) (sipK (zipDS z)) pr v

-- Theorems

export
total mapLeftS : {v' : k -> Type} -> (to : TotalOrd k o) ->
                 (f : (a : k) -> v a -> v' a) ->
                 (z : ZipDownS tc pc h d k o tb pl pr v) ->
                 goLeftS to (zdmapS f z) = zmapS f (goLeftS to z)
export
total mapRightS : {v' : k -> Type} -> (to : TotalOrd k o) ->
                  (f : (a : k) -> v a -> v' a) ->
                  (z : ZipDownS tc pc h d k o tb pl pr v) ->
                  goRightS to (zdmapS f z) = zmapS f (goRightS to z)

export
total lookLeft : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                 (z : ZipDownS cc pc h d k o cb pl pr v) ->
                 lookZip o to a (goLeftS to z) = lookZip o to a (zipDS z)
export
total lookRight : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (z : ZipDownS cc pc h d k o cb pl pr v) ->
                  lookZip o to a (goRightS to z) = lookZip o to a (zipDS z)

-- Implementation

export
total glPfC : TotalOrd k o -> (pl : Maybe k) -> (lb : Bnds k) ->
              (m : k) -> (rb : Bnds k) -> (pr : Maybe k) ->
              IsGoodZip o pl pr (boundStuff lb m rb) ->
              IsGood o lb m rb -> OrderedBounds o lb -> OrderedBounds o rb ->
              IsGoodCrumbL o m rb pl pr
export
total glPfZ : TotalOrd k o -> (pl : Maybe k) -> (lb : Bnds k) ->
              (m : k) -> (rb : Bnds k) -> (pr : Maybe k) ->
              IsGoodZip o pl pr (boundStuff lb m rb) ->
              IsGood o lb m rb -> IsGoodZip o pl (Just m) lb
export
total grPfC : TotalOrd k o -> (pl : Maybe k) -> (lb : Bnds k) ->
              (m : k) -> (rb : Bnds k) -> (pr : Maybe k) ->
              IsGoodZip o pl pr (boundStuff lb m rb) ->
              IsGood o lb m rb -> OrderedBounds o lb -> OrderedBounds o rb ->
              IsGoodCrumbR o m lb pl pr
export
total grPfZ : TotalOrd k o -> (pl : Maybe k) -> (lb : Bnds k) ->
              (m : k) -> (rb : Bnds k) -> (pr : Maybe k) ->
              IsGoodZip o pl pr (boundStuff lb m rb) ->
              IsGood o lb m rb -> IsGoodZip o (Just m) pr rb

goLeftS {pc} to z with (child (zipDS z))
  | LifS = either void void (fst (canDS z))
  goLeftS {pc=True} to z | (RedS l m w r p) = either void void (snd (canDS z))
  goLeftS {pc=False} {pl} {pr} to z | (RedS {lb} {rb} l m w r p) =
    MkRBZipS l (RedLS m w r (parnt (zipDS z))
                 (glPfC to pl lb m rb pr
                   (cmpat (zipDS z)) p (pfOrdered to l) (pfOrdered to r)))
      (glPfZ to pl lb m rb pr (cmpat (zipDS z)) p)
  goLeftS {pl} {pr} to z | (BlkS {lb} {rb} l m w r p) =
    MkRBZipS l (BlkLS m w r (parnt (zipDS z))
                 (glPfC to pl lb m rb pr
                   (cmpat (zipDS z)) p (pfOrdered to l) (pfOrdered to r)))
      (glPfZ to pl lb m rb pr (cmpat (zipDS z)) p)
goRightS {pc} to z with (child (zipDS z))
  | LifS = either void void (fst (canDS z))
  goRightS {pc=True} to z | (RedS l m w r p) = either void void (snd (canDS z))
  goRightS {pc=False} {pl} {pr} to z | (RedS {lb} {rb} l m w r p) =
    MkRBZipS r (RedRS l m w (parnt (zipDS z))
                 (grPfC to pl lb m rb pr
                   (cmpat (zipDS z)) p (pfOrdered to l) (pfOrdered to r)))
      (grPfZ to pl lb m rb pr (cmpat (zipDS z)) p)
  goRightS {pl} {pr} to z | (BlkS {lb} {rb} l m w r p) =
    MkRBZipS r (BlkRS l m w (parnt (zipDS z))
                 (grPfC to pl lb m rb pr
                   (cmpat (zipDS z)) p (pfOrdered to l) (pfOrdered to r)))
      (grPfZ to pl lb m rb pr (cmpat (zipDS z)) p)

-- Proofs needed in implementation

total glPfCL : TotalOrd k o -> (pl : Maybe k) -> (lb : Bnds k) ->
               (m : k) -> (rb : Bnds k) -> (pr : Maybe k) ->
               IsGoodZip o pl pr (boundStuff lb m rb) ->
               IsGood o lb m rb -> OrderedBounds o lb ->
               maybe () (EnsureR o m rb) pl
total glPfCR : TotalOrd k o -> (pl : Maybe k) -> (lb : Bnds k) ->
               (m : k) -> (rb : Bnds k) -> (pr : Maybe k) ->
               IsGoodZip o pl pr (boundStuff lb m rb) ->
               IsGood o lb m rb -> OrderedBounds o rb ->
               maybe () (EnsureL o m rb) pr
total grPfCL : TotalOrd k o -> (pl : Maybe k) -> (lb : Bnds k) ->
               (m : k) -> (rb : Bnds k) -> (pr : Maybe k) ->
               IsGoodZip o pl pr (boundStuff lb m rb) ->
               IsGood o lb m rb -> OrderedBounds o lb ->
               maybe () (EnsureR o m lb) pl
total grPfCR : TotalOrd k o -> (pl : Maybe k) -> (lb : Bnds k) ->
               (m : k) -> (rb : Bnds k) -> (pr : Maybe k) ->
               IsGoodZip o pl pr (boundStuff lb m rb) ->
               IsGood o lb m rb -> OrderedBounds o rb ->
               maybe () (EnsureL o m lb) pr
total glPfCL0 : TotalOrd k o -> (pl : k) -> (lb : Bnds k) -> (m : k) ->
                IsGT (o (boundStuffL m lb) pl) ->
                IsGoodL o m lb -> OrderedBounds o lb ->
                IsLT (o pl m)
total grPfCR0 : TotalOrd k o -> (m : k) -> (rb : Bnds k) -> (pr : k) ->
                IsLT (o (boundStuffR m rb) pr) ->
                IsGoodR o m rb -> OrderedBounds o rb ->
                IsLT (o m pr)
total glPfCL1 : TotalOrd k o -> (l : k) -> (m : k) -> (rb : Bnds k) ->
                IsLT (o l m) -> IsGoodR o m rb -> IsGoodR o l rb
total grPfCR1 : TotalOrd k o -> (lb : Bnds k) -> (m : k) -> (r : k) ->
                IsLT (o m r) -> IsGoodL o m lb -> IsGoodL o r lb

glPfCL0 to l Nothing m z g lo = flipGT to z
glPfCL0 to l (Just (ll, lr)) m z g lo =
  tran to (flipGT to z) (tranQL to lo (flipGT to g))
grPfCR0 to m Nothing r z g ro = z
grPfCR0 to m (Just (rl, rr)) r z g ro =
  tran to g (tranQL to ro z)

glPfCL1 to l m Nothing = const (const ())
glPfCL1 to l m (Just (rl, rr)) = tran to
grPfCR1 to Nothing m r = const (const ())
grPfCR1 to (Just (ll, lr)) m r = tranGG to . flipLT to

glPfCL to Nothing lb m rb pr z g lo = ()
glPfCL to (Just l) lb m rb pr z g lo with (glPfCL0 to l lb m
                                                   (fst z) (fst g) lo)
  | lm = (lm, glPfCL1 to l m rb lm (snd g))
glPfCR to pl lb m rb Nothing z g ro = ()
glPfCR to pl lb m Nothing (Just r) z g ro = (snd z, ())
glPfCR to pl lb m (Just (rl, rr)) (Just r) z g ro =
  (tran to (snd g) (tranQL to ro (snd z)), flipLT to (snd z))
grPfCL to Nothing lb m rb pr z g lo = ()
grPfCL to (Just l) Nothing m rb pr z g lo = (flipGT to (fst z), ())
grPfCL to (Just l) (Just (ll, lr)) m rb pr z g lo =
  (tran to (flipGT to (fst z)) (tranQL to lo (flipGT to (fst g))),
   flipGT to (fst z))
grPfCR to pl lb m rb Nothing z g ro = ()
grPfCR to pl lb m rb (Just r) z g ro with (grPfCR0 to m rb r
                                                   (snd z) (snd g) ro)
  | mr = (mr, grPfCR1 to lb m r mr (fst g))

glPfC to pl lb m rb pr pz pg lo ro =
  (snd pg,
   glPfCL to pl lb m rb pr pz pg lo,
   glPfCR to pl lb m rb pr pz pg ro)
grPfC to pl lb m rb pr pz pg lo ro =
  (fst pg,
   grPfCL to pl lb m rb pr pz pg lo,
   grPfCR to pl lb m rb pr pz pg ro)

glPfZ to pl Nothing m rb pr pz pg = ()
glPfZ to pl (Just (ll, lr)) m rb pr pz pg = (fst pz, flipGT to (fst pg))
grPfZ to pl lb m Nothing pr pz pg = ()
grPfZ to pl lb m (Just (rl, rr)) pr pz pg = (flipLT to (snd pg), snd pz)

-- Proofs

mapLeftS to f (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
mapLeftS {pc=True} to f (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) =
  either void void (snd j)
mapLeftS {pc=False} to f (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) =
  rwRBZipS Refl (rwRedLS Refl Refl)
mapLeftS to f (MkZipDownS (MkRBZipS (BlkS l m w r g) p q) j) =
  rwRBZipS Refl (rwBlkLS Refl Refl)
mapRightS to f (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
mapRightS {pc=True} to f (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) =
  either void void (snd j)
mapRightS {pc=False} to f (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) =
  rwRBZipS Refl (rwRedRS Refl Refl)
mapRightS to f (MkZipDownS (MkRBZipS (BlkS l m w r g) p q) j) =
  rwRBZipS Refl (rwBlkRS Refl Refl)

lookLeft o to a (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
lookLeft {pc=True} o to a
  (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) = either void void (snd j)
lookLeft {pc=False} {pl} {pr} o to a
  (MkZipDownS (MkRBZipS (RedS {lb} {rb} l m w r g) p q) j) = sym (strippyZ to a
    (MkRBZipS (RedS l m w r g) p q)
    (MkRBZipS l
      (RedLS m w r p (glPfC to pl lb m rb pr q g
                            (pfOrdered to l) (pfOrdered to r)))
      (glPfZ to pl lb m rb pr q g)) moveLeft)
lookLeft {pl} {pr} o to a
  (MkZipDownS (MkRBZipS (BlkS {lb} {rb} l m w r g) p q) j) = sym (strippyZ to a
    (MkRBZipS (BlkS l m w r g) p q)
    (MkRBZipS l
      (BlkLS m w r p (glPfC to pl lb m rb pr q g
                            (pfOrdered to l) (pfOrdered to r)))
      (glPfZ to pl lb m rb pr q g)) moveLeft)

lookRight o to a (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
lookRight {pc=True} o to a
  (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) = either void void (snd j)
lookRight {pc=False} {pl} {pr} o to a
  (MkZipDownS (MkRBZipS (RedS {lb} {rb} l m w r g) p q) j) = sym (strippyZ to a
    (MkRBZipS (RedS l m w r g) p q)
    (MkRBZipS r
      (RedRS l m w p (grPfC to pl lb m rb pr q g
                            (pfOrdered to l) (pfOrdered to r)))
      (grPfZ to pl lb m rb pr q g)) moveRight)
lookRight {pl} {pr} o to a
  (MkZipDownS (MkRBZipS (BlkS {lb} {rb} l m w r g) p q) j) = sym (strippyZ to a
    (MkRBZipS (BlkS l m w r g) p q)
    (MkRBZipS r
      (BlkRS l m w p (grPfC to pl lb m rb pr q g
                            (pfOrdered to l) (pfOrdered to r)))
      (grPfZ to pl lb m rb pr q g)) moveRight)

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
