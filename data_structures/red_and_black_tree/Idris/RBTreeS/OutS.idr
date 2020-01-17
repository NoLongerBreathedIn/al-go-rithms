module RBTreeS.OutS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains functions related to getting out of a tree.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import public RBTreeS.StructsS
import public RBTreeS.Types
import RBTreeS.UpS
import RBTreeS.SizeUp
import StepRec
import RBTreeS.FmapS
import RBTreeS.LookS

public export
total EqSum : Nat -> Nat -> Nat -> Type
EqSum result augend addend = result = augend + addend

public export
record ZipOutS (k : Type) (o : Comp k) (v : k -> Type) (n : Nat) where
  constructor MkZipOutS
  ccOS, pcOS : Bool
  htOS, dpOS : Nat
  cbOS : Bnds k
  plOS, prOS : Maybe k
  zipOS : RBZipS ccOS pcOS htOS htOS dpOS k o cbOS plOS prOS v
  canOS : Either (IsFalse ccOS) (IsFalse pcOS)
  prpOS : EqSum n htOS dpOS

public export
total mkZipOutS : RBZipS cc pc h h d k o cb pl pr v ->
                  Either (IsFalse cc) (IsFalse pc) ->
                  ZipOutS k o v (h + d)

public export
total mkZipOutS' : RBZipS cc pc h h d k o cb pl pr v ->
                   Either (IsFalse cc) (IsFalse pc) ->
                   {n : Nat} -> n = h + d -> ZipOutS k o v n

mkZipOutS' z j q = MkZipOutS _ _ _ _ _ _ _ z j q

mkZipOutS {h} {d} z j = mkZipOutS' z j Refl

public export
total rwZipOutS : {n : Nat} ->
                  {z : RBZipS cc pc h h d k o cb pl pr v} ->
                  {z' : RBZipS cc pc h h d k o cb pl pr v} ->
                  {j : Either (IsFalse cc) (IsFalse pc)} ->
                  {j' : Either (IsFalse cc) (IsFalse pc)} ->
                  {q : n = h + d} -> {q' : n = h + d} ->
                  z = z' -> j = j' ->
                  mkZipOutS' z j q = mkZipOutS' z' j' q'
rwZipOutS {n} {h} {d} {q} {q'} ze je with (ssEql n (h + d) q q')
  rwZipOutS Refl Refl | Refl = Refl

public export
total zomapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipOutS k o v n -> ZipOutS k o v' n

public export
Sized (ZipOutS k o v n) where
  size z = pcOS z `sizeUp` dpOS z

public export
total TreeHide : (k : Type) -> Comp k -> (k -> Type) -> Nat -> Type
TreeHide k o v n = (b : Bnds k ** RBTreeS False n k o b v)

public export
total thmap : {v' : k -> Type} ->  ((a : k) -> v a -> v' a) ->
               TreeHide k o v n -> TreeHide k o v' n

public export
total ejectS : TotalOrd k o -> ZipOutS k o v n -> TreeHide k o v n

-- Theorems

export
total mapEjectS : {v' : k -> Type} -> (to : TotalOrd k o) ->
                  (f : (a : k) -> v a -> v' a) ->
                  (z : ZipOutS k o v n) ->
                  ejectS to (zomapS f z) = thmap f (ejectS to z)

export
total lookEject : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (z : ZipOutS k o v n) ->
                  lookTreeS o to a (snd (ejectS to z)) =
                  lookZip o to a (zipOS z)

-- Implementation

zomapS f (MkZipOutS _ _ _ _ _ _ _ z j q) = mkZipOutS' (zmapS f z) j q
thmap f (b ** t) = (b ** tmapS f t)

public export
total ejectStepS : TotalOrd k o ->
                   Step (ZipOutS k o v n) (TreeHide k o v n) Smaller

public export
total upGood : (z : RBZipS cc pc ch ph (S d) k o cb pl pr v) ->
               Either (IsFalse pc) (IsFalse $ sipPc z)

public export
total upGood' : (cr : RBCrumbS c h (S d) k o l r v) ->
                Either (IsFalse c) (IsFalse $ srPc cr)
upGood (MkRBZipS c p q) = upGood' p

public export
total shdi : (m : Nat) -> (n : Nat) -> (b : Bool) ->
             m + S n = succHD b m + succHD (not b) n

public export
total upDec : (tc : Bool) -> (pc : Bool) -> (d : Nat) ->
              Either (IsFalse tc) (IsFalse pc) ->
              sizeUp pc (succHD (not tc) d) `LT` sizeUp tc (S d)

ejectStepS to (MkZipOutS cc _ h Z cb _ _ z j q) with (parnt z)
  | RootS with (cc)
    | False = Left (cb ** rewrite trans q (plusZeroRightNeutral h) in child z)
    | True = either void void j
  | RedLS _ _ _ _ _ impossible
  | RedRS _ _ _ _ _ impossible
ejectStepS {n} to (MkZipOutS _ pc h (S d) _ _ _ z j q) =
  let ug = upGood z in
    Right (mkZipOutS' (goUpS to $ MkZipUpS z j) ug (trans q $ shdi h d pc) **
           upDec pc (sipPc z) d ug)

ejectS = sizeStepRec . ejectStepS

-- Miniproofs

upDec False _ _ = const $ sultNum Z _ False _
upDec True False _ = const lteRefl
upDec True True _ = either void void

upGood' (RedLS _ _ _ _ _) = Right ()
upGood' (RedRS _ _ _ _ _) = Right ()
upGood' (BlkLS _ _ _ _ _) = Left ()
upGood' (BlkRS _ _ _ _ _) = Left ()

shdi _ _ True = Refl
shdi m n False = sym $ plusSuccRightSucc m n

-- Proofs

total mapEjectSStep : {v : k -> Type} -> {v' : k -> Type} ->
                      (to : TotalOrd k o) ->
                      (f : (a : k) -> v a -> v' a) ->
                      SizeCommStep (zomapS f) (thmap f)
                      (ejectStepS to) (ejectStepS to)

total csZomapS : {v : k -> Type} -> {v' : k -> Type} ->
                 (f : (a : k) -> v a -> v' a) ->
                 CompatSize (zomapS f)
csZomapS f (MkZipOutS _ _ _ _ _ _ _ z j q) = Refl

total mapEjectSStep' : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                       {m : Nat} -> {n : Nat} -> (q : m = n) ->
                       (t : RBTreeS c n k o b v) ->
                       rewrite__impl (\nn => RBTreeS c nn k o b v') q
                         (tmapS f t) = tmapS f (rewrite q in t)

mapEjectSStep _ f (MkZipOutS cc _ h Z cb _ _ (MkRBZipS c p g) j q) with (p)
  | RootS with (cc)
    | False = cong {f=\g => Left (cb ** g)} $
              mapEjectSStep' f (trans q $ plusZeroRightNeutral h) c
    | True = either void void j
  | RedLS _ _ _ _ _ impossible
  | BlkLS _ _ _ _ _ impossible
mapEjectSStep to {v'} f (MkZipOutS True _ _ (S d) _ _ _
  (MkRBZipS c (RedLS m w r p x) g) j q) = either void void j
mapEjectSStep to {v'} f (MkZipOutS True _ h (S d) _ _ _
  (MkRBZipS c (RedRS l m w p x) g) j q) = either void void j
mapEjectSStep to {v'} f (MkZipOutS False _ h (S d) _ _ _
  (MkRBZipS c (RedLS m w r p x) g) j q) = Refl
mapEjectSStep to {v'} f (MkZipOutS False _ h (S d) _ _ _
  (MkRBZipS c (RedRS l m w p x) g) j q) = Refl
mapEjectSStep to {v'} f (MkZipOutS _ _ h (S d) _ _ _
  (MkRBZipS c (BlkLS m w r p x) g) j q) = Refl
mapEjectSStep to {v'} f (MkZipOutS _ _ h (S d) _ _ _
  (MkRBZipS c (BlkRS l m w p x) g) j q) = Refl

mapEjectS to f = sizeRecComm (csZomapS f) (mapEjectSStep to f)

mapEjectSStep' f Refl t = Refl

total zol : TotalOrd k o -> (a : k) -> ZipOutS k o v n -> Maybe (v a)
total thl : TotalOrd k o -> (a : k) -> TreeHide k o v n -> Maybe (v a)

zol {o} to a z = lookZip o to a $ zipOS z
thl {o} to a z = lookTreeS o to a $ snd z

total lookEjectStep : (to : TotalOrd k o) -> (a : k) ->
                      StepPropEq {rel=Smaller}
                                 (Maybe (v a))
                                 (ejectStepS {v} to)
                                 (zol to a)
                                 (thl to a)

total lookEjectStep' : {m : Nat} -> {n : Nat} -> (q : m = n) ->
                       (to : TotalOrd k o) -> (a : k) ->
                       (t : RBTreeS False n k o b v) ->
                       lookTreeS o to a $
                         rewrite__impl (\nn => RBTreeS False nn k o b v) q t =
                       lookTreeS o to a t

lookEjectStep to a (MkZipOutS cc _ h Z _ _ _ z j q) with (parnt z)
  | RootS with (cc)
    | False = lookEjectStep' (trans q $ plusZeroRightNeutral h) to a (child z)
    | True = either void void j
  | RedLS _ _ _ _ _ impossible
  | RedRS _ _ _ _ _ impossible
lookEjectStep {o} to a (MkZipOutS _ pc h (S d) _ _ _ z j q) =
  lookUp o to a (MkZipUpS z j)

lookEject o to a = sizeStepRecEq (ejectStepS to) (lookEjectStep to a)

lookEjectStep' Refl _ _ _ = Refl

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
