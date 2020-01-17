module RBTreeS.SearchS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains functions for unzipping the tree to a specific key.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import public RBTreeS.StructsS
import public RBTreeS.Types
import RBTreeS.DownS
import RBTreeS.SizeUp
import StepRec
import RBTreeS.FmapS
import RBTreeS.LookS

public export
total IsGoodZipS : Comp k -> k -> Maybe k -> Maybe k -> Type
IsGoodZipS o a pl pr = (IsGoodZipL o a pl, IsGoodZipR o a pr)

public export
total ssIsGoodZipS : (o : Comp k) -> (a : k) -> (pl : Maybe k) ->
                    (pr : Maybe k) -> SubSing (IsGoodZipS o a pl pr)
ssIsGoodZipS o a pl pr = ssPair (ssIsGoodZipL o a pl) (ssIsGoodZipR o a pr)

public export
record ZipSearchS k (o : Comp k) (v : k -> Type) (a : k) where
  constructor MkZipSearchS
  ccZSS, pcZSS : Bool
  hZSS, dZSS : Nat
  cbZSS : Bnds k
  plZSS, prZSS : Maybe k
  zipZSS : RBZipS ccZSS pcZSS hZSS hZSS dZSS k o cbZSS plZSS prZSS v
  canZSS : Either (IsFalse ccZSS) (IsFalse pcZSS)
  prpZSS : IsGoodZipS o a plZSS prZSS

public export
total mkZipSearchS : RBZipS cc pc h h d k o cb pl pr v ->
                     Either (IsFalse cc) (IsFalse pc) ->
                     IsGoodZipS o a pl pr -> ZipSearchS k o v a
mkZipSearchS z j q = MkZipSearchS _ _ _ _ _ _ _ z j q

public export
total rwZipSearchS : {z : RBZipS cc pc h h d k o cb pl pr v} ->
                     {z' : RBZipS cc pc h h d k o cb pl pr v} ->
                     {j : Either (IsFalse cc) (IsFalse pc)} ->
                     {j' : Either (IsFalse cc) (IsFalse pc)} ->
                     {p : IsGoodZipS o a pl pr} ->
                     {p' : IsGoodZipS o a pl pr} -> z = z' -> j = j' ->
                     mkZipSearchS z j p = mkZipSearchS z' j' p'

rwZipSearchS {o} {a} {pl} {pr} {p} {p'} ze je
  with (ssIsGoodZipS o a pl pr p p')
    rwZipSearchS Refl Refl | Refl = Refl

public export
total zipUpSearchS : RBTreeS False h k o b v ->
                     ZipSearchS k o v a
zipUpSearchS {b} {h} t =
  MkZipSearchS False True h Z b Nothing Nothing (zipUpS t) (Left ()) ((), ())

public export
total zsmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipSearchS k o v a -> ZipSearchS k o v' a

public export
total IsGoodZipF : Comp k -> k -> Maybe k -> Maybe k -> Maybe k -> Type
IsGoodZipF o a pl pr = maybe (IsGoodZipS o a pl pr) (IsEQ . o a)

public export
total ssIsGoodZipF : (o : Comp k) -> (a : k) -> (pl : Maybe k) ->
                     (pr : Maybe k) -> (m : Maybe k) ->
                     SubSing (IsGoodZipF o a pl pr m)
ssIsGoodZipF o a pl pr =
  ssMebbe (ssIsGoodZipS o a pl pr) (\m => ssIsEQ (o a m))

public export
record ZipFoundS k (o : Comp k) (v : k -> Type) (a : k) where
  constructor MkZipFoundS
  ccFS, pcFS : Bool
  hFS, dFS : Nat
  cbFS : Bnds k
  plFS, prFS : Maybe k
  zipFS : RBZipS ccFS pcFS hFS hFS dFS k o cbFS plFS prFS v
  canFS : Either (IsFalse ccFS) (IsFalse pcFS)
  prpFS : IsGoodZipF o a plFS prFS (sipK zipFS)

public export
total mkZipFoundS : (z : RBZipS cc pc h h d k o cb pl pr v) ->
                   Either (IsFalse cc) (IsFalse pc) ->
                   IsGoodZipF o a pl pr (sreeK (child z)) ->
                   ZipFoundS k o v a
mkZipFoundS z j q = MkZipFoundS _ _ _ _ _ _ _ z j q

public export
total rwZipFoundS : {z : RBZipS cc pc h h d k o cb pl pr v} ->
                     {z' : RBZipS cc pc h h d k o cb pl pr v} ->
                     {j : Either (IsFalse cc) (IsFalse pc)} ->
                     {j' : Either (IsFalse cc) (IsFalse pc)} ->
                     {p : IsGoodZipF o a pl pr (sipK z)} ->
                     {p' : IsGoodZipF o a pl pr (sipK z')} ->
                     z = z' -> j = j' ->
                     mkZipFoundS z j p = mkZipFoundS z' j' p'

rwZipFoundS {o} {a} {pl} {pr} {p} {p'} {z} {z'=z} Refl je
  with (ssIsGoodZipF o a pl pr (sipK z) p p')
    rwZipFoundS Refl Refl | Refl = Refl

public export
Sized (ZipSearchS k o v a) where
  size z = ccZSS z `sizeUp` hZSS z

public export
total zfmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipFoundS k o v a -> ZipFoundS k o v' a

public export
total searchS : TotalOrd k o -> (a : k) ->
                ZipSearchS k o v a -> ZipFoundS k o v a

-- Theorems

export
total mapSearchS : {v' : k -> Type} -> (to : TotalOrd k o) ->
                   (f : (a : k) -> v a -> v' a) ->
                   (z : ZipSearchS k o v a) ->
                   searchS to a (zsmapS f z) = zfmapS f (searchS to a z)

export
total lookSearch : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) -> (b : k) ->
                   (z : ZipSearchS k o v a) ->
                   lookZip o to b (zipFS (searchS to a z)) =
                   lookZip o to b (zipZSS z)

-- Implementation

zsmapS f (MkZipSearchS _ _ _ _ _ _ _ z c p) = mkZipSearchS (zmapS f z) c p

zfmapS f (MkZipFoundS _ _ _ _ _ _ _ z c p) =
  mkZipFoundS (zmapS f z) c (replace (sym (mapSipK f z)) p)

public export
total searchStepS : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                    Step (ZipSearchS k o v a) (ZipFoundS k o v a) Smaller

searchStepS o to a (MkZipSearchS _ _ _ _ _ _ _ (MkRBZipS LifS p g) j q) =
  Left (mkZipFoundS (MkRBZipS LifS p g) j q)
searchStepS o to a (MkZipSearchS _ _ _ _ _ _ _
  (MkRBZipS (RedS l m w r e) p g) j q) with (enh o a m)
    | ELT x = Right (mkZipSearchS (goLeftS to (MkZipDownS (MkRBZipS 
      (RedS l m w r e) p g) (Left (), j))) (Left ()) (fst q, x) ** sultCol _)
    | EEQ x = Left (mkZipFoundS (MkRBZipS (RedS l m w r e) p g) j x)
    | EGT x = Right (mkZipSearchS (goRightS to (MkZipDownS (MkRBZipS
      (RedS l m w r e) p g) (Left (), j))) (Left ()) (x, snd q) ** sultCol _)
searchStepS o to a (MkZipSearchS _ _ _ _ _ _ _
  (MkRBZipS (BlkS l m w r e) p g) j q) with (enh o a m)
    | ELT x = Right (mkZipSearchS (goLeftS to (MkZipDownS (MkRBZipS
      (BlkS l m w r e) p g) (Right (), j))) (Right ()) (fst q, x) **
        sultNum Z _ False _)
    | EEQ x = Left (mkZipFoundS (MkRBZipS (BlkS l m w r e) p g) j x)
    | EGT x = Right (mkZipSearchS (goRightS to (MkZipDownS (MkRBZipS
      (BlkS l m w r e) p g) (Right (), j))) (Right ()) (x, snd q) **
        sultNum Z _ False _)

searchS {o} to a = sizeStepRec (searchStepS o to a)

-- Proofs

total mapSearchSStep : {v : k -> Type} -> {v' : k -> Type} ->
                       (to : TotalOrd k o) ->
                       (f : (a : k) -> v a -> v' a) ->
                       SizeCommStep (zsmapS f) (zfmapS f)
                       (searchStepS o to a) (searchStepS o to a)
                         
total csZsmapS : {v : k -> Type} -> {v' : k -> Type} ->
                 (f : (a : k) -> v a -> v' a) ->
                 CompatSize (zsmapS f)
csZsmapS f (MkZipSearchS _ _ _ _ _ _ _ z c p) = Refl

mapSearchSStep to f (MkZipSearchS _ _ _ _ _ _ _ (MkRBZipS LifS p g) j q) =
  cong $ rwZipFoundS Refl Refl
mapSearchSStep {o} {a} {v'} to f (MkZipSearchS _ _ _ _ _ _ _ (MkRBZipS
  (RedS l m w r b) p g) j q) with (enh o a m)
    | ELT x = let mpart = mapLeftS to {v'} f (MkZipDownS 
                        (MkRBZipS (RedS l m w r b) p g) (Left (), j)) in 
      cong $ rwZipSearchS mpart Refl
    | EEQ x = cong $ rwZipFoundS Refl Refl
    | EGT x = let mpart = mapRightS to {v'} f (MkZipDownS 
                        (MkRBZipS (RedS l m w r b) p g) (Left (), j)) in
      cong $ rwZipSearchS mpart Refl
mapSearchSStep {o} {a} {v'} to f (MkZipSearchS _ _ _ _ _ _ _ (MkRBZipS 
  (BlkS l m w r b) p g) j q) with (enh o a m)
    | ELT x = let mpart = mapLeftS to {v'} f (MkZipDownS 
                        (MkRBZipS (BlkS l m w r b) p g) (Right (), j)) in 
      cong $ rwZipSearchS mpart Refl
    | EEQ x = cong $ rwZipFoundS Refl Refl
    | EGT x = let mpart = mapRightS to {v'} f (MkZipDownS
                        (MkRBZipS (BlkS l m w r b) p g) (Right (), j)) in
      cong $ rwZipSearchS mpart Refl

mapSearchS to f = sizeRecComm (csZsmapS f) (mapSearchSStep to f)

total zsl : TotalOrd k o -> (b : k) -> ZipSearchS k o v a -> Maybe (v b)
total zfl : TotalOrd k o -> (b : k) -> ZipFoundS k o v a -> Maybe (v b)

zsl {o} to b z = lookZip o to b (zipZSS z)
zfl {o} to b z = lookZip o to b (zipFS z)

total lookSearchStep : (to : TotalOrd k o) -> (a : k) -> (b : k) ->
                       StepPropEq (Maybe (v b))
                                  (searchStepS {v} o to a)
                                  (zsl to b)
                                  (zfl to b)

lookSearchStep to a b (MkZipSearchS _ _ _ _ _ _ _
  (MkRBZipS LifS p g) j q) = Refl
lookSearchStep {o} to a b (MkZipSearchS _ _ _ _ _ _ _
  (MkRBZipS (RedS l m w r f) p g) j q) with (enh o a m)
    | ELT x = lookLeft o to b (MkZipDownS
                (MkRBZipS (RedS l m w r f) p g) (Left (), j))
    | EEQ x = Refl
    | EGT x = lookRight o to b (MkZipDownS
                (MkRBZipS (RedS l m w r f) p g) (Left (), j))
lookSearchStep {o} to a b (MkZipSearchS _ _ _ _ _ _ _
  (MkRBZipS (BlkS l m w r f) p g) j q) with (enh o a m)
    | ELT x = lookLeft o to b (MkZipDownS
                (MkRBZipS (BlkS l m w r f) p g) (Right (), j))
    | EEQ x = Refl
    | EGT x = lookRight o to b (MkZipDownS
                (MkRBZipS (BlkS l m w r f) p g) (Right (), j))

lookSearch o to a b =
  sizeStepRecEq (searchStepS o to a) (lookSearchStep to a b)

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
