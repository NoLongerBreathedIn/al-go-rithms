module RBTreeS.SearchLookS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains proofs that the functions in SearchS are correct.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import public RBTreeS.SearchS
import public RBTreeS.SizeUp
import RBTreeS.LookS
import RBTreeS.DownS
import StepRec

-- Theorems

export
total lookSearch : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) -> (b : k) ->
                   (z : ZipSearchS k o v a) ->
                   lookZip o to b (zipFS (searchS to a z)) =
                   lookZip o to b (zipZSS z)

-- Proofs:

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
