module RBTreeS.SearchFmapS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains a proof
-- that the functions in SearchS interact properly with fmap.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import public RBTreeS.SearchS
import RBTreeS.SizeUp
import RBTreeS.FmapS
import StepRec
import RBTreeS.DownS


public export
total zsmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipSearchS k o v a -> ZipSearchS k o v' a

public export
total zfmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipFoundS k o v a -> ZipFoundS k o v' a

-- Theorems

export
total mapSearchS : {v' : k -> Type} -> (to : TotalOrd k o) ->
                   (f : (a : k) -> v a -> v' a) ->
                   (z : ZipSearchS k o v a) ->
                   searchS to a (zsmapS f z) = zfmapS f (searchS to a z)

-- Implementation:

zsmapS f (MkZipSearchS _ _ _ _ _ _ _ z c p) = mkZipSearchS (zmapS f z) c p

zfmapS f (MkZipFoundS _ _ _ _ _ _ _ z c p) =
  mkZipFoundS (zmapS f z) c (replace (sym (mapSipK f z)) p)

-- Proofs:

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
-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
 
