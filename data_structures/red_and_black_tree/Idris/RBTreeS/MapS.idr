module RBTreeS.MapS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file brings it all together.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing

import RBTreeS.Types
import RBTreeS.StructsS
import RBTreeS.FmapS
import RBTreeS.LookS

public export
record RBMapS k (v : k -> Type) where
  constructor MkRBMapS
  to : Comp k
  depth : Nat
  bounds : Bnds k
  pf : TotalOrd k to
  contents : RBTreeS False depth k to bounds v

public export
total rbMapSOrder : RBMapS k v -> Comp k
rbMapSOrder = to

public export
total emptyS : (o : Comp k) -> TotalOrd k o -> RBMapS k v

public export
total lookupS : (a : k) -> RBMapS k v -> Maybe (v a)

{-
public export
total insertS : (a : k) -> v a -> RBMapS k v -> RBMapS k v

public export
total removeS : k -> RBMapS k v -> RBMapS k v
-}

public export
total mapmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
                RBMapS k v -> RBMapS k v'

-- Theorems

{-
export
total lookupInsertDiff : (a : k) -> (b : k) -> (bv : v b) ->
                         (m : RBMapS k v) -> IsNE (rbMapOrder m a b) ->
                         lookupS a (insertS b bv m) = lookupS a m

export
total lookupInsertSame : (a : k) -> (av : v a) -> (m : RBMapS k v) ->
                         lookupS a (insertS a av m) = Just av

export
total lookupRemoveDiff : (a : k) -> (b : k) -> (m : RBMapS k v) ->
                         IsNE (rbMapOrder m a b) ->
                         lookupS a (removeS b m) = lookupS a m

export
total lookupRemoveSame : (a : k) -> (m : RBMapS k v) ->
                         lookupS a (removeS a m) = Nothing
-}

export
total lookupEmptyS : (a : k) -> (o : Comp k) -> (t : TotalOrd k o) ->
                     lookupS a (emptyS o t) = Nothing
export
total lookupMapS : {v' : k -> Type} -> (a : k) ->
                   (f : (b : k) -> v b -> v' b) -> (m : RBMapS k v) ->
                   lookupS a (mapmapS f m) = map (f a) (lookupS a m)
export
total mapmapIdS : (m : RBMapS k v) -> mapmapS (\b => id {a=v b}) m = m
export
total mapmapCompS : {v' : k -> Type} -> {w : k -> Type} -> (m : RBMapS k v) ->
                    (f : (a : k) -> v a -> v' a) ->
                    (g : (a : k) -> v' a -> w a) ->
                    mapmapS g (mapmapS f m) = mapmapS (\a => g a . f a) m

{-
export
total insertMapS : (a : k) -> (w : v a) -> (m : RBMapS k v) ->
                   (f : (b : k) -> v b -> v' b) ->
                   insertS a (f a w) (mapmapS f m) = mapmapS f (insertS a w m)

export
total removeMapS : (a : k) -> (m : RBMapS k v) ->
                   (f : (b : k) -> v b -> v' b) ->
                   removeS a (mapmapS f m) = mapmapS f (removeS a m)
-}

export
total emptyMapS : {v : k -> Type} -> {v' : k -> Type} ->
                  (o : Comp k) -> (p : TotalOrd k o) ->
                  (f : (b : k) -> v b -> v' b) ->
                  mapmapS f (emptyS o p) = emptyS {v=v'} o p

{-
export
total removeEmptyS : (a : k) -> (o : Comp k) -> (t : TotalOrd k o) ->
                     removeS a (emptyS o t) = emptyS o t
-}

-- Implementation

emptyS o p = MkRBMapS o Z Nothing p LifS

lookupS a (MkRBMapS to depth bounds pf contents) =
  lookTreeS to pf a contents

mapmapS f (MkRBMapS to depth bounds pf contents) =
  MkRBMapS to depth bounds pf (tmapS f contents)

-- Proofs

{-
lookupInsertDiff a b w m pf = ?lid
lookupInsertSame a w m = ?lis
lookupRemoveDiff a b m pf = ?lrd
lookupRemoveSame a m = ?lrs
-}

lookupEmptyS a o t = Refl

lookupMapS a f (MkRBMapS o d b to t) = lookTmapS o to a f t

mapmapIdS (MkRBMapS o d b to t) = cong $ tmapIdS t

mapmapCompS (MkRBMapS o d b to t) f g = cong $ tmapCompS t f g

{-
insertMapS a m f = ?insMap
removeMapS a m f = ?remMap
-}

emptyMapS o p f = Refl

{-
removeEmptyS a o t = ?remEmp
-}

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
