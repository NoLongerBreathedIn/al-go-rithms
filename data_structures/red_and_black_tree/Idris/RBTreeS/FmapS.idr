module RBTreeS.FmapS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file is for mapping functions.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import public RBTreeS.StructsS

public export
total tmapS : {v : k -> Type} -> ((a : k) -> v a -> v' a) ->
              RBTreeS c h k o b v -> RBTreeS c h k o b v'

public export
total cmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
              RBCrumbS c h d k o pl pr v -> RBCrumbS c h d k o pl pr v'

public export
total zmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
             RBZipS cc pc ch ph pd k o cb pl pr v ->
             RBZipS cc pc ch ph pd k o cb pl pr v'

-- Theorems

export
total tmapIdS : (t : RBTreeS c h k o b v) -> tmapS (\q => id {a=v q}) t = t
export
total tmapCompS : {v' : k -> Type} -> {w : k -> Type} ->
                  (t : RBTreeS c h k o b v) ->
                  (f : (a : k) -> v a -> v' a) ->
                  (g : (a : k) -> v' a -> w a) ->
                  tmapS g (tmapS f t) = tmapS (\a => g a . f a) t
export
total mapChildS : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                  (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                  child (zmapS f z) = tmapS f (child z)
export
total mapParntS : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                  (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                  parnt (zmapS f z) = cmapS f (parnt z)
export
total mapSreeK : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                 (t : RBTreeS c h k o b v) ->
                 sreeK (tmapS f t) = sreeK t
export
total mapSipK : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                sipK (zmapS f z) = sipK z
export
total mapSrK : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
               (cr : RBCrumbS c h d k o pl pr v) ->
               srK (cmapS f cr) = srK cr
export
total mapSipJ : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                sipJ (zmapS f z) = sipJ z
export
total mapSreeLc : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                  (t : RBTreeS c h k o b v) ->
                  sreeLc (tmapS f t) = sreeLc t
export
total mapSipLc : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                 (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                 sipLc (zmapS f z) = sipLc z
export
total mapSreeRc : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                  (t : RBTreeS c h k o b v) ->
                  sreeRc (tmapS f t) = sreeRc t
export
total mapSipRc : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                 (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                 sipRc (zmapS f z) = sipRc z
export
total mapTreeLb : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                  (t : RBTreeS c h k o b v) ->
                  treeLb (tmapS f t) = treeLb t
export
total mapZipLb : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                 (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                 zipLb (zmapS f z) = zipLb z
export
total mapTreeRb : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                  (t : RBTreeS c h k o b v) ->
                  treeRb (tmapS f t) = treeRb t
export
total mapZipRb : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
                 (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                 zipRb (zmapS f z) = zipRb z

-- Implementation

tmapS f LifS = LifS
tmapS f (RedS l m mv r pf) = RedS (tmapS f l) m (f m mv) (tmapS f r) pf
tmapS f (BlkS l m mv r pf) = BlkS (tmapS f l) m (f m mv) (tmapS f r) pf

cmapS f RootS = RootS
cmapS f (RedLS m w r p q) = RedLS m (f m w) (tmapS f r) (cmapS f p) q
cmapS f (RedRS l m w p q) = RedRS (tmapS f l) m (f m w) (cmapS f p) q
cmapS f (BlkLS m w r p q) = BlkLS m (f m w) (tmapS f r) (cmapS f p) q
cmapS f (BlkRS l m w p q) = BlkRS (tmapS f l) m (f m w) (cmapS f p) q

zmapS f (MkRBZipS t c q) = MkRBZipS (tmapS f t) (cmapS f c) q

-- Proofs

tmapIdS LifS = Refl
tmapIdS (RedS l m w r p) = rwRedS (tmapIdS l) (tmapIdS r)
tmapIdS (BlkS l m w r p) = rwBlkS (tmapIdS l) (tmapIdS r)

tmapCompS LifS f g = Refl
tmapCompS (RedS l m w r p) f g = rwRedS (tmapCompS l f g) (tmapCompS r f g)
tmapCompS (BlkS l m w r p) f g = rwBlkS (tmapCompS l f g) (tmapCompS r f g)

mapChildS f (MkRBZipS c p q) = Refl
mapParntS f (MkRBZipS c p q) = Refl
mapSreeK f LifS = Refl
mapSreeK f (RedS l m w r p) = Refl
mapSreeK f (BlkS l m w r p) = Refl
mapSipK f (MkRBZipS c p q) = mapSreeK f c
mapSrK f RootS = Refl
mapSrK f (RedLS m w s p g) = Refl
mapSrK f (RedRS s m w p g) = Refl
mapSrK f (BlkLS m w s p g) = Refl
mapSrK f (BlkRS s m w p g) = Refl
mapSipJ f (MkRBZipS c p q) = mapSrK f p
mapSreeLc f LifS = Refl
mapSreeLc f (RedS l m w r p) = Refl
mapSreeLc f (BlkS l m w r p) = Refl
mapSipLc f (MkRBZipS c p q) = mapSreeLc f c
mapSreeRc f LifS = Refl
mapSreeRc f (RedS l m w r p) = Refl
mapSreeRc f (BlkS l m w r p) = Refl
mapSipRc f (MkRBZipS c p q) = mapSreeRc f c
mapTreeLb f LifS = Refl
mapTreeLb f (RedS l m w r p) = Refl
mapTreeLb f (BlkS l m w r p) = Refl
mapZipLb f (MkRBZipS c p q) = mapTreeLb f c
mapTreeRb f LifS = Refl
mapTreeRb f (RedS l m w r p) = Refl
mapTreeRb f (BlkS l m w r p) = Refl
mapZipRb f (MkRBZipS c p q) = mapTreeRb f c

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
