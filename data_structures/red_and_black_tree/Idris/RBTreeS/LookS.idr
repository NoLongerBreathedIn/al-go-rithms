module RBTreeS.LookS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains functions related to lookup.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import public RBTreeS.StructsS
import RBTreeS.FmapS
import BST.LookB

-- Main interface

mutual
  public export
  total lookTreeS : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                    RBTreeS c h k o b v -> Maybe (v a)
  public export
  total pickTreeS : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                    RBTreeS lc lh k o lb v -> (m : k) -> v m ->
                    RBTreeS rc rh k o rb v ->
                    Maybe (v a)

  pickTreeS o to a l m w r with (enh o a m)
    | ELT x = lookTreeS o to a l
    | EEQ x = Just (replace (corff to x) w)
    | EGT x = lookTreeS o to a r

  lookTreeS o to a LifS = Nothing
  lookTreeS o to a (RedS l m w r p) = pickTreeS o to a l m w r
  lookTreeS o to a (BlkS l m w r p) = pickTreeS o to a l m w r

mutual
  public export
  total lookCrumb : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                    RBCrumbS c h d k o pl pr v -> Maybe (v a)
  public export
  total pickCrumbL : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                     (m : k) -> v m -> RBTreeS cc ch k o cb v ->
                     RBCrumbS pc ph pd k o pl pr v -> Maybe (v a)
  public export
  total pickCrumbR : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                     RBTreeS cc ch k o cb v -> (m : k) -> v m ->
                     RBCrumbS pc ph pd k o pl pr v -> Maybe (v a)

  pickCrumbL {pr} o to a m w c p with (enh o a m)
    | ELT x = lookCrumb o to a p
    | EEQ x = Just (replace (corff to x) w)
    pickCrumbL {pr=Nothing} o to a m w c p | EGT x = lookTreeS o to a c
    pickCrumbL {pr=Just r} o to a m w c p | EGT x with (enh o a r)
      | ELT y = lookTreeS o to a c
      | EEQ y = lookCrumb o to a p
      | EGT y = lookCrumb o to a p

  pickCrumbR {pl} o to a c m w p with (enh o a m)
    pickCrumbR {pl=Nothing} o to a c m w p | ELT x = lookTreeS o to a c
    pickCrumbR {pl=Just l} o to a c m w p | ELT x with (enh o a l)
      | ELT y = lookCrumb o to a p
      | EEQ y = lookCrumb o to a p
      | EGT y = lookTreeS o to a c
    | EEQ x = (Just (replace (corff to x) w))
    | EGT x = lookCrumb o to a p

  lookCrumb o to a RootS = Nothing
  lookCrumb o to a (RedLS m w r c p) = pickCrumbL o to a m w r c
  lookCrumb o to a (RedRS l m w c p) = pickCrumbR o to a l m w c
  lookCrumb o to a (BlkLS m w r c p) = pickCrumbL o to a m w r c
  lookCrumb o to a (BlkRS l m w c p) = pickCrumbR o to a l m w c

public export
total lookZip : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                RBZipS cc pc ch ph pd k o cb pl pr v -> Maybe (v a)
public export
total lookZip' : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                 RBZipS cc pc ch ph pd k o cb pl pr v -> Maybe (v a)

lookZip' {pr=Nothing} o to a z = lookTreeS o to a (child z)
lookZip' {pr=Just r} o to a z with (enh o a r)
  | ELT x = lookTreeS o to a (child z)
  | EEQ x = lookCrumb o to a (parnt z)
  | EGT x = lookCrumb o to a (parnt z)

lookZip {pl=Nothing} o to a z = lookZip' o to a z
lookZip {pl=Just l} o to a z with (enh o a l)
  | ELT x = lookCrumb o to a (parnt z)
  | EEQ x = lookCrumb o to a (parnt z)
  | EGT x = lookZip' o to a z

-- Theorems

export
total strippyT : {o : Comp k} -> (to : TotalOrd k o) -> (a : k) ->
                 (t : RBTreeS c h k o b v) -> (t' : RBTreeS c' h' k o b' v) ->
                 lookT o to a (stripT t) = lookT o to a (stripT t') ->
                 lookTreeS o to a t = lookTreeS o to a t'

export
total strippyC : {o : Comp k} -> (to : TotalOrd k o) -> (a : k) ->
                 (cr : RBCrumbS c h d k o l r v) ->
                 (cr' : RBCrumbS c' h' d' k o l' r' v) ->
                 lookC o to a (stripC cr) = lookC o to a (stripC cr') ->
                 lookCrumb o to a cr = lookCrumb o to a cr'

export
total strippyZ : {o : Comp k} -> (to : TotalOrd k o) -> (a : k) ->
                 (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                 (z' : RBZipS cc' pc' ch' ph' pd' k o cb' pl' pr' v) ->
                 lookZ o to a (stripZ z) = lookZ o to a (stripZ z') ->
                 lookZip o to a z = lookZip o to a z'

export
total zipUpLook : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (t : RBTreeS c h k o b v) ->
                  lookZip o to a (zipUpS t) = lookTreeS o to a t

-- Proofs

mutual
  total stripLT : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (t : RBTreeS c h k o b v) ->
                  lookT o to a (stripT t) = lookTreeS o to a t
  total stripPT : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (l : RBTreeS lc lh k o lb v) -> (m : k) -> (w : v m) ->
                  (r : RBTreeS rc rh k o rb v) ->
                  pickT o to a (stripT l) m w (stripT r) =
                  pickTreeS o to a l m w r

  stripPT o to a l m w r with (enh o a m)
    | ELT x = stripLT o to a l
    | EEQ x = Refl
    | EGT x = stripLT o to a r
  
  stripLT o to a LifS = Refl
  stripLT o to a (RedS l m w r p) = stripPT o to a l m w r
  stripLT o to a (BlkS l m w r p) = stripPT o to a l m w r

strippyT {o} to a t t' p = 
  trans (sym (stripLT o to a t)) (trans p (stripLT o to a t'))

mutual
  total stripLC : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (r : RBCrumbS c h d k o pl pr v) ->
                  lookC o to a (stripC r) = lookCrumb o to a r
  total stripCL : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (m : k) -> (w : v m) -> (c : RBTreeS cc ch k o cb v) ->
                  (p : RBCrumbS pc ph pd k o pl pr v) ->
                  pickCL o to a m w (stripT c) (stripC p) =
                  pickCrumbL o to a m w c p
  total stripCR : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (c : RBTreeS cc ch k o cb v) -> (m : k) -> (w : v m) ->
                  (p : RBCrumbS pc ph pd k o pl pr v) ->
                  pickCR o to a (stripT c) m w (stripC p) =
                  pickCrumbR o to a c m w p

  stripCL {pr} o to a m w c p with (enh o a m)
    | ELT x = stripLC o to a p
    | EEQ x = Refl
    stripCL {pr=Nothing} o to a m w c p | EGT x = stripLT o to a c
    stripCL {pr=Just r} o to a m w c p | EGT x with (enh o a r)
      | ELT y = stripLT o to a c
      | EEQ y = stripLC o to a p
      | EGT y = stripLC o to a p

  stripCR {pl} o to a c m w p with (enh o a m)
    stripCR {pl=Nothing} o to a c m w p | ELT x = stripLT o to a c
    stripCR {pl=Just l} o to a c m w p | ELT x with (enh o a l)
      | ELT y = stripLC o to a p
      | EEQ y = stripLC o to a p
      | EGT y = stripLT o to a c
    | EEQ x = Refl
    | EGT x = stripLC o to a p
  
  stripLC o to a RootS = Refl
  stripLC o to a (RedLS m w r p q) = stripCL o to a m w r p
  stripLC o to a (RedRS l m w p q) = stripCR o to a l m w p
  stripLC o to a (BlkLS m w r p q) = stripCL o to a m w r p
  stripLC o to a (BlkRS l m w p q) = stripCR o to a l m w p

strippyC {o} to a cr cr' p = 
  trans (sym (stripLC o to a cr)) (trans p (stripLC o to a cr'))

total stripLZ : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                lookZ o to a (stripZ z) = lookZip o to a z
total stripLZ' : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                 (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                 lookZ' o to a (stripZ z) = lookZip' o to a z

stripLZ' {pr=Nothing} o to a (MkRBZipS cl pn pf) = stripLT o to a cl
stripLZ' {pr=Just r} o to a (MkRBZipS cl pn pf) with (enh o a r)
  | ELT x = stripLT o to a cl
  | EEQ x = stripLC o to a pn
  | EGT x = stripLC o to a pn

stripLZ {pl=Nothing} o to a z = stripLZ' o to a z
stripLZ {pl=Just l} o to a z with (enh o a l)
  stripLZ o to a (MkRBZipS cl pn pf) | ELT x = stripLC o to a pn
  stripLZ o to a (MkRBZipS cl pn pf) | EEQ x = stripLC o to a pn
  | EGT x = stripLZ' o to a z

strippyZ {o} to a z z' p = 
  trans (sym (stripLZ o to a z)) (trans p (stripLZ o to a z'))

zipUpLook {b=Nothing} o to a t = Refl
zipUpLook {b=Just (l,r)} o to a t = Refl

-- Theorems intertwined with their proofs

mutual
  export
  total lookTmapS : {v' : k -> Type} -> (o : Comp k) ->
                    (to : TotalOrd k o) -> (a : k) ->
                    (f : (b : k) -> v b -> v' b) ->
                    (t : RBTreeS c h k o b v) ->
                    lookTreeS o to a (tmapS f t) =
                    map (f a) (lookTreeS o to a t)
  export
  total pickTmapS : {v' : k -> Type} -> (o : Comp k) ->
                    (to : TotalOrd k o) -> (a : k) ->
                    (f : (b : k) -> v b -> v' b) ->
                    (l : RBTreeS lc lh k o lb v) ->
                    (m : k) -> (w : v m) ->
                    (r : RBTreeS rc rh k o rb v) ->
                    pickTreeS o to a (tmapS f l) m (f m w) (tmapS f r) =
                    map (f a) (pickTreeS o to a l m w r)

  pickTmapS o to a f l m w r with (enh o a m)
    | ELT x = lookTmapS o to a f l
    | EEQ x with (corff to x)
      pickTmapS o to m f l m w r | EEQ x | Refl = Refl
    | EGT x = lookTmapS o to a f r

  lookTmapS o to a f LifS = Refl
  lookTmapS o to a f (RedS l m w r p) = pickTmapS o to a f l m w r
  lookTmapS o to a f (BlkS l m w r p) = pickTmapS o to a f l m w r

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
