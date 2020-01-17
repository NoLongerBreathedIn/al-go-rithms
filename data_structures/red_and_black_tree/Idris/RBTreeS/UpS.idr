module RBTreeS.UpS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- This file contains functions related to moving up.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import public RBTreeS.StructsS
import RBTreeS.FmapS
import RBTreeS.LookS
import BST.MoveB
import public RBTreeS.Types

public export
record ZipUpS (cc : Bool) (pc : Bool) (h : Nat) (d : Nat)
              k (o : Comp k) (cb : Bnds k) (pl : Maybe k) (pr : Maybe k)
              (v : k -> Type) where
  constructor MkZipUpS
  zipUS : RBZipS cc pc h h (S d) k o cb pl pr v
  canUS : Either (IsFalse cc) (IsFalse pc)

public export
total zumapS : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
               ZipUpS cc pc h d k o cb pl pr v ->
               ZipUpS cc pc h d k o cb pl pr v'
zumapS f (MkZipUpS z c) = MkZipUpS (zmapS f z) c

public export
total goUpS : TotalOrd k o -> (z : ZipUpS cc tc h d k o cb pl pr v) ->
              RBZipS tc (sipPc (zipUS z)) (succHD tc h) (succHD tc h)
                     (succHD (not tc) d) k o (zipPb (zipUS z))
                                             (zipPl (zipUS z))
                                             (zipPr (zipUS z)) v

-- Theorems

export
total mapUpS : {v' : k -> Type} -> (to : TotalOrd k o) ->
               (f : (a : k) -> v a -> v' a) ->
               (z : ZipUpS cc tc h d k o cb pl pr v) ->
               goUpS to (zumapS f z) = zmapS f (goUpS to z)

export
total lookUp : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
               (z : ZipUpS cc pc h d k o cb pl pr v) ->
               lookZip o to a (goUpS to z) = lookZip o to a (zipUS z)

-- Implementation

export
total guPLT : TotalOrd k o -> (l : Maybe k) -> (lb : Bnds k) -> (m : k) ->
              IsGoodZip o l (Just m) lb -> IsGoodL o m lb
export
total guPRT : TotalOrd k o -> (m : k) -> (rb : Bnds k) -> (r : Maybe k) ->
              IsGoodZip o (Just m) r rb -> IsGoodR o m rb
export
total guPLZ : TotalOrd k o -> (l : Maybe k) -> (lb : Bnds k) -> (m : k) ->
              (rb : Bnds k) -> (r : Maybe k) -> IsGoodZip o l (Just m) lb ->
              IsGoodCrumbL o m rb l r -> IsGoodZip o l r (boundStuff lb m rb)
export
total guPRZ : TotalOrd k o -> (l : Maybe k) -> (lb : Bnds k) -> (m : k) ->
              (rb : Bnds k) -> (r : Maybe k) -> IsGoodZip o (Just m) r rb ->
              IsGoodCrumbR o m lb l r -> IsGoodZip o l r (boundStuff lb m rb)

goUpS {cc} {cb} to z with (child (zipUS z))
  | c with (cmpat (zipUS z))
    | q with (parnt (zipUS z))
      goUpS {cc=True} to z | c | q | RedLS m w s p g =
        either void void (canUS z)
      goUpS {cc=True} to z | c | q | RedRS s m w p g =
        either void void (canUS z)
      goUpS {cc=False} {cb} to z | c | q | RedLS {pl} {pr} {rb} m w s p g =
        MkRBZipS (RedS c m w s (guPLT to pl cb m q, fst g)) p
                 (guPLZ to pl cb m rb pr q g)
      goUpS {cc=False} {cb} to z | c | q | RedRS {pl} {pr} {lb} s m w p g =
        MkRBZipS (RedS s m w c (fst g, guPRT to m cb pr q)) p
                 (guPRZ to pl lb m cb pr q g)
      | BlkLS {pl} {pr} {rb} m w s p g =
        MkRBZipS (BlkS c m w s (guPLT to pl cb m q, fst g)) p
                 (guPLZ to pl cb m rb pr q g)
      | BlkRS {pl} {pr} {lb} s m w p g =
        MkRBZipS (BlkS s m w c (fst g, guPRT to m cb pr q)) p
                 (guPRZ to pl lb m cb pr q g)

-- Proofs of internal functions

total guPLZ0 : TotalOrd k o -> (l : Maybe k) -> (m : k) -> (rb : Bnds k) ->
               maybe () (EnsureR o m rb) l -> IsGoodZipL o m l
total guPLZ1 : TotalOrd k o -> (l : Maybe k) -> (m : k) -> (rb : Bnds k) ->
               (r : Maybe k) -> maybe () (EnsureL o m rb) r ->
               IsGoodZipR o (boundStuffR m rb) r
total guPRZ0 : TotalOrd k o -> (lb : Bnds k) -> (m : k) -> (r : Maybe k) ->
               maybe () (EnsureL o m lb) r -> IsGoodZipR o m r
total guPRZ1 : TotalOrd k o -> (l : Maybe k) -> (lb : Bnds k) -> (m : k) ->
               (r : Maybe k) -> maybe () (EnsureR o m lb) l ->
               IsGoodZipL o (boundStuffL m lb) l

guPLZ0 to Nothing m rb e = ()
guPLZ0 to (Just l) m rb e = flipLT to (fst e)
guPLZ1 to l m rb Nothing c = ()
guPLZ1 to l m Nothing (Just r) c = fst c
guPLZ1 to l m (Just rb) (Just r) c = flipGT to (snd c)
guPRZ0 to lb m Nothing e = ()
guPRZ0 to lb m (Just r) e = fst e
guPRZ1 to Nothing lb m r c = ()
guPRZ1 to (Just l) Nothing m r c = flipLT to (fst c)
guPRZ1 to (Just l) (Just lb) m r c = flipLT to (snd c)

guPLT to l Nothing m z = ()
guPLT to l (Just (ll, lr)) m z = flipLT to (snd z)
guPRT to m Nothing r z = ()
guPRT to m (Just (rl, rr)) r z = flipGT to (fst z)
guPLZ to l Nothing m rb r z c = (guPLZ0 to l m rb (fst (snd c)), 
                                 guPLZ1 to l m rb r (snd (snd c)))
guPLZ to l (Just lb) m rb r z c = (fst z, guPLZ1 to l m rb r (snd (snd c)))
guPRZ to l lb m Nothing r z c = (guPRZ1 to l lb m r (fst (snd c)),
                                 guPRZ0 to lb m r (snd (snd c)))
guPRZ to l lb m (Just rb) r z c = (guPRZ1 to l lb m r (fst (snd c)), snd z)

-- Proofs

mapUpS {cc=True} to f (MkZipUpS (MkRBZipS t (RedLS m w r p g) q) j) =
  either void void j
mapUpS {cc=False} to f (MkZipUpS (MkRBZipS t (RedLS m w r p g) q) j) = Refl
mapUpS {cc=True} to f (MkZipUpS (MkRBZipS t (RedRS l m w p g) q) j) =
  either void void j
mapUpS {cc=False} to f (MkZipUpS (MkRBZipS t (RedRS l m w p g) q) j) = Refl
mapUpS to f (MkZipUpS (MkRBZipS t (BlkLS m w r p g) q) j) = Refl
mapUpS to f (MkZipUpS (MkRBZipS t (BlkRS l m w p g) q) j) = Refl


lookUp {cc=True} o to a (MkZipUpS (MkRBZipS t (RedLS m w r p g) q) j) =
  either void void j
lookUp {cc=True} o to a (MkZipUpS (MkRBZipS t (RedRS l m w p g) q) j) =
  either void void j
lookUp {cc=False} {cb} o to a
  (MkZipUpS (MkRBZipS t (RedLS {pl} {pr} {rb} m w r p g) q) j) = strippyZ to a
    (MkRBZipS (RedS t m w r (guPLT to pl cb m q, fst g)) p
              (guPLZ to pl cb m rb pr q g))
    (MkRBZipS t (RedLS m w r p g) q) moveLeft
lookUp {cc=False} {cb} o to a
  (MkZipUpS (MkRBZipS t (RedRS {pl} {pr} {lb} l m w p g) q) j) = strippyZ to a
    (MkRBZipS (RedS l m w t (fst g, guPRT to m cb pr q)) p
              (guPRZ to pl lb m cb pr q g))
    (MkRBZipS t (RedRS l m w p g) q) moveRight
lookUp {cb} o to a
  (MkZipUpS (MkRBZipS t (BlkLS {pl} {pr} {rb} m w r p g) q) j) = strippyZ to a
    (MkRBZipS (BlkS t m w r (guPLT to pl cb m q, fst g)) p
              (guPLZ to pl cb m rb pr q g))
    (MkRBZipS t (BlkLS m w r p g) q) moveLeft
lookUp {cb} o to a
  (MkZipUpS (MkRBZipS t (BlkRS {pl} {pr} {lb} l m w p g) q) j) = strippyZ to a
    (MkRBZipS (BlkS l m w t (fst g, guPRT to m cb pr q)) p
              (guPRZ to pl lb m cb pr q g))
    (MkRBZipS t (BlkRS l m w p g) q) moveRight

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
