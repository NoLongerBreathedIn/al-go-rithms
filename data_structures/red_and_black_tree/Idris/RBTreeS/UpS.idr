module RBTreeS.UpS -- 'S' due to idris bug #3539

-- A slow implementation of RBTrees (slow because it carries proofs)
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import TotalOrd
import SubSing
import BST

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
rwBlkS {o} {lb} {m} {rb} {p} {p'} j k with (ssIsGood o lb m rb p p')
  rwBlkS Refl Refl | Refl = Refl

public export
total trB : RBTreeS c n k o b v -> Bnds k
trB {b} t = b

public export
total stripT : RBTreeS c h k o b v -> BST k o b v
stripT LifS = Leaf
stripT (RedS l m w r p) = Node (stripT l) m w (stripT r) p
stripT (BlkS l m w r p) = Node (stripT l) m w (stripT r) p

public export
record RBMapS k (v : k -> Type) where
  constructor MkRBMapS
  to : Comp k
  depth : Nat
  bounds : Bnds k
  pf : TotalOrd k to
  contents : RBTreeS False depth k to bounds v

public export
total rbMapOrder : RBMapS k v -> Comp k
rbMapOrder = to

public export
total emptyS : (o : Comp k) -> TotalOrd k o -> RBMapS k v
emptyS o p = MkRBMapS o Z Nothing p LifS

{-BEG_LOOK
public export
total lookupS : (a : k) -> RBMapS k v -> Maybe (v a)
END_LOOK-}

{-
public export
total insertS : (a : k) -> v a -> RBMapS k v -> RBMapS k v

public export
total removeS : k -> RBMapS k v -> RBMapS k v
-}

{-BEG_MAP
public export
total mapmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
                RBMapS k v -> RBMapS k v'
END_MAP-}

-- Theorems

{-BEG_THM
{-BEG_LOOK
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

{-BEG_MAP
export
total lookupMapS : {v' : k -> Type} -> (a : k) ->
                   (f : (b : k) -> v b -> v' b) -> (m : RBMapS k v) ->
                   lookupS a (mapmapS f m) = map (f a) (lookupS a m)
END_LOOK-}

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
END_MAP-}

{-
export
total removeEmptyS : (a : k) -> (o : Comp k) -> (t : TotalOrd k o) ->
                     removeS a (emptyS o t) = emptyS o t
-}
END_THM-}

-- Implementation

{-BEG_LOOK
mutual
  public export
  total lookTreeS : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                    RBTreeS c h k o b v -> Maybe (v a)
  public export
  total pickTreeS : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                    RBTreeS lc lh k o lb v -> (m : k) -> v m ->
                    RBTreeS rc rh k o rb v ->
                    Maybe (v a)

{-BEG_DIMP
  pickTreeS o to a l m w r with (enh o a m)
    | LTE x = lookTreeS o to a l
    | EQE x = Just (replace (corff to x) w)
    | GTE x = lookTreeS o to a r

  lookTreeS o to a LifS = Nothing
  lookTreeS o to a (RedS l m w r p) = pickTreeS o to a l m w r
  lookTreeS o to a (BlkS l m w r p) = pickTreeS o to a l m w r
END_DIMP-}
lookupS a (MkRBMapS o d b to t) = lookTreeS o to a t

mutual
  export
  total stripLT : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (t : RBTreeS c h k o b v) ->
                  lookT o to a (stripT t) = lookTreeS o to a t
  export
  total stripPT : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (l : RBTreeS lc lh k o lb v) -> (m : k) -> (w : v m) ->
                  (r : RBTreeS rc rh k o rb v) ->
                  pickT o to a (stripT l) m w (stripT r) =
                  pickTreeS o to a l m w r

{-BEG_DIMP
{-BEG_STRIP
  stripPT o to a l m w r with (enh o a m)
    | LTE x = stripLT o to a l
    | EQE x = Refl
    | GTE x = stripLT o to a r
  
  stripLT o to a LifS = Refl
  stripLT o to a (RedS l m w r p) = stripPT o to a l m w r
  stripLT o to a (BlkS l m w r p) = stripPT o to a l m w r
END_STRIP-}
END_DIMP-}
END_LOOK-}

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

{-BEG_LOOK
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

{-BEG_DIMP
  pickCrumbL {pr} o to a m w c p with (enh o a m)
    | LTE x = lookCrumb o to a p
    | EQE x = Just (replace (corff to x) w)
    pickCrumbL {pr=Nothing} o to a m w c p | GTE x = lookTreeS o to a c
    pickCrumbL {pr=Just r} o to a m w c p | GTE x with (enh o a r)
      | LTE y = lookTreeS o to a c
      | EQE y = lookCrumb o to a p
      | GTE y = lookCrumb o to a p

  pickCrumbR {pl} o to a c m w p with (enh o a m)
    pickCrumbR {pl=Nothing} o to a c m w p | LTE x = lookTreeS o to a c
    pickCrumbR {pl=Just l} o to a c m w p | LTE x with (enh o a l)
      | LTE y = lookCrumb o to a p
      | EQE y = lookCrumb o to a p
      | GTE y = lookTreeS o to a c
    | EQE x = (Just (replace (corff to x) w))
    | GTE x = lookCrumb o to a p

  lookCrumb o to a RootS = Nothing
  lookCrumb o to a (RedLS m w r c p) = pickCrumbL o to a m w r c
  lookCrumb o to a (RedRS l m w c p) = pickCrumbR o to a l m w c
  lookCrumb o to a (BlkLS m w r c p) = pickCrumbL o to a m w r c
  lookCrumb o to a (BlkRS l m w c p) = pickCrumbR o to a l m w c
END_DIMP-}

mutual
  export
  total stripLC : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (r : RBCrumbS c h d k o pl pr v) ->
                  lookC o to a (stripC r) = lookCrumb o to a r
  export
  total stripCL : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (m : k) -> (w : v m) -> (c : RBTreeS cc ch k o cb v) ->
                  (p : RBCrumbS pc ph pd k o pl pr v) ->
                  pickCL o to a m w (stripT c) (stripC p) =
                  pickCrumbL o to a m w c p
  export
  total stripCR : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (c : RBTreeS cc ch k o cb v) -> (m : k) -> (w : v m) ->
                  (p : RBCrumbS pc ph pd k o pl pr v) ->
                  pickCR o to a (stripT c) m w (stripC p) =
                  pickCrumbR o to a c m w p

{-BEG_DIMP
{-BEG_STRIP
  stripCL {pr} o to a m w c p with (enh o a m)
    | LTE x = stripLC o to a p
    | EQE x = Refl
    stripCL {pr=Nothing} o to a m w c p | GTE x = stripLT o to a c
    stripCL {pr=Just r} o to a m w c p | GTE x with (enh o a r)
      | LTE y = stripLT o to a c
      | EQE y = stripLC o to a p
      | GTE y = stripLC o to a p

  stripCR {pl} o to a c m w p with (enh o a m)
    stripCR {pl=Nothing} o to a c m w p | LTE x = stripLT o to a c
    stripCR {pl=Just l} o to a c m w p | LTE x with (enh o a l)
      | LTE y = stripLC o to a p
      | EQE y = stripLC o to a p
      | GTE y = stripLT o to a c
    | EQE x = Refl
    | GTE x = stripLC o to a p
  
  stripLC o to a RootS = Refl
  stripLC o to a (RedLS m w r p q) = stripCL o to a m w r p
  stripLC o to a (RedRS l m w p q) = stripCR o to a l m w p
  stripLC o to a (BlkLS m w r p q) = stripCL o to a m w r p
  stripLC o to a (BlkRS l m w p q) = stripCR o to a l m w p
END_STRIP-}
END_DIMP-}
END_LOOK-}

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

{-BEG_LOOK
public export
total lookZip : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                RBZipS cc pc ch ph pd k o cb pl pr v -> Maybe (v a)
public export
total lookZip' : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                 RBZipS cc pc ch ph pd k o cb pl pr v -> Maybe (v a)

export
total zipUpLook : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (t : RBTreeS c h k o b v) ->
                  lookZip o to a (zipUpS t) = lookTreeS o to a t

{-BEG_DIMP
lookZip' {pr=Nothing} o to a z = lookTreeS o to a (child z)
lookZip' {pr=Just r} o to a z with (enh o a r)
  | LTE x = lookTreeS o to a (child z)
  | EQE x = lookCrumb o to a (parnt z)
  | GTE x = lookCrumb o to a (parnt z)

lookZip {pl=Nothing} o to a z = lookZip' o to a z
lookZip {pl=Just l} o to a z with (enh o a l)
  | LTE x = lookCrumb o to a (parnt z)
  | EQE x = lookCrumb o to a (parnt z)
  | GTE x = lookZip' o to a z

zipUpLook {b=Nothing} o to a t = Refl
zipUpLook {b=Just (l,r)} o to a t = Refl
END_DIMP-}

export
total stripLZ : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                lookZ o to a (stripZ z) = lookZip o to a z
export
total stripLZ' : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                 (z : RBZipS cc pc ch ph pd k o cb pl pr v) ->
                 lookZ' o to a (stripZ z) = lookZip' o to a z

{-BEG_DIMP
{-BEG_STRIP
stripLZ' {pr=Nothing} o to a (MkRBZipS cl pn pf) = stripLT o to a cl
stripLZ' {pr=Just r} o to a (MkRBZipS cl pn pf) with (enh o a r)
  | LTE x = stripLT o to a cl
  | EQE x = stripLC o to a pn
  | GTE x = stripLC o to a pn

stripLZ {pl=Nothing} o to a z = stripLZ' o to a z
stripLZ {pl=Just l} o to a z with (enh o a l)
  stripLZ o to a (MkRBZipS cl pn pf) | LTE x = stripLC o to a pn
  stripLZ o to a (MkRBZipS cl pn pf) | EQE x = stripLC o to a pn
  | GTE x = stripLZ' o to a z
END_STRIP-}
END_DIMP-}

export
total strippyZ : {o : Comp k} -> (to : TotalOrd k o) -> (a : k) ->
                 {z : RBZipS cc pc ch ph pd k o cb pl pr v} ->
                 {z' : RBZipS cc' pc' ch' ph' pd' k o cb' pl' pr' v} ->
                 lookZ o to a (stripZ z) = lookZ o to a (stripZ z') ->
                 lookZip o to a z = lookZip o to a z'
strippyZ {o} to a {z} {z'} p = 
  trans (sym (stripLZ o to a z)) (trans p (stripLZ o to a z'))
END_LOOK-}

export
total pfOrdered : TotalOrd k o -> RBTreeS c h k o b v -> OrderedBounds o b

pfOrdered _ LifS = ()
pfOrdered to (RedS lc _ _ rc pf) =
  pfOrdered' to (pfOrdered to lc) (pfOrdered to rc) pf
pfOrdered to (BlkS lc _ _ rc pf) =
  pfOrdered' to (pfOrdered to lc) (pfOrdered to rc) pf

{-BEG_MAP
public export
total tmapS : {v : k -> Type} -> ((a : k) -> v a -> v' a) ->
              RBTreeS c h k o b v -> RBTreeS c h k o b v'
tmapS f LifS = LifS
tmapS f (RedS l m mv r pf) = RedS (tmapS f l) m (f m mv) (tmapS f r) pf
tmapS f (BlkS l m mv r pf) = BlkS (tmapS f l) m (f m mv) (tmapS f r) pf

mapmapS f (MkRBMapS to depth bounds pf contents) =
  MkRBMapS to depth bounds pf (tmapS f contents)

public export
total cmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
              RBCrumbS c h d k o pl pr v -> RBCrumbS c h d k o pl pr v'
cmapS f RootS = RootS
cmapS f (RedLS m w r p q) = RedLS m (f m w) (tmapS f r) (cmapS f p) q
cmapS f (RedRS l m w p q) = RedRS (tmapS f l) m (f m w) (cmapS f p) q
cmapS f (BlkLS m w r p q) = BlkLS m (f m w) (tmapS f r) (cmapS f p) q
cmapS f (BlkRS l m w p q) = BlkRS (tmapS f l) m (f m w) (cmapS f p) q

public export
total zmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
             RBZipS cc pc ch ph pd k o cb pl pr v ->
             RBZipS cc pc ch ph pd k o cb pl pr v'
zmapS f (MkRBZipS t c q) = MkRBZipS (tmapS f t) (cmapS f c) q
END_MAP-}

{-BEG_ZD-}
public export
record ZipDownS (cc : Bool) (pc : Bool) (h : Nat) (d : Nat)
                k (o : Comp k) (cb : Bnds k) (pl : Maybe k) (pr : Maybe k)
                (v : k -> Type) where
  constructor MkZipDownS
  zipDS : RBZipS cc pc h h d k o cb pl pr v
  canDS : (Either (IsTrue cc) (IsPos h), Either (IsFalse cc) (IsFalse pc))

{-BEG_MAP
public export
total zdmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipDownS cc pc h d k o cb pl pr v ->
               ZipDownS cc pc h d k o cb pl pr v'
zdmapS f (MkZipDownS z c) = MkZipDownS (zmapS f z) c
END_MAP-}

public export
total treeMk : RBTreeS c h k o b v -> Either (IsTrue c) (IsPos h) -> k
treeMk (RedS _ m _ _ _) = const m
treeMk (BlkS _ m _ _ _) = const m
treeMk LifS = either void void

public export
total zipMk : ZipDownS cc pc h d k o cb pl pr v -> k
zipMk x = treeMk (child (zipDS x)) (fst (canDS x))

public export
total sipLc : ZipDownS cc pc h d k o cb pl pr v -> Bool
public export
total zipLb : ZipDownS cc pc h d k o cb pl pr v -> Bnds k
public export
total sipRc : ZipDownS cc pc h d k o cb pl pr v -> Bool
public export
total zipRb : ZipDownS cc pc h d k o cb pl pr v -> Bnds k

public export
total sreeLc : RBTreeS c h k o b v -> Bool
public export
total treeLb : RBTreeS c h k o b v -> Bnds k
public export
total sreeRc : RBTreeS c h k o b v -> Bool
public export
total treeRb : RBTreeS c h k o b v -> Bnds k

sreeLc LifS = False
sreeLc (RedS x m y z w) = False
sreeLc (BlkS {lc} x m y z w) = lc
treeLb LifS = Nothing
treeLb (RedS {lb} x m y z w) = lb
treeLb (BlkS {lb} x m y z w) = lb
sreeRc LifS = False
sreeRc (RedS x m y z w) = False
sreeRc (BlkS {rc} x m y z w) = rc
treeRb LifS = Nothing
treeRb (RedS {rb} x m y z w) = rb
treeRb (BlkS {rb} x m y z w) = rb

sipLc x = sreeLc (child (zipDS x))
zipLb x = treeLb (child (zipDS x))
sipRc x = sreeRc (child (zipDS x))
zipRb x = treeRb (child (zipDS x))

public export
total goLeftS : TotalOrd k o -> (z : ZipDownS tc pc h d k o tb pl pr v) ->
                RBZipS (sipLc z) tc (predH tc h (fst (canDS z)))
                                    (predH tc h (fst (canDS z))) (succHD tc d)
                                    k o (zipLb z) pl (Just (zipMk z)) v
public export
total goRightS : TotalOrd k o -> (z : ZipDownS tc pc h d k o tb pl pr v) ->
                 RBZipS (sipRc z) tc (predH tc h (fst (canDS z)))
                                     (predH tc h (fst (canDS z))) (succHD tc d)
                                     k o (zipRb z) (Just (zipMk z)) pr v

export
total goLeftGoodS : (z : ZipDownS tc pc h d k o tb pl pr v) ->
                    Either (IsFalse (sipLc z)) (IsFalse tc)
export
total goRightGoodS : (z : ZipDownS tc pc h d k o tb pl pr v) ->
                     Either (IsFalse (sipLc z)) (IsFalse tc)

goLeftGoodS (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
goLeftGoodS (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) = Left ()
goLeftGoodS (MkZipDownS (MkRBZipS (BlkS l m w r g) p q) j) = Right ()
goRightGoodS (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
goRightGoodS (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) = Left ()
goRightGoodS (MkZipDownS (MkRBZipS (BlkS l m w r g) p q) j) = Right ()


{-BEG_MAP
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
END_MAP-}

{-BEG_LOOK
export
total lookLeft : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                 (z : ZipDownS cc pc h d k o cb pl pr v) ->
                 lookZip o to a (goLeftS to z) = lookZip o to a (zipDS z)
export
total lookRight : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                  (z : ZipDownS cc pc h d k o cb pl pr v) ->
                  lookZip o to a (goRightS to z) = lookZip o to a (zipDS z)
END_LOOK-}

{-BEG_DIMP
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

{-BEG_PF
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
END_PF-}

{-BEG_MAP
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
END_MAP-}

{-BEG_LOOK
lookLeft o to a (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
lookLeft {pc=True} o to a
  (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) = either void void (snd j)
lookLeft {pc=False} {pl} {pr} o to a
  (MkZipDownS (MkRBZipS (RedS {lb} {rb} l m w r g) p q) j) = sym (strippyZ to a
    {z=MkRBZipS (RedS l m w r g) p q}
    {z'=MkRBZipS l
      (RedLS m w r p (glPfC to pl lb m rb pr q g
                            (pfOrdered to l) (pfOrdered to r)))
      (glPfZ to pl lb m rb pr q g)} moveLeft)
lookLeft {pl} {pr} o to a
  (MkZipDownS (MkRBZipS (BlkS {lb} {rb} l m w r g) p q) j) = sym (strippyZ to a
    {z=MkRBZipS (BlkS l m w r g) p q}
    {z'=MkRBZipS l
      (BlkLS m w r p (glPfC to pl lb m rb pr q g
                            (pfOrdered to l) (pfOrdered to r)))
      (glPfZ to pl lb m rb pr q g)} moveLeft)

lookRight o to a (MkZipDownS (MkRBZipS LifS p q) j) = either void void (fst j)
lookRight {pc=True} o to a
  (MkZipDownS (MkRBZipS (RedS l m w r g) p q) j) = either void void (snd j)
lookRight {pc=False} {pl} {pr} o to a
  (MkZipDownS (MkRBZipS (RedS {lb} {rb} l m w r g) p q) j) = sym (strippyZ to a
    {z=MkRBZipS (RedS l m w r g) p q}
    {z'=MkRBZipS r
      (RedRS l m w p (grPfC to pl lb m rb pr q g
                            (pfOrdered to l) (pfOrdered to r)))
      (grPfZ to pl lb m rb pr q g)} moveRight)
lookRight {pl} {pr} o to a
  (MkZipDownS (MkRBZipS (BlkS {lb} {rb} l m w r g) p q) j) = sym (strippyZ to a
    {z=MkRBZipS (BlkS l m w r g) p q}
    {z'=MkRBZipS r
      (BlkRS l m w p (grPfC to pl lb m rb pr q g
                            (pfOrdered to l) (pfOrdered to r)))
      (grPfZ to pl lb m rb pr q g)} moveRight)

END_LOOK-}
END_DIMP-}
{-END_ZD-}

{-BEG_ZU
public export
record ZipUpS (cc : Bool) (pc : Bool) (h : Nat) (d : Nat)
              k (o : Comp k) (cb : Bnds k) (pl : Maybe k) (pr : Maybe k)
              (v : k -> Type) where
  constructor MkZipUpS
  zipUS : RBZipS cc pc h h (S d) k o cb pl pr v
  canUS : Either (IsFalse cc) (IsFalse pc)

{-BEG_MAP
public export
total zumapS : {v' : k -> Type} -> (f : (a : k) -> v a -> v' a) ->
               ZipUpS cc pc h d k o cb pl pr v ->
               ZipUpS cc pc h d k o cb pl pr v'
zumapS f (MkZipUpS z c) = MkZipUpS (zmapS f z) c
END_MAP-}

public export
total zipPb : ZipUpS cc pc h d k o cb pl pr v -> Bnds k
public export
total zipPl : ZipUpS cc pc h d k o cb pl pr v -> Maybe k
public export
total zipPr : ZipUpS cc pc h d k o cb pl pr v -> Maybe k
public export
total sipPc : ZipUpS cc tc h d k o cb pl pr v -> Bool

zipPb {cb} z with (parnt (zipUS z))
  zipPb {cb} z | (RedLS {rb} m w r c p) = boundStuff cb m rb
  zipPb {cb} z | (RedRS {lb} l m w c p) = boundStuff lb m cb
  zipPb {cb} z | (BlkLS {rb} m w r c p) = boundStuff cb m rb
  zipPb {cb} z | (BlkRS {lb} l m w c p) = boundStuff lb m cb
zipPl = crPl . parnt . zipUS
zipPr = crPr . parnt . zipUS
sipPc = crPc . parnt . zipUS

public export
total goUpS : TotalOrd k o -> (z : ZipUpS cc tc h d k o cb pl pr v) ->
              RBZipS tc (sipPc z) (succHD tc h) (succHD tc h)
                     (succHD (not tc) d) k o (zipPb z) (zipPl z) (zipPr z) v

export
total goUpGoodS : (z : ZipUpS cc tc h d k o cb pl pr v) ->
                  Either (IsFalse tc) (IsFalse (sipPc z))

goUpGoodS (MkZipUpS (MkRBZipS c (RedLS m w r p g) q) j) = Right ()
goUpGoodS (MkZipUpS (MkRBZipS c (RedRS l m w p g) q) j) = Right ()
goUpGoodS (MkZipUpS (MkRBZipS c (BlkLS m w r p g) q) j) = Left ()
goUpGoodS (MkZipUpS (MkRBZipS c (BlkRS l m w p g) q) j) = Left ()

{-BEG_MAP
export
total mapUpS : {v' : k -> Type} -> (to : TotalOrd k o) ->
               (f : (a : k) -> v a -> v' a) ->
               (z : ZipUpS cc tc h d k o cb pl pr v) ->
               goUpS to (zumapS f z) = zmapS f (goUpS to z)
END_MAP-}

{-BEG_LOOK
export
total lookUp : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
               (z : ZipUpS cc pc h d k o cb pl pr v) ->
               lookZip o to a (goUpS to z) = lookZip o to a (zipUS z)
END_LOOK-}

{-BEG_DIMP
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

{-BEG_PF
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
END_PF-}

{-BEG_MAP
mapUpS {cc=True} to f (MkZipUpS (MkRBZipS t (RedLS m w r p g) q) j) =
  either void void j
mapUpS {cc=False} to f (MkZipUpS (MkRBZipS t (RedLS m w r p g) q) j) = Refl
mapUpS {cc=True} to f (MkZipUpS (MkRBZipS t (RedRS l m w p g) q) j) =
  either void void j
mapUpS {cc=False} to f (MkZipUpS (MkRBZipS t (RedRS l m w p g) q) j) = Refl
mapUpS to f (MkZipUpS (MkRBZipS t (BlkLS m w r p g) q) j) = Refl
mapUpS to f (MkZipUpS (MkRBZipS t (BlkRS l m w p g) q) j) = Refl
END_MAP-}

lookUp {cc=True} o to a (MkZipUpS (MkRBZipS t (RedLS m w r p g) q) j) =
  either void void j
lookUp {cc=True} o to a (MkZipUpS (MkRBZipS t (RedRS l m w p g) q) j) =
  either void void j
lookUp {cc=False} {cb} o to a
  (MkZipUpS (MkRBZipS t (RedLS {pl} {pr} {rb} m w r p g) q) j) = strippyZ to a
    {z=MkRBZipS (RedS t m w r (guPLT to pl cb m q, fst g)) p
                (guPLZ to pl cb m rb pr q g)}
    {z'=MkRBZipS t (RedLS m w r p g) q} moveLeft
lookUp {cc=False} {cb} o to a
  (MkZipUpS (MkRBZipS t (RedRS {pl} {pr} {lb} l m w p g) q) j) = strippyZ to a
    {z=MkRBZipS (RedS l m w t (fst g, guPRT to m cb pr q)) p
                (guPRZ to pl lb m cb pr q g)}
    {z'=MkRBZipS t (RedRS l m w p g) q} moveRight
lookUp {cb} o to a
  (MkZipUpS (MkRBZipS t (BlkLS {pl} {pr} {rb} m w r p g) q) j) = strippyZ to a
    {z=MkRBZipS (BlkS t m w r (guPLT to pl cb m q, fst g)) p
                (guPLZ to pl cb m rb pr q g)}
    {z'=MkRBZipS t (BlkLS m w r p g) q} moveLeft
lookUp {cb} o to a
  (MkZipUpS (MkRBZipS t (BlkRS {pl} {pr} {lb} l m w p g) q) j) = strippyZ to a
    {z=MkRBZipS (BlkS l m w t (fst g, guPRT to m cb pr q)) p
                (guPRZ to pl lb m cb pr q g)}
    {z'=MkRBZipS t (BlkRS l m w p g) q} moveRight
END_DIMP-}
END_ZU-}

{-BEG_SEARCH-}
public export
total IsGoodZipS : Comp k -> k -> Maybe k -> Maybe k -> Type
IsGoodZipS o a pl pr = (IsGoodZipL o a pl, IsGoodZipR o a pr)

public export
total ssIsGoodZipS : (o : Comp k) -> (a : k) -> (pl : Maybe k) ->
                    (pr : Maybe k) -> SubSing (IsGoodZipS o a pl pr)
ssIsGoodZipS o a pl pr = ssPair (ssIsGoodZipL o a pl) (ssIsGoodZipR o a pr)

public export
record ZipSearchS (cc : Bool) (pc : Bool) (h : Nat) (d : Nat) k (o : Comp k)
                  (cb : Bnds k) (pl : Maybe k) (pr : Maybe k) (v : k -> Type)
                  (a : k) where
  constructor MkZipSearchS
  zipSS : RBZipS cc pc h h d k o cb pl pr v
  canSS : Either (IsFalse cc) (IsFalse pc)
  prpSS : IsGoodZipS o a pl pr

public export
total zipUpSearchS : RBTreeS False h k o b v ->
                     ZipSearchS False True h Z k o b Nothing Nothing v a
zipUpSearchS t = MkZipSearchS (zipUpS t) (Left ()) ((), ())

{-BEG_MAP
public export
total zsmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipSearchS cc pc h d k o cb pl pr v a ->
               ZipSearchS cc pc h d k o cb pl pr v' a
zsmapS f (MkZipSearchS z c p) = MkZipSearchS (zmapS z) c p
END_MAP-}

{-BEG_ZD-}
public export
total IsGoodZipF : Comp k -> k -> Maybe k -> Type
IsGoodZipF o a = maybe () (IsEQ . o a)

public export
total ssIsGoodZipF : (o : Comp k) -> (a : k) -> (m : Maybe k) ->
                     SubSing (IsGoodZipF o a m)
ssIsGoodZipF o a = ssMebbe ssUnit (\m => ssIsEQ (o a m))

public export
record ZipFoundS k (o : Comp k) (v : k -> Type) (a : k) where
  constructor MkZipFoundS
  ccFS, pcFS : Bool
  hFS, dFS : Nat
  cbFS : Bnds k
  plFS, prFS : Maybe k
  zipFS : ZipSearchS ccFS pcFS hFS dFS k o cbFS plFS prFS v a
  prpSS : IsGoodZipF o a (sreeK (child (zipSS zipFS)))

{-BEG_MAP
public export
total zfmapS : {v' : k -> Type} -> ((a : k) -> v a -> v' a) ->
               ZipFoundS k o v a -> ZipFoundS k o v' a
zfmapS f (MkZipFoundS z p) = MkZipFoundS (zsmapS f z) p
END_MAP-}

public export
total searchS : TotalOrd k o -> (a : k) ->
                ZipSearchS cc pc h d k o cb pl pr v a -> ZipFoundS k o v a

{-BEG_MAP
export
total mapSearchS : {v' : k -> Type} -> (to : TotalOrd k o) ->
                   (f : (a : k) -> v a -> v' a) ->
                   (z : ZipSearchS cc pc h d k o cb pl pr v a) ->
                   searchS to a (zsmapS f z) = zfmapS f (searchS to a z)
END_MAP-}

{-BEG_LOOK
export
total lookSearch : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
                   (z : ZipSearchS cc pc h d k o cb pl pr v a) ->
                   lookZip o to a (zipSS (zipFS (searchS to a z))) =
                   lookZip o to a (zipSS z)
END_LOOK-}

{-BEG_IMP-}
mutual
  public export
  total searchST : (pc : Bool) -> (h : Nat) -> (d : Nat) ->
                   (cb : Bnds k) -> (pl : Maybe k) -> (pr : Maybe k) ->
                   TotalOrd k o -> (a : k) ->
                   ZipSearchS True pc h d k o cb pl pr v a -> ZipFoundS k o v a
  public export
  total searchSF : (pc : Bool) -> (h : Nat) -> (d : Nat) -> (cb : Bnds k) ->
                   (pl : Maybe k) -> (pr : Maybe k) -> TotalOrd k o ->
                   (a : k) -> ZipSearchS False pc h d k o cb pl pr v a ->
                   ZipFoundS k o v a
  public export
  total searchSI : TotalOrd k o -> (a : k) ->
                   ZipSearchS cc pc h d k o cb pl pr v a -> ZipFoundS k o v a
  public export
  total searchSJ : TotalOrd k o -> (a : k) ->
                   ZipSearchS False pc h d k o cb pl pr v a ->
                   ZipFoundS k o v a
  
  searchSF pc Z d Nothing pl pr to a
    (MkZipSearchS (MkRBZipS LifS c g) j q) = 
      MkZipFoundS False pc Z d Nothing pl pr 
                  (MkZipSearchS (MkRBZipS LifS c g) j q) ()
  searchSF {o} pc (S h) d (boundStuff lb m rb) pl pr to a (MkZipSearchS (MkRBZipS (BlkS l m w r g) c p) j q) with (enh o a m)
    | LTE x = searchSI to a (MkZipSearchS (goLeftS to (MkZipDownS (MkRBZipS (BlkS l m w r g) c p) (Right (), j))) (Right ()) (fst q, x))
    | EQE x = MkZipFoundS False pc (S h) d (boundStuff lb m rb) pl pr
                          (MkZipSearchS (MkRBZipS (BlkS l m w r g) c p) j q) x
    | GTE x = searchSI to a (MkZipSearchS (goRightS to (MkZipDownS (MkRBZipS (BlkS l m w r g) c p) (Right (), j))) (Right ()) (x, snd q))

  searchST {o} pc h d (boundStuff lb m rb) pl pr to a (MkZipSearchS (MkRBZipS (RedS l m w r g) c p) j q) with (enh o a m)
    | LTE x = searchSJ to a (MkZipSearchS (goLeftS to (MkZipDownS (MkRBZipS (RedS l m w r g) c p) (Left (), j))) (Left ()) (fst q, x))
    | EQE x = MkZipFoundS True pc h d (boundStuff lb m rb) pl pr
                          (MkZipSearchS (MkRBZipS (RedS l m w r g) c p) j q) x
    | GTE x = searchSJ to a (MkZipSearchS (goRightS to (MkZipDownS (MkRBZipS (RedS l m w r g) c p) (Left (), j))) (Left ()) (x, snd q))

  searchSI {cc=True} {pc} {h} {d} {cb} {pl} {pr} to a z =
    searchST pc h d cb pl pr to a z
  searchSI {cc=False} {pc} {h} {d} {cb} {pl} {pr} to a z =
    searchSF pc h d cb pl pr to a z

  searchSJ {pc} {h} {d} {cb} {pl} {pr} to a z =
    searchSF pc h d cb pl pr to a z

--searchS = searchSI

{-BEG_MAP
END_MAP-}

{-BEG_LOOK
END_LOOK-}
{-END_IMP-}
{-END_ZD-}
{-END_SEARCH-}

{-
insertS a w m = ?insertS_rhs
removeS a m = ?removeS_rhs
-}

{-BEG_THM
{-BEG_PF
{-BEG_LOOK
{-
lookupInsertDiff a b w m pf = ?lid
lookupInsertSame a w m = ?lis
lookupRemoveDiff a b m pf = ?lrd
lookupRemoveSame a m = ?lrs
-}

lookupEmptyS a o t = Refl

{-BEG_MAP
mutual
  total lookTmapS : {v' : k -> Type} -> (o : Comp k) ->
                    (to : TotalOrd k o) -> (a : k) ->
                    (f : (b : k) -> v b -> v' b) ->
                    (t : RBTreeS c h k o b v) ->
                    lookTreeS o to a (tmapS f t) =
                    map (f a) (lookTreeS o to a t)
  total pickTmapS : {v' : k -> Type} -> (o : Comp k) ->
                    (to : TotalOrd k o) -> (a : k) ->
                    (f : (b : k) -> v b -> v' b) ->
                    (l : RBTreeS lc lh k o lb v) ->
                    (m : k) -> (w : v m) ->
                    (r : RBTreeS rc rh k o rb v) ->
                    pickTreeS o to a (tmapS f l) m (f m w) (tmapS f r) =
                    map (f a) (pickTreeS o to a l m w r)

  pickTmapS o to a f l m w r with (enh o a m)
    | LTE x = lookTmapS o to a f l
    | EQE x with (corff to x)
      pickTmapS o to m f l m w r | EQE x | Refl = Refl
    | GTE x = lookTmapS o to a f r

  lookTmapS o to a f LifS = Refl
  lookTmapS o to a f (RedS l m w r p) = pickTmapS o to a f l m w r
  lookTmapS o to a f (BlkS l m w r p) = pickTmapS o to a f l m w r

lookupMapS a f (MkRBMapS o d b to t) = lookTmapS o to a f t
END_LOOK-}

total tmapIdS : (t : RBTreeS c h k o b v) -> tmapS (\q => id {a=v q}) t = t
tmapIdS LifS = Refl
tmapIdS (RedS l m w r p) = rwRedS (tmapIdS l) (tmapIdS r)
tmapIdS (BlkS l m w r p) = rwBlkS (tmapIdS l) (tmapIdS r)

mapmapIdS (MkRBMapS o d b to t) = cong (tmapIdS t)

total tmapCompS : {v' : k -> Type} -> {w : k -> Type} ->
                  (t : RBTreeS c h k o b v) ->
                  (f : (a : k) -> v a -> v' a) ->
                  (g : (a : k) -> v' a -> w a) ->
                  tmapS g (tmapS f t) = tmapS (\a => g a . f a) t
tmapCompS LifS f g = Refl
tmapCompS (RedS l m w r p) f g = rwRedS (tmapCompS l f g) (tmapCompS r f g)
tmapCompS (BlkS l m w r p) f g = rwBlkS (tmapCompS l f g) (tmapCompS r f g)

mapmapCompS (MkRBMapS o d b to t) f g = cong (tmapCompS t f g)

{-
insertMapS a m f = ?insMap
removeMapS a m f = ?remMap
-}

emptyMapS o p f = Refl
END_MAP-}

{-
removeEmptyS a o t = ?remEmp
-}
END_PF-}
END_THM-}

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
