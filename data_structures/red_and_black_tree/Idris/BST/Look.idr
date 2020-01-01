module BST

-- Binary search trees for the RBTree implementation (useful in proofs)
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019 CC-BY

import SubSing
import TotalOrd

public export
total Bnds : Type -> Type
Bnds k = Maybe (k, k)

public export
total IsGood : Comp a -> Bnds a -> a -> Bnds a -> Type

public export
total boundStuff : Bnds a -> a -> Bnds a -> Bnds a

public export
total IsGoodL : Comp a -> a -> Bnds a -> Type
public export
total IsGoodR : Comp a -> a -> Bnds a -> Type
IsGoodL c m = maybe () (IsGT . c m . snd)
IsGoodR c m = maybe () (IsLT . c m . fst)

IsGood c l m r = (IsGoodL c m l, IsGoodR c m r)

export
total ssIsGoodL : (o : Comp t) -> (m : t) -> (b : Bnds t) ->
                  SubSing (IsGoodL o m b)
export
total ssIsGoodR : (o : Comp t) -> (m : t) -> (b : Bnds t) ->
                  SubSing (IsGoodR o m b)
export
total ssIsGood : (o : Comp t) -> (l : Bnds t) -> (m : t) -> (r : Bnds t) ->
                 SubSing (IsGood o l m r)

ssIsGoodL o m Nothing = ssUnit
ssIsGoodL o m (Just (ll, lr)) = ssIsGT (o m lr)
ssIsGoodR o m Nothing = ssUnit
ssIsGoodR o m (Just (rl, rr)) = ssIsLT (o m rl)
ssIsGood o l m r = ssPair (ssIsGoodL o m l) (ssIsGoodR o m r)

public export
total boundStuffL : a -> Bnds a -> a
public export
total boundStuffR : a -> Bnds a -> a
boundStuffL a = maybe a fst
boundStuffR a = maybe a snd

boundStuff l m r = Just (boundStuffL m l, boundStuffR m r)

public export
data BST : (k : Type) -> Comp k -> Bnds k -> (k -> Type) -> Type where
  Leaf : BST k o Nothing v
  Node : BST k o lb v -> (m : k) -> v m -> BST k o rb v ->
         IsGood o lb m rb -> BST k o (boundStuff lb m rb) v

-- Useful stuff

mutual
  public export
  total lookT : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                BST k o b v -> Maybe (v a)
  public export
  total pickT : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                BST k o lb v -> (m : k) -> v m -> BST k o rb v ->
                Maybe (v a)

{-BEG_DIMP-}
  pickT o to a l m w r with (enh o a m)
    | LTE x = lookT o to a l
    | EQE x = Just (replace (corff to x) w)
    | GTE x = lookT o to a r

  lookT o to a Leaf = Nothing
  lookT o to a (Node l m w r p) = pickT o to a l m w r
{-END_DIMP-}

public export
total IsGoodCrumbR : Comp a -> a -> Bnds a -> Maybe a -> Maybe a -> Type
public export
total IsGoodCrumbL : Comp a -> a -> Bnds a -> Maybe a -> Maybe a -> Type

public export
total EnsureR : Comp a -> a -> Bnds a -> a -> Type
public export
total EnsureL : Comp a -> a -> Bnds a -> a -> Type
public export
total IsGoodCrumb : Comp a -> a -> Bnds a -> Maybe a -> Maybe a -> Type

EnsureR c m b l = (IsLT (c l m),
                   IsGoodR c l b)
EnsureL c m b r = (IsLT (c m r),
                   IsGoodL c r b)
IsGoodCrumb c m b pl pr = (maybe () (EnsureR c m b) pl,
                           maybe () (EnsureL c m b) pr)
IsGoodCrumbR c m lb pl pr = (IsGoodL c m lb,
                             IsGoodCrumb c m lb pl pr)
IsGoodCrumbL c m rb pl pr = (IsGoodR c m rb,
                             IsGoodCrumb c m rb pl pr)

export
total ssIsGoodCrumbR : (c : Comp t) -> (m : t) -> (b : Bnds t) ->
                       (l : Maybe t) -> (r : Maybe t) ->
                       SubSing (IsGoodCrumbR c m b l r)
export
total ssIsGoodCrumbL : (c : Comp t) -> (m : t) -> (b : Bnds t) ->
                       (l : Maybe t) -> (r : Maybe t) ->
                       SubSing (IsGoodCrumbL c m b l r)
export
total ssIsGoodCrumb : (c : Comp t) -> (m : t) -> (b : Bnds t) ->
                      (l : Maybe t) -> (r : Maybe t) ->
                      SubSing (IsGoodCrumb c m b l r)
export
total ssEnsureR : (c : Comp t) -> (m : t) -> (b : Bnds t) -> (l : t) ->
                  SubSing (EnsureR c m b l)
export
total ssEnsureL : (c : Comp t) -> (m : t) -> (b : Bnds t) -> (r : t) ->
                  SubSing (EnsureL c m b r)

ssEnsureR c m b l = ssPair (ssIsLT (c l m)) (ssIsGoodR c l b)
ssEnsureL c m b r = ssPair (ssIsLT (c m r)) (ssIsGoodL c r b)

ssIsGoodCrumb c m b l r = ssPair (ssMebbe ssUnit (ssEnsureR c m b) l)
                                 (ssMebbe ssUnit (ssEnsureL c m b) r)
ssIsGoodCrumbL c m b l r = ssPair (ssIsGoodR c m b) (ssIsGoodCrumb c m b l r)
ssIsGoodCrumbR c m b l r = ssPair (ssIsGoodL c m b) (ssIsGoodCrumb c m b l r)

public export
data BSC : (k : Type) -> Comp k -> Maybe k -> Maybe k ->
           (k -> Type) -> Type where
  Rut : BSC k o Nothing Nothing v
  Lft : (m : k) -> v m -> BST k o rb v -> BSC k o pl pr v ->
        IsGoodCrumbL o m rb pl pr -> BSC k o pl (Just m) v
  Rgt : BST k o lb v -> (m : k) -> v m -> BSC k o pl pr v ->
        IsGoodCrumbR o m lb pl pr -> BSC k o (Just m) pr v

mutual
  public export
  total lookC : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                BSC k o pl pr v -> Maybe (v a)
  public export
  total pickCL : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                 (m : k) -> v m -> BST k o cb v ->
                 BSC k o pl pr v -> Maybe (v a)
  public export
  total pickCR : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                 BST k o cb v -> (m : k) -> v m ->
                 BSC k o pl pr v -> Maybe (v a)

{-BEG_DIMP-}
  pickCL {pr} o to a m w c p with (enh o a m)
    | LTE x = lookC o to a p
    | EQE x = Just (replace (corff to x) w)
    pickCL {pr=Nothing} o to a m w c p | GTE x = lookT o to a c
    pickCL {pr=Just r} o to a m w c p | GTE x with (enh o a r)
      | LTE y = lookT o to a c
      | EQE y = lookC o to a p
      | GTE y = lookC o to a p

  pickCR {pl} o to a c m w p with (enh o a m)
    pickCR {pl=Nothing} o to a c m w p | LTE x = lookT o to a c
    pickCR {pl=Just l} o to a c m w p | LTE x with (enh o a l)
      | LTE y = lookC o to a p
      | EQE y = lookC o to a p
      | GTE y = lookT o to a c
    | EQE x = (Just (replace (corff to x) w))
    | GTE x = lookC o to a p

  lookC o to a Rut = Nothing
  lookC o to a (Lft m w r c p) = pickCL o to a m w r c
  lookC o to a (Rgt l m w c p) = pickCR o to a l m w c
{-END_DIMP-}

public export
total IsGoodZipL : Comp k -> k -> Maybe k -> Type
public export
total IsGoodZipR : Comp k -> k -> Maybe k -> Type

IsGoodZipL o r = maybe () (IsGT . o r)
IsGoodZipR o l = maybe () (IsLT . o l)

public export
total IsGoodZip : Comp k -> Maybe k -> Maybe k -> Bnds k -> Type
IsGoodZip o l r =
  maybe () (\b => (IsGoodZipL o (fst b) l, IsGoodZipR o (snd b) r))

export
total ssIsGoodZipL : (o : Comp k) -> (bl : k) -> (l : Maybe k) ->
                     SubSing (IsGoodZipL o bl l)
export
total ssIsGoodZipR : (o : Comp k) -> (bl : k) -> (l : Maybe k) ->
                     SubSing (IsGoodZipR o bl l)
export
total ssIsGoodZip : (o : Comp k) -> (l : Maybe k) -> (r : Maybe k) ->
                    (b : Bnds k) -> SubSing (IsGoodZip o l r b)

ssIsGoodZipL o bl = ssMebbe ssUnit (\l => ssIsGT (o bl l))
ssIsGoodZipR o br = ssMebbe ssUnit (\r => ssIsLT (o br r))
ssIsGoodZip o l r = ssMebbe ssUnit (\b => ssPair (ssIsGoodZipL o (fst b) l)
                                                 (ssIsGoodZipR o (snd b) r))

public export
record BSZ (k : Type) (o : Comp k) (cb : Bnds k)
           (pl : Maybe k) (pr : Maybe k) (v : k -> Type) where
  constructor MkBSZ
  cld : BST k o cb v
  pnt : BSC k o pl pr v
  cpt : IsGoodZip o pl pr cb

public export
total lookZ : (o : Comp k) -> TotalOrd k o -> (a : k) ->
              BSZ k o cb pl pr v -> Maybe (v a)
public export
total lookZ' : (o : Comp k) -> TotalOrd k o -> (a : k) ->
               BSZ k o cb pl pr v -> Maybe (v a)

{-BEG_DIMP-}
lookZ' {pr=Nothing} o to a z = lookT o to a (cld z)
lookZ' {pr=Just r} o to a z with (enh o a r)
  | LTE x = lookT o to a (cld z)
  | EQE x = lookC o to a (pnt z)
  | GTE x = lookC o to a (pnt z)

lookZ {pl=Nothing} o to a z = lookZ' o to a z
lookZ {pl=Just l} o to a z with (enh o a l)
  | LTE x = lookC o to a (pnt z)
  | EQE x = lookC o to a (pnt z)
  | GTE x = lookZ' o to a z
{-END_DIMP-}

public export
total OrderedBounds : Comp k -> Bnds k -> Type
OrderedBounds o = maybe () (IsLE . uncurry o)

export
total ssOrderedBounds : (o : Comp k) -> (b : Bnds k) ->
                        SubSing (OrderedBounds o b)
ssOrderedBounds o = ssMebbe ssUnit (\b => ssIsLE (uncurry o b))

public export
total pfOrdered' : TotalOrd k o -> OrderedBounds o lb ->
                   OrderedBounds o rb -> IsGood o lb m rb ->
                   OrderedBounds o (boundStuff lb m rb)

pfOrdered' {lb = Nothing} {rb = Nothing} {m} to _ _ _ = Right (refl to m)
pfOrdered' {lb = Nothing} {rb = Just (rl, rr)} {m} to _ ro (_, pr) =
  Left (tranLQ to pr ro)
pfOrdered' {lb = Just (ll, lr)} {rb = Nothing} {m} to lo _ (pl, _) =
  Left (tranQL to lo (flipGT to pl))
pfOrdered' {lb = Just (ll, lr)} {rb = Just (rl, rr)} {m} to lo ro (pl, pr) =
  Left (tran to (tranQL to lo (flipGT to pl)) (tranLQ to pr ro))

public export
total pfOrderedBST : TotalOrd k o -> BST k o b v -> OrderedBounds o b
pfOrderedBST _ Leaf = ()
pfOrderedBST to (Node lt _ _ rt pf) =
  pfOrdered' to (pfOrderedBST to lt) (pfOrderedBST to rt) pf

total iLG : IsLT o -> IsGT o -> a
iLG {o} l g = void (incompLG o l g)
total iLE : IsLT o -> IsEQ o -> a
iLE {o} l e = void (incompLE o l e)
total iEG : IsEQ o -> IsGT o -> a
iEG {o} e g = void (incompEG o e g)

total iQG : IsLE o -> IsGT o -> a
iQG {o} {a} = either (iLG {o} {a}) (iEG {o} {a})

total iLQ : IsLT o -> IsGE o -> a
iLQ {o} l = either (iLE {o} l) (iLG {o} l)

total mL : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
           (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
           (p : BSC k o pl pr v) -> (g0 : IsGood o lb m rb) ->
           (q0 : IsGoodZip o pl pr (boundStuff lb m rb)) ->
           (g1 : IsGoodCrumbL o m rb pl pr) ->
           (q1 : IsGoodZip o pl (Just m) lb) ->
           lookZ o to a (MkBSZ (Node l m w r g0) p q0) =
           lookZ o to a (MkBSZ l (Lft m w r p g1) q1)

total mL0 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (p : BSC k o pl pr v) -> (g0 : IsGood o lb m rb) ->
            (q0 : IsGoodZip o pl pr (boundStuff lb m rb)) ->
            (g1 : IsGoodCrumbL o m rb pl pr) ->
            (q1 : IsGoodZip o pl (Just m) lb) ->
            lookZ' o to a (MkBSZ (Node l m w r g0) p q0) =
            lookZ' o to a (MkBSZ l (Lft m w r p g1) q1)
total mL1 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (p : BSC k o (Just pl) pr v) -> IsLE (o a pl) ->
            IsGoodCrumbL o m rb (Just pl) pr ->
            lookC o to a p = pickCL o to a m w r p
total mL2 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (p : BSC k o pl (Just pr) v) -> IsGE (o a pr) ->
            (g1 : IsGoodCrumbL o m rb pl (Just pr)) ->
            (q1 : IsGoodZip o pl (Just m) lb) ->
            lookC o to a p = lookZ' o to a (MkBSZ l (Lft m w r p g1) q1)
total mL3 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (p : BSC k o pl pr v) -> maybe () (IsLT . o a) pr ->
            (g1 : IsGoodCrumbL o m rb pl pr) ->
            (q1 : IsGoodZip o pl (Just m) lb) ->
            pickT o to a l m w r = lookZ' o to a (MkBSZ l (Lft m w r p g1) q1)

export
total moveLeft : lookZ o to a (MkBSZ (Node l m w r g0) p q0) =
                 lookZ o to a (MkBSZ l (Lft m w r p g1) q1)
moveLeft {o} {to} {a} {l} {m} {w} {r} {p} {g0} {q0} {g1} {q1} =
  mL o to a l m w r p g0 q0 g1 q1

mL {pl=Nothing} o to a l m w r p g0 q0 g1 q1 = mL0 o to a l m w r p g0 q0 g1 q1
mL {pl=Just pl} o to a l m w r p g0 q0 g1 q1 with (enh o a pl)
  | LTE x = mL1 o to a m w r p (Left x) g1
  | EQE x = mL1 o to a m w r p (Right x) g1
  | GTE x = mL0 o to a l m w r p g0 q0 g1 q1

mL0 {pr=Nothing} o to a l m w r p g0 q0 g1 q1 = mL3 o to a l m w r p () g1 q1
mL0 {pr=Just pr} o to a l m w r p g0 q0 g1 q1 with (enh o a pr)
  | LTE x = mL3 o to a l m w r p x g1 q1
  | EQE x = mL2 o to a l m w r p (Left x) g1 q1
  | GTE x = mL2 o to a l m w r p (Right x) g1 q1

mL1 o to a m w r p g q with (tranQL to g (fst (fst (snd q))))
  | x with (enh o a m)
    | LTE y = Refl
    | EQE y = iLE x y
    | GTE y = iLG x y

mL2 {pr} o to a l m w r p j g1 q1 with (tranQG to j (flipLT to
                                                         (fst (snd (snd g1)))))
  | x with (enh o a m)
    | LTE y = iLG y x
    | EQE y = iEG y x
    | GTE y with (enh o a m)
      | LTE z = iLG z x
      | EQE z = iEG z x
      | GTE z with (enh o a pr)
        | LTE s = iLQ s j
        | EQE s = Refl
        | GTE s = Refl

mL3 {pr} o to a l m w r p j g1 q1 with (enh o a m)
  | LTE x = Refl
  | EQE x with (enh o a m)
    | LTE y = iLE y x
    | EQE y with (ssIsEQ (o a m) x y)
      mL3 o to a l m w r p j g1 q1 | EQE x | EQE x | Refl = Refl
    | GTE y = iEG x y
  | GTE x with (enh o a m)
    | LTE y = iLG y x
    | EQE y = iEG y x
    mL3 {pr=Nothing} o to a l m w r p j g1 q1 | GTE x | GTE y = Refl
    mL3 {pr=Just pr} o to a l m w r p j g1 q1 
      | GTE x | GTE y with (enh o a pr)
        | LTE z = Refl
        | EQE z = iLE j z
        | GTE z = iLG j z

total mR : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
           (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
           (p : BSC k o pl pr v) -> (g0 : IsGood o lb m rb) ->
           (q0 : IsGoodZip o pl pr (boundStuff lb m rb)) ->
           (g1 : IsGoodCrumbR o m lb pl pr) ->
           (q1 : IsGoodZip o (Just m) pr rb) ->
           lookZ o to a (MkBSZ (Node l m w r g0) p q0) =
           lookZ o to a (MkBSZ r (Rgt l m w p g1) q1)
total mR0 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (p : BSC k o pl pr v) -> IsGT (o a m) -> (g0 : IsGood o lb m rb) ->
            (g1 : IsGoodCrumbR o m lb pl pr) ->
            lookZ' o to a (MkBSZ (Node l m w r g0) p q0) =
            lookZ' o to a (MkBSZ r (Rgt l m w p g1) q1)

total mR1 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (p : BSC k o pl pr v) -> IsLT (o a m) ->
            (g1 : IsGoodCrumbR o m lb pl pr) ->
            lookZ' o to a (MkBSZ (Node l m w r g0) p q0) = lookT o to a l

total mR2 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (p : BSC k o pl pr v) -> (x : IsEQ (o a m)) ->
            (g0 : IsGood o lb m rb) ->
            (q0 : IsGoodZip o pl pr (boundStuff lb m rb)) ->
            (g1 : IsGoodCrumbR o m lb pl pr) ->
            lookZ' o to a (MkBSZ (Node l m w r g0) p q0) =
            Just (replace (corff to x) w)
total mR3 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> 
            (r : BST k o rb v) -> IsGood o lb m rb -> IsGT (o a m) ->
            pickT o to a l m w r = lookT o to a r
total mR4 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) ->
            (p : BSC k o pl (Just pr) v) -> IsGoodCrumbR o m lb pl (Just pr) ->
            IsGE (o a pr) -> lookC o to a p = pickCR o to a l m w p
total mR5 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            IsLT (o a m) -> pickT o to a l m w r = lookT o to a l
total mR6 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (x : IsEQ (o a m)) ->
            pickT o to a l m w r = Just (replace (corff to x) w)
total mR7 : (o : Comp k) -> (to : TotalOrd k o) -> (a : k) ->
            (l : BST k o lb v) -> (m : k) -> (w : v m) -> (r : BST k o rb v) ->
            (p : BSC k o (Just pl) pr v) -> IsLE (o a pl) ->
            (g1 : IsGoodCrumbR o m lb (Just pl) pr) ->
            (q1 : IsGoodZip o (Just m) pr rb) ->
            lookC o to a p = lookZ o to a (MkBSZ r (Rgt l m w p g1) q1)

mR {pl=Nothing} o to a l m w r p g0 q0 g1 q1 with (enh o a m)
  | LTE x with (enh o a m)
    | LTE y = mR1 o to a l m w r p x g1
    | EQE y = iLE x y
    | GTE y = iLG x y
  | EQE x with (enh o a m)
    | LTE y = iLE y x
    | EQE y = mR2 o to a l m w r p y g0 q0 g1
    | GTE y = iEG x y
  | GTE x = mR0 o to a l m w r p x g0 g1
mR {pl=Just pl} o to a l m w r p g0 q0 g1 q1 with (enh o a pl)
  | LTE x = mR7 o to a l m w r p (Left x) g1 q1
  | EQE x = mR7 o to a l m w r p (Right x) g1 q1
  | GTE x with (enh o a m)
    | LTE y with (enh o a m)
      | LTE z with (enh o a pl)
        | LTE s = iLG s x
        | EQE s = iEG s x
        | GTE s = mR1 o to a l m w r p y g1
      | EQE z = iLE y z
      | GTE z = iLG y z
    | EQE y with (enh o a m)
      | LTE z = iLE z y
      | EQE z = mR2 o to a l m w r p z g0 q0 g1
      | GTE z = iEG y z
    | GTE y = mR0 o to a l m w r p y g0 g1

mR0 {pr=Nothing} o to a l m w r p j g0 g1 = mR3 o to a l m w r g0 j
mR0 {pr=Just pr} o to a l m w r p j g0 g1 with (enh o a pr)
  | LTE x = mR3 o to a l m w r g0 j
  | EQE x = mR4 o to a l m w p g1 (Left x)
  | GTE x = mR4 o to a l m w p g1 (Right x)

mR1 {pr=Nothing} o to a l m w r p j g1 = mR5 o to a l m w r j
mR1 {pr=Just pr} o to a l m w r p j g1 with (tran to j (fst (snd (snd g1))))
  | x with (enh o a pr)
    | LTE y = mR5 o to a l m w r j
    | EQE y = iLE x y
    | GTE y = iLG x y

mR2 {pr=Nothing} o to a l m w r p j g0 q0 g1 = mR6 o to a l m w r j
mR2 {pr=Just pr} o to a l m w r p j g0 q0 g1 with (tranQL to (Right j)
                                                          (fst (snd (snd g1))))
  | x with (enh o a pr)
    | LTE y = mR6 o to a l m w r j
    | EQE y = iLE x y
    | GTE y = iLG x y

mR3 o to a l m w r g0 j with (enh o a m)
  | LTE x = iLG x j
  | EQE x = iEG x j
  | GTE x = Refl

mR4 o to a l m w p g1 j with (tranQG to j (flipLT to (fst (snd (snd g1)))))
  | x with (enh o a m)
    | LTE y = iLG y x 
    | EQE y = iEG y x
    | GTE y = Refl

mR5 o to a l m w r j with (enh o a m)
  | LTE x = Refl
  | EQE x = iLE j x
  | GTE x = iLG j x

mR6 o to a l m w r j with (enh o a m)
  | LTE x = iLE x j
  | EQE x with (ssIsEQ (o a m) x j)
    mR6 o to a l m w r j | EQE j | Refl = Refl
  | GTE x = iEG j x

mR7 {pl} o to a l m w r p j g1 q1 with (tranQL to j (fst (fst (snd g1))))
  | x with (enh o a m)
    | LTE y with (enh o a m)
      | LTE z with (enh o a pl)
        | LTE s = Refl
        | EQE s = Refl
        | GTE s = iQG j s
      | EQE z = iLE y z
      | GTE z = iLG y z
    | EQE y = iLE x y
    | GTE y = iLG x y

export
total moveRight : lookZ o to a (MkBSZ (Node l m w r g0) p q0) =
                  lookZ o to a (MkBSZ r (Rgt l m w p g1) q1)
moveRight {o} {to} {a} {l} {m} {w} {r} {p} {g0} {q0} {g1} {q1} =
  mR o to a l m w r p g0 q0 g1 q1
