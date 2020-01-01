module BST.StructsB -- 'B' due to idris bug #3539

-- Binary search trees for the RBTree implementation (useful in proofs)
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

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

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
