module BST.StructsB -- 'B' due to idris bug #3539

-- Binary search trees for the RBTree implementation (useful in proofs)
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import SubSing
import TotalOrd
import public BST.TypesB

public export
data BST : (k : Type) -> Comp k -> Bnds k -> (k -> Type) -> Type where
  Leaf : BST k o Nothing v
  Node : BST k o lb v -> (m : k) -> v m -> BST k o rb v ->
         IsGood o lb m rb -> BST k o (boundStuff lb m rb) v

public export
data BSC : (k : Type) -> Comp k -> Maybe k -> Maybe k ->
           (k -> Type) -> Type where
  Rut : BSC k o Nothing Nothing v
  Lft : (m : k) -> v m -> BST k o rb v -> BSC k o pl pr v ->
        IsGoodCrumbL o m rb pl pr -> BSC k o pl (Just m) v
  Rgt : BST k o lb v -> (m : k) -> v m -> BSC k o pl pr v ->
        IsGoodCrumbR o m lb pl pr -> BSC k o (Just m) pr v

public export
record BSZ (k : Type) (o : Comp k) (cb : Bnds k)
           (pl : Maybe k) (pr : Maybe k) (v : k -> Type) where
  constructor MkBSZ
  cld : BST k o cb v
  pnt : BSC k o pl pr v
  cpt : IsGoodZip o pl pr cb

export
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

export
total pfOrderedBST : TotalOrd k o -> BST k o b v -> OrderedBounds o b
pfOrderedBST _ Leaf = ()
pfOrderedBST to (Node lt _ _ rt pf) =
  pfOrdered' to (pfOrderedBST to lt) (pfOrderedBST to rt) pf

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
