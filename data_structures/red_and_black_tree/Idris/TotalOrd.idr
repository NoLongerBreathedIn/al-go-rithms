module TotalOrd

-- Ordering stuff for the RBTree implementation
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import SubSing

public export
total IsLT : Ordering -> Type
IsLT LT = ()
IsLT EQ = Void
IsLT GT = Void
public export
total IsGT : Ordering -> Type
IsGT LT = Void
IsGT EQ = Void
IsGT GT = ()
public export
total IsEQ : Ordering -> Type
IsEQ LT = Void
IsEQ EQ = ()
IsEQ GT = Void
public export
total IsNE : Ordering -> Type
IsNE o = Either (IsLT o) (IsGT o)
public export
total IsLE : Ordering -> Type
IsLE o = Either (IsLT o) (IsEQ o)
public export
total IsGE : Ordering -> Type
IsGE o = Either (IsEQ o) (IsGT o)

public export
total Comp : Type -> Type
Comp a = a -> a -> Ordering

public export
data EOrd : Ordering -> Type where
  LTE : IsLT x -> EOrd x
  EQE : IsEQ x -> EOrd x
  GTE : IsGT x -> EOrd x

export
total enh : (o : Comp a) -> (l : a) -> (r : a) -> EOrd (o l r)
enh o l r with (o l r)
  enh o l r | LT = LTE ()
  enh o l r | EQ = EQE ()
  enh o l r | GT = GTE ()

%default total
public export
record TotalOrd t (to : Comp t) where
  constructor MkTotOrd
  tran : {a : t} -> {b : t} -> {c : t} ->
         IsLT (to a b) -> IsLT (to b c) -> IsLT (to a c)
  refl : (a : t) -> IsEQ (to a a)
  corf : {a : t} -> {b : t} -> IsEQ (to a b) -> a = b
  asym : (a : t) -> (b : t) -> IsLT (to a b) = IsGT (to b a)
%default partial

export
total eqS : TotalOrd t o -> (a : t) -> (b : t) -> a = b -> IsEQ (o b a)
eqS to a a Refl = refl to a

export
total corfE : TotalOrd t o -> (a : t) -> (b : t) -> IsEQ (o a b) -> a = b
corfE to _ _ p = corf to p

export
total corff : {a : t} -> {b : t} -> TotalOrd t o -> IsEQ (o a b) -> b = a
corff to p = sym (corf to p)

export
total corffE : TotalOrd t o -> (a : t) -> (b : t) -> IsEQ (o a b) -> b = a
corffE to _ _ p = corff to p


export
total flipEQ : TotalOrd t o -> IsEQ (o a b) -> IsEQ (o b a)
flipEQ {a} {b} to ab = eqS to a b (corf to ab)

export
total flipLT : TotalOrd t o -> IsLT (o a b) -> IsGT (o b a)
flipLT {a} {b} to ab = rewrite sym (asym to a b) in ab

export
total flipGT : TotalOrd t o -> IsGT (o a b) -> IsLT (o b a)
flipGT {a} {b} to ab = rewrite asym to b a in ab

export
total flipGE : TotalOrd t o -> IsGE (o a b) -> IsLE (o b a)
flipGE to = either (Right . flipEQ to) (Left . flipGT to)

export
total flipLE : TotalOrd t o -> IsLE (o a b) -> IsGE (o b a)
flipLE to = either (Right . flipLT to) (Left . flipEQ to)

export
total flipNE : TotalOrd t o -> IsNE (o a b) -> IsNE (o b a)
flipNE to = either (Right . flipLT to) (Left . flipGT to)

export
total tranLQ : TotalOrd t o -> IsLT (o a b) -> IsLE (o b c) -> IsLT (o a c)
tranLQ {b} {c} to ab (Right bc) = rewrite corffE to b c bc in ab
tranLQ to ab (Left bc) = tran to ab bc

export
total tranQL : TotalOrd t o -> IsLE (o a b) -> IsLT (o b c) -> IsLT (o a c)
tranQL {a} {b} to (Right ab) bc = rewrite corfE to a b ab in bc
tranQL to (Left ab) bc = tran to ab bc

export
total tranLE : TotalOrd t o -> IsLE (o a b) -> IsLE (o b c) -> IsLE (o a c)
tranLE to (Left ab) bc = Left (tranLQ to ab bc)
tranLE {a} {b} to (Right ab) bc = rewrite corfE to a b ab in bc

export
total tranGG : TotalOrd t o -> IsGT (o a b) -> IsGT (o b c) -> IsGT (o a c)
tranGG to ab bc = flipLT to (tran to (flipGT to bc) (flipGT to ab))

export
total tranGQ : TotalOrd t o -> IsGT (o a b) -> IsGE (o b c) -> IsGT (o a c)
tranGQ {b} {c} to ab (Left bc) = rewrite corffE to b c bc in ab
tranGQ to ab (Right bc) = tranGG to ab bc

export
total tranQG : TotalOrd t o -> IsGE (o a b) -> IsGT (o b c) -> IsGT (o a c)
tranQG {a} {b} to (Left ab) bc = rewrite corfE to a b ab in bc
tranQG to (Right ab) bc = tranGG to ab bc

export
total tranGE : TotalOrd t o -> IsGE (o a b) -> IsGE (o b c) -> IsGE (o a c)
tranGE {a} {b} to (Left ab) bc = rewrite corfE to a b ab in bc
tranGE to (Right ab) bc = Right (tranGQ to ab bc)

export
total incompLE : (x : Ordering) -> IsLT x -> IsEQ x -> Void
incompLE LT = const id
incompLE EQ = const
incompLE GT = const
export
total incompLG : (x : Ordering) -> IsLT x -> IsGT x -> Void
incompLG LT = const id
incompLG EQ = const
incompLG GT = const
export
total incompEG : (x : Ordering) -> IsEQ x -> IsGT x -> Void
incompEG LT = const
incompEG EQ = const id
incompEG GT = const

export
total ssIsLT : (o : Ordering) -> SubSing (IsLT o)
ssIsLT LT = ssUnit
ssIsLT EQ = ssVoid
ssIsLT GT = ssVoid

export
total ssIsEQ : (o : Ordering) -> SubSing (IsEQ o)
ssIsEQ LT = ssVoid
ssIsEQ EQ = ssUnit
ssIsEQ GT = ssVoid

export
total ssIsGT : (o : Ordering) -> SubSing (IsGT o)
ssIsGT LT = ssVoid
ssIsGT EQ = ssVoid
ssIsGT GT = ssUnit

export
total ssIsNE : (o : Ordering) -> SubSing (IsNE o)
ssIsNE o = ssEither (ssIsLT o) (ssIsGT o) (incompLG o)

export
total ssIsLE : (o : Ordering) -> SubSing (IsLE o)
ssIsLE o = ssEither (ssIsLT o) (ssIsEQ o) (incompLE o)

export
total ssIsGE : (o : Ordering) -> SubSing (IsGE o)
ssIsGE o = ssEither (ssIsEQ o) (ssIsGT o) (incompEG o)
