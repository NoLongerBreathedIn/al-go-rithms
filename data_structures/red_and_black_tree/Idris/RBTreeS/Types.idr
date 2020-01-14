module RBTreeS.Types

-- Some utility functions for red-black trees.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import SubSing

%default total
%access public export

IsTrue : Bool -> Type
IsTrue True = ()
IsTrue False = Void

IsFalse : Bool -> Type
IsFalse True = Void
IsFalse False = ()

IsZero : Nat -> Type
IsZero Z = ()
IsZero (S _) = Void

IsPos : Nat -> Type
IsPos Z = Void
IsPos (S _) = ()

IsNothing : Maybe a -> Type
IsNothing Nothing = ()
IsNothing (Just _) = Void

IsFull : Maybe a -> Type
IsFull Nothing = Void
IsFull (Just _) = ()

IsRight : Either l r -> Type
IsRight (Left _) = Void
IsRight (Right _) = ()

IsLeft : Either l r -> Type
IsLeft (Left _) = ()
IsLeft (Right _) = Void

ssIsNothing : {x : Maybe a} -> SubSing (IsNothing x)
ssIsFull : {x : Maybe a} -> SubSing (IsFull x)
ssIsLeft : {x : Either l r} -> SubSing (IsLeft x)
ssIsRight : {x : Either l r} -> SubSing (IsRight x)
ssIsZero : {x : Nat} -> SubSing (IsZero x)
ssIsPos : {x : Nat} -> SubSing (IsPos x)
ssIsFalse : {x : Bool} -> SubSing (IsFalse x)
ssIsTrue : {x : Bool} -> SubSing (IsTrue x)

ssIsNothing {x=Nothing} = ssUnit
ssIsNothing {x=Just x} = ssVoid
ssIsFull {x=Nothing} = ssVoid
ssIsFull {x=Just x} = ssUnit
ssIsLeft {x=Left l} = ssUnit
ssIsLeft {x=Right r} = ssVoid
ssIsRight {x=Left l} = ssVoid
ssIsRight {x=Right r} = ssUnit
ssIsZero {x=Z} = ssUnit
ssIsZero {x=S k} = ssVoid
ssIsPos {x=Z} = ssVoid
ssIsPos {x=S k} = ssUnit
ssIsFalse {x=False} = ssUnit
ssIsFalse {x=True} = ssVoid
ssIsTrue {x=False} = ssVoid
ssIsTrue {x=True} = ssUnit

predH : (b : Bool) -> (n : Nat) -> Nat
predH True x = x
predH False Z = Z
predH False (S k) = k

succHD : Bool -> Nat -> Nat
succHD True = id
succHD False = S

enhE : (z : Either l r) -> Either (IsLeft z) (IsRight z)
enhE (Left _) = Left ()
enhE (Right _) = Right ()

enhM : (z : Maybe a) -> Either (IsNothing z) (IsFull z)
enhM Nothing = Left ()
enhM (Just _) = Right ()

fromJust : {ma : Maybe a} -> IsFull ma -> a
fromJust {ma=Nothing} x = void x
fromJust {ma=Just x} () = x

fromLeft : {eth : Either l r} -> IsLeft eth -> l
fromLeft {eth=Left ll} = const ll
fromLeft {eth=Right rr} = void

fromRight : {eth : Either l r} -> IsRight eth -> r
fromRight {eth=Left ll} = void
fromRight {eth=Right rr} = const rr

fromSucc : {nn : Nat} -> IsPos nn -> Nat
fromSucc {nn=Z} x = void x
fromSucc {nn=S n} () = n

mebbeNothing : IsNothing ma -> maybe ifn ifj ma = ifn
mebbeNothing {ma=Nothing} = const Refl
mebbeNothing {ma=Just _} = void

mebbeJust : (x : IsFull ma) -> maybe ifn ifj ma = ifj (fromJust x)
mebbeJust {ma=Nothing} x = void x
mebbeJust {ma=Just x} () = Refl

eitherLeft : (x : IsLeft eth) -> either ifl ifr eth = ifl (fromLeft x)
eitherLeft {eth=Left ll} () = Refl
eitherLeft {eth=Right rr} x = void x

eitherRight : (x : IsRight eth) -> either ifl ifr eth = ifr (fromRight x)
eitherRight {eth=Left ll} x = void x
eitherRight {eth=Right rr} () = Refl

icpMaybe : {x : Maybe a} -> IsNothing x -> IsFull x -> b
icpEither : {x : Either l r} -> IsLeft x -> IsRight x -> b
icpNat : {x : Nat} -> IsPos x -> IsZero x -> b

icpMaybe {x=Nothing} = const void
icpMaybe {x=Just _} = void
icpEither {x=Left _} = const void
icpEither {x=Right _} = void
icpNat {x=Z} = void
icpNat {x=S _} = const void

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
