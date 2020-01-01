module TotalOrdDO

-- Useful implementation of TotalOrd
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import Decidable.Equality
-- requires contrib
import Decidable.Order

import TotalOrd

data OrdTy : (t : Type) -> (to : t -> t -> Type) -> t -> t -> Type where
  TyEq : a = b -> OrdTy t to a b
  TyLt : (a = b -> Void) -> to a b -> OrdTy t to a b
  TyGt : (a = b -> Void) -> to b a -> OrdTy t to a b

total cOrd : (Ordered t to, DecEq t) => (a : t) -> (b : t) -> OrdTy t to a b
cOrd {to} a b with (decEq a b)
  | (Yes pf) = TyEq pf
  | (No c) with (order {to} a b)
    | (Left l) = TyLt c l
    | (Right r) = TyGt c r

export
total cmpOrd : (Ordered t to, DecEq t) => Comp t
cmpOrd {to} a b with (cOrd {to} a b)
  | TyEq prf = EQ
  | TyLt f x = LT
  | TyGt f x = GT

export
total exEQ : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             IsEQ (cmpOrd {to} a b) -> a = b
exEQ {to} a b ab with (cOrd {to} a b)
  | TyEq prf = prf
  | TyLt f x = void ab
  | TyGt f x = void ab

export
total exLT : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             IsLT (cmpOrd {to} a b) -> (a = b -> Void, to a b)
exLT {to} a b ab with (cOrd {to} a b)
  | TyEq prf = void ab
  | TyLt f x = (f, x)
  | TyGt f x = void ab

export
total exGT : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             IsGT (cmpOrd {to} a b) -> (a = b -> Void, to b a)
exGT {to} a b ab with (cOrd {to} a b)
  | TyEq prf = void ab
  | TyLt f x = void ab
  | TyGt f x = (f, x)

export
total exGE : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             IsGE (cmpOrd {to} a b) -> to b a
exGE {to} a b (Left ab) with (exEQ {to} a b ab)
  exGE {to} b b (Left bb) | Refl = reflexive {po=to} b
exGE a b (Right ab) = snd (exGT a b ab)

export
total exNE : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             IsNE (cmpOrd {to} a b) -> a = b -> Void
exNE {to} a b ab = either (fst . exLT {to} a b) (fst . exGT {to} a b) ab

export
total exLE : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             IsLE (cmpOrd {to} a b) -> to a b
exLE a b (Left ab) = snd (exLT a b ab)
exLE {to} a b (Right ab) with (exEQ {to} a b ab)
  exLE {to} b b (Right bb) | Refl = reflexive {po=to} b

export
total inEQ : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             a = b -> IsEQ (cmpOrd {to} a b)
inEQ {to} a b prf with (cOrd {to} a b)
  | TyEq x = ()
  | TyLt f x = f prf
  | TyGt f x = f prf

export
total inLT : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             (a = b -> Void) -> to a b -> IsLT (cmpOrd {to} a b)
inLT {to} a b f x with (cOrd {to} a b)
  | TyEq prf = f prf
  | TyLt g y = ()
  | TyGt g y = f (antisymmetric a b x y)

export
total inGT : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             (a = b -> Void) -> to b a -> IsGT (cmpOrd {to} a b)
inGT {to} a b f x with (cOrd {to} a b)
  | TyEq prf = f prf
  | TyLt g y = f (antisymmetric a b y x)
  | TyGt g y = ()

export
total inGE : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             to b a -> IsGE (cmpOrd {to} a b)
inGE {to} a b ab with (cOrd {to} a b)
  | TyEq prf = Left ()
  | TyLt f x = void (f (antisymmetric a b x ab))
  | TyGt f x = Right ()

export
total inNE : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             (a = b -> Void) -> IsNE (cmpOrd {to} a b)
inNE {to} a b ab with (cOrd {to} a b)
  | TyEq prf = void (ab prf)
  | TyLt f x = Left ()
  | TyGt f x = Right ()

export
total inLE : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
             to a b -> IsLE (cmpOrd {to} a b)
inLE {to} a b ab with (cOrd {to} a b)
  | TyEq prf = Right ()
  | TyLt f x = Left ()
  | TyGt f x = void (f (antisymmetric a b ab x))

total tranCmpOrd : (Ordered t to, DecEq t) => IsLT (cmpOrd {t} {to} a b) ->
                   IsLT (cmpOrd {t} {to} b c) -> IsLT (cmpOrd {t} {to} a c)

total tranCmpOrd' : (Ordered t to) => (a : t) -> (b : t) -> (c : t) ->
                    to a b -> to b c -> a = c -> a = b
tranCmpOrd' a b c x y prf = antisymmetric a b x (rewrite prf in y)

tranCmpOrd {a} {b} {c} {to} ab bc with (exLT {to} a b ab)
  | (f, x) with (exLT {to} b c bc)
    | (g, y) = inLT a c (f . tranCmpOrd' {to} a b c x y) (transitive a b c x y)

total reflCmpOrd : (Ordered t to, DecEq t) => (a : t) -> IsEQ (cmpOrd {to} a a)
reflCmpOrd {to} a = inEQ {to} a a Refl

total corfCmpOrd : (Ordered t to, DecEq t) =>
                   IsEQ (cmpOrd {t} {to} a b) -> a = b
corfCmpOrd {t} {to} {a} {b} x = exEQ {to} a b x

total asymCmpOrd : (Ordered t to, DecEq t) => (a : t) -> (b : t) ->
                   IsLT (cmpOrd {to} a b) = IsGT (cmpOrd {to} b a)
asymCmpOrd {to} a b with (cOrd {to} a b)
  | (TyEq prf) with (cOrd {to} b a)
    | (TyEq x) = Refl
    | (TyLt f x) = Refl
    | (TyGt f x) = void (f (sym prf))
  | (TyLt f x) with (cOrd {to} b a)
    | (TyEq prf) = void (f (sym prf))
    | (TyLt g y) = void (f (antisymmetric a b x y))
    | (TyGt g y) = Refl
  | (TyGt f x) with (cOrd {to} b a)
    | (TyEq prf) = Refl
    | (TyLt g y) = Refl
    | (TyGt g y) = void (f (antisymmetric a b y x))

export
total cmpOrdTot : (Ordered t to, DecEq t) => TotalOrd t (cmpOrd {to})
cmpOrdTot {to} = MkTotOrd (tranCmpOrd {to})
                          (reflCmpOrd {to})
                          (corfCmpOrd {to})
                          (asymCmpOrd {to})

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:

