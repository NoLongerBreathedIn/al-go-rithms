module StepRec

-- Useful stepwise induction and proofs.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import Decidable.Equality
import SubSing

%default total
%access public export

Step : (a : Type) -> Type -> (a -> a -> Type) -> Type
Step a b rel = (x : a) -> Either b (y ** rel y x)

StepProp : Step a b rel -> (a -> Type) -> (b -> Type) -> Type
StepProp {a} f p q = (x : a) -> p x -> either q (p . fst) (f x)

StepPropEq : (c : Type) -> Step a b rel -> (a -> c) -> (b -> c) -> Type
StepPropEq {a} c st f g = (x : a) -> either g (f . fst) (st x) = f x

PropStep : (a : Type) -> (a -> Type) -> (a -> a -> Type) -> Type
PropStep a p rel = (x : a) -> Either (p x) (y ** (rel y x, p y -> p x))

on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)

firstDP : {P : b -> Type} -> (f : a -> b) -> (x : a ** P (f x)) ->
          (x : b ** P x)
firstDP f (x ** pfx) = (f x ** pfx)

CommStep : (rel : a' -> a' -> Type) ->
           (af : a -> a') -> (b -> b') -> Step a' b' rel ->
           Step a b (rel `on` af) -> Type
CommStep {a} rel af bf sl sr =
  (x : a) -> sl (af x) = either (Left . bf) (Right . firstDP af) (sr x)

curryDP : {v : k -> Type} -> ((l : k) -> v l -> x) -> (ll ** v ll) -> x
curryDP f (l ** r) = f l r

accStepRec : Step a b rel -> (z : a) -> Accessible rel z -> b

twistStep : Step a b rel -> (x : a) -> ((y : a) -> rel y x -> b) -> b

twistStep f x fin with (f x)
  | Left l = l
  | Right (r ** rp) = fin r rp

accStepRec = accRec . twistStep

accStepRecInd : (f : Step a b rel) -> StepProp f p q -> (z : a) ->
                (za : Accessible rel z) -> p z -> q (accStepRec f z za)

StepTy : (f : Step a b rel) -> (a -> Type) -> (b -> Type) -> a -> Type
StepTy {rel} f p q z = (za : Accessible rel z) -> p z -> q (accStepRec f z za)

twistStepProp : (f : Step a b rel) -> StepProp f p q -> (x : a) ->
                ((y : a) -> rel y x -> StepTy f p q y) -> StepTy f p q x

twistStepProp f pf x fin (Access xa) px with (pf x px)
  | pfx with (f x)
    | Left l = pfx
    | Right (fx ** fxl) = fin fx fxl (xa fx fxl) pfx

accStepRecInd {p} {q} f pf z za =
  accInd {P=StepTy f p q} (twistStepProp f pf) z za za

accStepRecEq : (st : Step a b rel) -> StepPropEq c st f g -> (z : a) ->
               (za : Accessible rel z) -> g (accStepRec st z za) = f z

twistStepPropEq : (st : Step a b rel) -> StepPropEq c st f g -> (v : c) ->
                  StepProp st (\x => f x = v) (\x => g x = v)

twistStepPropEq st pr v x q with (pr x)
  | prx with (st x)
    | Left l = trans prx q
    | Right (y ** yr) = trans prx q

accStepRecEq {f} st pr z za =
  accStepRecInd st (twistStepPropEq st pr (f z)) z za $ Refl {x=f z}

accStepInd : PropStep a p rel -> (z : a) -> Accessible rel z -> p z

twistPropStep : PropStep a p rel -> (x : a) ->
                ((y : a) -> rel y x -> p y) -> p x

twistPropStep f x rec with (f x)
  | Left px = px
  | Right (y ** (yx, fy)) = fy (rec y yx)

accStepInd = accInd . twistPropStep

accShift : (z : a) -> Accessible rel (f z) -> Accessible (rel `on` f) z
accShift {f} z (Access ac) = Access (\y, ry => accShift y (ac (f y) ry))

Accbl : (a' -> a' -> Type) -> (a -> a') -> Type
Accbl {a} rel af = (x : a ** Accessible rel (af x))

accblize : (rel : a' -> a' -> Type) -> (af : a -> a') ->
           Accbl rel af -> Accbl rel af -> Type
accblize rel af = rel `on` (af . fst)

accblizeAcc : (rel : a' -> a' -> Type) -> (af : a -> a') ->
              (x : a) -> (xa : Accessible rel (af x)) ->
              Accessible (accblize rel af) (x ** xa)
accblizeAcc rel af x xa = accShift {f=af . fst} (x ** xa) xa

CommStepProp : (af : a -> a') -> (b -> b') -> Step a' b' rel ->
               Step a b (rel `on` af) -> Accbl rel af -> Type
CommStepProp af bf sl sr (z ** za) =
  accStepRec sl (af z) za = bf (accStepRec sr z (accShift z za))

accRecComm : CommStep {a} rel af bf sl sr -> (z : a) ->
             (za : Accessible rel (af z)) ->
             CommStepProp af bf sl sr (z ** za)

twistCommStep : CommStep {a} rel af bf sl sr ->
                PropStep (Accbl rel af) (CommStepProp af bf sl sr)
                (accblize rel af)

tcsH : (x : a) -> Step a b rel -> ((y : a) -> rel y x -> Accessible rel y) ->
       (y : a ** rel y x) -> b
tcsH x sl xa (y ** yr) = accStepRec sl y (xa y yr)

twistCommStep {af} {sl} {sr} cs (x ** Access xa) with (cs x)
  | csx with (sl (af x))
    | Left lb with (sr x)
      | Left rb = Left (leftInjective csx)
      | Right (ry ** rr) = void (leftNotRight csx)
    | Right (ly ** lr) with (sr x)
      | Left rb = void (leftNotRight (sym csx))
      | Right (ry ** rr) = Right ((ry ** xa (af ry) rr) **
        (rr, trans (cong {f=tcsH (af x) sl xa} (rightInjective csx))))

accRecComm {rel} {af} cs z za =
  accStepInd (twistCommStep cs) (z ** za) (accblizeAcc rel af z za)

wfStepRec : WellFounded rel => Step a b rel -> a -> b
wfStepRecInd : WellFounded rel => (f : Step a b rel) -> StepProp f p q ->
               (z : a) -> p z -> q (wfStepRec f z)
wfStepRecEq : WellFounded rel => (st : Step a b rel) -> StepPropEq c st f g ->
              (z : a) -> g (wfStepRec st z) = f z
wfStepInd : WellFounded rel => PropStep a p rel -> (z : a) -> p z

sizeStepRec : Sized a => Step a b Smaller -> a -> b
sizeStepRecInd : Sized a => (f : Step a b Smaller) -> StepProp f p q ->
                 (z : a) -> p z -> q (sizeStepRec f z)
sizeStepRecEq : Sized a => (st : Step a b Smaller) -> StepPropEq c st f g ->
              (z : a) -> g (sizeStepRec st z) = f z
sizeStepInd : Sized a => PropStep a p Smaller -> (z : a) -> p z

wfStepRec {rel} f z = accStepRec f z (wellFounded {rel} z)
wfStepRecInd {rel} f pf z = accStepRecInd f pf z (wellFounded {rel} z)
wfStepRecEq {rel} st pf z = accStepRecEq st pf z (wellFounded {rel} z)
wfStepInd {rel} f z = accStepInd f z (wellFounded {rel} z)

sizeAcc' : (Sized a) => (x : Nat) -> (y : a) -> (size y `LT` x) ->
           SizeAccessible y
sizeAcc' (S x') y (LTESucc yLEx') =
  Access (\z, zLTy => sizeAcc' x' z (lteTransitive zLTy yLEx'))

sizeAcc : (Sized a) => (x : a) -> SizeAccessible x
sizeAcc x = Access (sizeAcc' $ size x)

sizeStepRec f z = accStepRec f z (sizeAcc z)
sizeStepRecInd f pf z = accStepRecInd f pf z (sizeAcc z)
sizeStepRecEq st pf z = accStepRecEq st pf z (sizeAcc z)
sizeStepInd f z = accStepInd f z (sizeAcc z)

CompatSize : (Sized a, Sized a') => (a -> a') -> Type
CompatSize {a} af = (x : a) -> size (af x) = size x

ssLTE : (x : Nat) -> (y : Nat) -> SubSing (x `LTE` y)
ssLTE Z y LTEZero LTEZero = Refl
ssLTE (S x) (S y) (LTESucc a) (LTESucc b) = cong (ssLTE x y a b)

ssSmaller : Sized a => (x : a) -> (y : a) -> SubSing (Smaller x y)
ssSmaller x y = ssLTE (S (size x)) (size y)

twstSmlr' : x = y -> LTE x z -> LTE y z
twstSmlr' {x} {y = x} Refl = id
twstSmlr : x = y -> LT x z -> LT y z
twstSmlr p = twstSmlr' (cong p)
twstLrgr : x = y -> LT z x -> LT z y
twstLrgr {x} {y=x} Refl = id

ttsmlr : (p : x = y) -> (q : LT y z) -> twstSmlr p (twstSmlr (sym p) q) = q
ttsmlr Refl q = Refl

tssmlr : (p : x = y) -> (q : LTE x z) ->
  twstSmlr' (cong p) (LTESucc q) = LTESucc (twstSmlr' p q)
tssmlr {x} {y=x} Refl q = Refl

twistSmaller' : x' = x -> y' = y -> x `LT` y -> x' `LT` y'
twistSmaller' scx scy = twstLrgr (sym scy) . twstSmlr (sym scx)

twistSmaller : (Sized a, Sized a') => {af : a -> a'} ->
               {x : a} -> {y : a} -> size (af x) = size x ->
               size (af y) = size y -> Smaller x y -> Smaller (af x) (af y)
twistSmaller scx scy = twistSmaller' scx scy

SizeCommStep : (Sized a, Sized a') => (af : a -> a') -> (b -> b') ->
               Step a' b' Smaller -> Step a b Smaller -> Type
SizeCommStep {a} af bf sl sr =
  (x : a) -> either Left (Right . fst) (sl (af x)) =
             either (Left . bf) (Right . af . fst) (sr x)

sizeRecComm : (Sized a, Sized a') => CompatSize {a} {a'} af ->
              SizeCommStep af bf sl sr ->
              (z : a) -> sizeStepRec sl (af z) = bf (sizeStepRec sr z)

tscsH : (Sized a, Sized a') => (af : a -> a') -> CompatSize {a} {a'} af ->
        Step a b Smaller -> Step a b (Smaller `on` af)
tscsH {a'} af sc s x with (s x)
  | Left sx = Left sx
  | Right (y ** ry) = Right (y **
          twistSmaller {af} {x=y} {y=x} (sc y) (sc x) ry)

srcH : (Sized a, Sized a') => (af : a -> a') -> (sc : CompatSize af) -> 
       (st : Step a b Smaller) -> (z : a) ->
       accStepRec (tscsH af sc st) z (accShift z (sizeAcc (af z))) =
       accStepRec st z (sizeAcc z)

trsmlr : (scx : x' = x) -> (scy : y' = y) -> (xLy : x `LT` y) ->
         (yLz : y' `LTE` z) ->
         lteTransitive xLy (twstSmlr' scy yLz) =
         twstSmlr scx (lteTransitive (twistSmaller' scx scy xLy) yLz)

trsmlr {x} {x'=x} {y} {y'=y} Refl Refl xLy yLz = Refl

mutual
  srcH' : (Sized a, Sized a') => (af : a -> a') -> (sc : CompatSize af) ->
          (st : Step a b Smaller) -> (z : Nat) -> (y : a) ->
          (yLz : size (af y) `LT` z) -> 
          accStepRec (tscsH af sc st) y (accShift y (sizeAcc' z (af y) yLz)) =
          accStepRec st y (sizeAcc' z y (twstSmlr (sc y) yLz))
  srcHD : (Sized a, Sized a') => (af : a -> a') -> (sc : CompatSize af) ->
          (st : Step a b Smaller) -> (z : Nat) -> (y : a) ->
          (yLz : size (af y) `LTE` z) ->
          accStepRec (tscsH af sc st) y
            (accShift y (sizeAcc' (S z) (af y) (LTESucc yLz))) =
          accStepRec st y (sizeAcc' (S z) y (LTESucc (twstSmlr' (sc y) yLz)))

  srcHD af sc st z y yLz with (st y)
    | Left dn = Refl
    | Right (x ** xr) = rewrite trsmlr (sc x) (sc y) xr yLz in
      srcH' af sc st z x (lteTransitive (twistSmaller' (sc x) (sc y) xr) yLz)

  srcH' af sc st (S z) y (LTESucc yLz) =
    trans (srcHD af sc st z y yLz)
          (sym (cong {f=\yr => accStepRec st y (sizeAcc' (S z) y yr)}
                     (tssmlr (sc y) yLz)))

srcHB : (Sized a, Sized a') => (af : a -> a') -> (sc : CompatSize af) ->
        (st : Step a b Smaller) -> (z : a) -> (y : a) -> (prf : Smaller y z) ->
        accStepRec (tscsH af sc st) y
          (accShift y (sizeAcc' (size z) (af y) (twstSmlr (sym (sc y)) prf))) =
        accStepRec st y (sizeAcc' (size z) y 
          (twstSmlr (sc y) (twstSmlr (sym (sc y)) prf))) ->
        accStepRec (tscsH af sc st) y (accShift y (sizeAcc'
          (size (af z)) (af y) (twistSmaller {a} {a'} (sc y) (sc z) prf))) =
        accStepRec st y (sizeAcc' (size z) y prf)

srcHC : (Sized a) => (z : Nat) -> (z' : Nat) -> (scz : z = z') -> (y : a) ->
        (yLz : size y `LT` z) ->
        sizeAcc' z' y (twstLrgr scz yLz) = sizeAcc' z y yLz
srcHC z z Refl y yLz = Refl

srcHB af sc st z y prf q = trans (trans 
  (cong {f=\ya => accStepRec (tscsH af sc st) y (accShift y ya)}
    (srcHC (size z) (size (af z)) (sym (sc z)) (af y)
      (twstSmlr (sym (sc y)) prf))) q)
  (cong {f=\prf => accStepRec st y (sizeAcc' (size z) y prf)}
    (ttsmlr (sc y) prf))

srcH {a} {a'} af sc st z with (st z)
  | Left rlt = Refl
  | Right (y ** prf) = srcHB af sc st z y prf $
     srcH' af sc st (size z) y (twstSmlr (sym (sc y)) prf)

tscsP : (Sized a, Sized a') => (af : a -> a') -> (sc : CompatSize {a'} af) ->
        (x : a) -> (ly : a') -> (lr : Smaller ly (af x)) ->
        (ry : a) -> (rr : Smaller ry x) -> ly = af ry ->
        the (y : a' ** Smaller y (af x)) (ly ** lr) =
        the (y : a' ** Smaller y (af x)) (af ry **
                       twistSmaller {a} {a'} (sc ry) (sc x) rr)
tscsP {a} {a'} af sc x (af ry) lr ry rr Refl =
  cong (ssSmaller (af ry) (af x) lr (twistSmaller {a} {a'} (sc ry) (sc x) rr))

twistSizeCommStep : (Sized a, Sized a') => {af : a -> a'} ->
                    (sc : CompatSize af) ->
                    SizeCommStep af bf sl sr ->
                    CommStep Smaller af bf sl (tscsH af sc sr)
twistSizeCommStep {af} {sl} {sr} sc cs x with (cs x) 
 | csx with (sl (af x))
   | Left lb with (sr x)
     | Left rb = cong (leftInjective csx)
     | Right (ry ** rr) = void (leftNotRight csx)
   | Right (ly ** lr) with (sr x)
     | Left rb = void (leftNotRight (sym csx))
     | Right (ry ** rr) = cong (tscsP af sc x ly lr ry rr (rightInjective csx))

sizeRecComm {af} {sr} sc cs z = rewrite sym (srcH af sc sr z) in
  accRecComm (twistSizeCommStep sc cs) z (sizeAcc (af z))
