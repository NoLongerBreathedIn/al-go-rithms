module BST.MoveB -- 'B' due to idris bug #3539

-- Proof that moving around doesn't affect lookups
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import SubSing
import TotalOrd
import public BST.LookB

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
  | ELT x = mL1 o to a m w r p (Left x) g1
  | EEQ x = mL1 o to a m w r p (Right x) g1
  | EGT x = mL0 o to a l m w r p g0 q0 g1 q1

mL0 {pr=Nothing} o to a l m w r p g0 q0 g1 q1 = mL3 o to a l m w r p () g1 q1
mL0 {pr=Just pr} o to a l m w r p g0 q0 g1 q1 with (enh o a pr)
  | ELT x = mL3 o to a l m w r p x g1 q1
  | EEQ x = mL2 o to a l m w r p (Left x) g1 q1
  | EGT x = mL2 o to a l m w r p (Right x) g1 q1

mL1 o to a m w r p g q with (tranQL to g (fst (fst (snd q))))
  | x with (enh o a m)
    | ELT y = Refl
    | EEQ y = iLE x y
    | EGT y = iLG x y

mL2 {pr} o to a l m w r p j g1 q1 with (tranQG to j (flipLT to
                                                         (fst (snd (snd g1)))))
  | x with (enh o a m)
    | ELT y = iLG y x
    | EEQ y = iEG y x
    | EGT y with (enh o a m)
      | ELT z = iLG z x
      | EEQ z = iEG z x
      | EGT z with (enh o a pr)
        | ELT s = iLQ s j
        | EEQ s = Refl
        | EGT s = Refl

mL3 {pr} o to a l m w r p j g1 q1 with (enh o a m)
  | ELT x = Refl
  | EEQ x with (enh o a m)
    | ELT y = iLE y x
    | EEQ y with (ssIsEQ (o a m) x y)
      mL3 o to a l m w r p j g1 q1 | EEQ x | EEQ x | Refl = Refl
    | EGT y = iEG x y
  | EGT x with (enh o a m)
    | ELT y = iLG y x
    | EEQ y = iEG y x
    mL3 {pr=Nothing} o to a l m w r p j g1 q1 | EGT x | EGT y = Refl
    mL3 {pr=Just pr} o to a l m w r p j g1 q1 
      | EGT x | EGT y with (enh o a pr)
        | ELT z = Refl
        | EEQ z = iLE j z
        | EGT z = iLG j z

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
  | ELT x with (enh o a m)
    | ELT y = mR1 o to a l m w r p x g1
    | EEQ y = iLE x y
    | EGT y = iLG x y
  | EEQ x with (enh o a m)
    | ELT y = iLE y x
    | EEQ y = mR2 o to a l m w r p y g0 q0 g1
    | EGT y = iEG x y
  | EGT x = mR0 o to a l m w r p x g0 g1
mR {pl=Just pl} o to a l m w r p g0 q0 g1 q1 with (enh o a pl)
  | ELT x = mR7 o to a l m w r p (Left x) g1 q1
  | EEQ x = mR7 o to a l m w r p (Right x) g1 q1
  | EGT x with (enh o a m)
    | ELT y with (enh o a m)
      | ELT z with (enh o a pl)
        | ELT s = iLG s x
        | EEQ s = iEG s x
        | EGT s = mR1 o to a l m w r p y g1
      | EEQ z = iLE y z
      | EGT z = iLG y z
    | EEQ y with (enh o a m)
      | ELT z = iLE z y
      | EEQ z = mR2 o to a l m w r p z g0 q0 g1
      | EGT z = iEG y z
    | EGT y = mR0 o to a l m w r p y g0 g1

mR0 {pr=Nothing} o to a l m w r p j g0 g1 = mR3 o to a l m w r g0 j
mR0 {pr=Just pr} o to a l m w r p j g0 g1 with (enh o a pr)
  | ELT x = mR3 o to a l m w r g0 j
  | EEQ x = mR4 o to a l m w p g1 (Left x)
  | EGT x = mR4 o to a l m w p g1 (Right x)

mR1 {pr=Nothing} o to a l m w r p j g1 = mR5 o to a l m w r j
mR1 {pr=Just pr} o to a l m w r p j g1 with (tran to j (fst (snd (snd g1))))
  | x with (enh o a pr)
    | ELT y = mR5 o to a l m w r j
    | EEQ y = iLE x y
    | EGT y = iLG x y

mR2 {pr=Nothing} o to a l m w r p j g0 q0 g1 = mR6 o to a l m w r j
mR2 {pr=Just pr} o to a l m w r p j g0 q0 g1 with (tranQL to (Right j)
                                                          (fst (snd (snd g1))))
  | x with (enh o a pr)
    | ELT y = mR6 o to a l m w r j
    | EEQ y = iLE x y
    | EGT y = iLG x y

mR3 o to a l m w r g0 j with (enh o a m)
  | ELT x = iLG x j
  | EEQ x = iEG x j
  | EGT x = Refl

mR4 o to a l m w p g1 j with (tranQG to j (flipLT to (fst (snd (snd g1)))))
  | x with (enh o a m)
    | ELT y = iLG y x 
    | EEQ y = iEG y x
    | EGT y = Refl

mR5 o to a l m w r j with (enh o a m)
  | ELT x = Refl
  | EEQ x = iLE j x
  | EGT x = iLG j x

mR6 o to a l m w r j with (enh o a m)
  | ELT x = iLE x j
  | EEQ x with (ssIsEQ (o a m) x j)
    mR6 o to a l m w r j | EEQ j | Refl = Refl
  | EGT x = iEG j x

mR7 {pl} o to a l m w r p j g1 q1 with (tranQL to j (fst (fst (snd g1))))
  | x with (enh o a m)
    | ELT y with (enh o a m)
      | ELT z with (enh o a pl)
        | ELT s = Refl
        | EEQ s = Refl
        | EGT s = iQG j s
      | EEQ z = iLE y z
      | EGT z = iLG y z
    | EEQ y = iLE x y
    | EGT y = iLG x y

export
total moveRight : lookZ o to a (MkBSZ (Node l m w r g0) p q0) =
                  lookZ o to a (MkBSZ r (Rgt l m w p g1) q1)
moveRight {o} {to} {a} {l} {m} {w} {r} {p} {g0} {q0} {g1} {q1} =
  mR o to a l m w r p g0 q0 g1 q1

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
