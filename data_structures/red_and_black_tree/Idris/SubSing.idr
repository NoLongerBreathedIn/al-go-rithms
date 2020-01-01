module SubSing

-- Subsingleton stuff for the RBTree implementation
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

public export
total SubSing : Type -> Type
SubSing t = (a : t) -> (b : t) -> a = b

export
total ssEither : SubSing l -> SubSing r -> (l -> r -> Void) ->
                 SubSing (Either l r)
ssEither lf rf cf (Left a) (Left b) = cong (lf a b)
ssEither lf rf cf (Left a) (Right b) = void (cf a b)
ssEither lf rf cf (Right a) (Left b) = void (cf b a)
ssEither lf rf cf (Right a) (Right b) = cong (rf a b)

export
total ssPair : SubSing l -> SubSing r -> SubSing (l, r)
ssPair lf rf (al, ar) (bl, br) with (lf al bl)
  ssPair lf rf (bl, ar) (bl, br) | Refl with (rf ar br)
    ssPair lf rf (bl, br) (bl, br) | Refl | Refl = Refl

export
total ssUnit : SubSing ()
ssUnit () () = Refl

export
total ssVoid : SubSing Void
ssVoid a = void a

export
total ssMebbe : SubSing n -> ((j : t) -> SubSing (f j)) -> (v : Maybe t) ->
                SubSing (maybe n f v)
ssMebbe nf jf Nothing = nf
ssMebbe nf jf (Just jv) = jf jv

export
total ssWhich : ((v : l) -> SubSing (f v)) -> ((w : r) -> SubSing (g w)) ->
                (e : Either l r) -> SubSing (either f g e)
ssWhich lf rf (Left lv) = lf lv
ssWhich lf rf (Right rv) = rf rv

export
total ssDP : {v : k -> Type} -> SubSing k ->
             ((a : k) -> SubSing (v a)) -> SubSing (a : k ** v a)
ssDP lf rf (al ** ar) (bl ** br) with (lf al bl)
  ssDP lf rf (bl ** ar) (bl ** br) | Refl = cong (rf bl ar br)

export
total ssEql : (a : t) -> (b : s) -> SubSing (a = b)
ssEql a a Refl Refl = Refl
