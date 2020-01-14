module RBTreeS.SizeUp

-- Some utility functions used to talk about the sizes of red-black trees.
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

public export
total sizeUp : Bool -> Nat -> Nat

sizeUp True = S . (* 2)
sizeUp False = (* 2)

public export
total sultCol : (n : Nat) -> sizeUp False n `LT` sizeUp True n
public export
total sultNum : (m : Nat) -> (b : Bool) -> (b' : Bool) -> (n : Nat) ->
                sizeUp b n `LT` sizeUp b' (S m + n)

public export
total sultS : (b : Bool) -> (n : Nat) -> sizeUp b (S n) = S (S (sizeUp b n))
sultS True n = Refl
sultS False n = Refl

public export
total sultNA : (m : Nat) -> (b : Bool) -> (b' : Bool) -> (n : Nat) ->
               sizeUp b n `LTE` S (sizeUp b' (m + n))

public export
total sultNB : (m : Nat) -> (b : Bool) -> (n : Nat) ->
               n * 2 `LTE` sizeUp b (m + n)

public export
total sultNC : (m : Nat) -> (n : Nat) -> n * 2 `LTE` (m + n) * 2

sultNC m n = rewrite plusCommutative m n in
  rewrite multDistributesOverPlusLeft n m 2 in lteAddRight (n * 2)

sultNB m True n = lteSuccRight $ sultNC m n
sultNB m False n = sultNC m n

sultNA m False b n = lteSuccRight $ sultNB m b n
sultNA m True b n = LTESucc $ sultNB m b n

sultCol n = lteRefl
sultNum m b b' n = rewrite sultS b' (m + n) in LTESucc $ sultNA m b b' n

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
 
 
