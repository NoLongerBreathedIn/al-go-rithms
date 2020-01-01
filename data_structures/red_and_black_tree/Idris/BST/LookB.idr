module BST.LookB -- 'B' due to idris bug #3539

-- Lookup in BSTs (used in proofs)
-- (c) Eyal Minsky-Fenick/NoLongerBreathedIn 2019-2020 CC-BY

import SubSing
import TotalOrd
import BST.StructsB

mutual
  public export
  total lookT : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                BST k o b v -> Maybe (v a)
  public export
  total pickT : (o : Comp k) -> TotalOrd k o -> (a : k) ->
                BST k o lb v -> (m : k) -> v m -> BST k o rb v ->
                Maybe (v a)

  pickT o to a l m w r with (enh o a m)
    | LTE x = lookT o to a l
    | EQE x = Just (replace (corff to x) w)
    | GTE x = lookT o to a r

  lookT o to a Leaf = Nothing
  lookT o to a (Node l m w r p) = pickT o to a l m w r

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

public export
total lookZ : (o : Comp k) -> TotalOrd k o -> (a : k) ->
              BSZ k o cb pl pr v -> Maybe (v a)
public export
total lookZ' : (o : Comp k) -> TotalOrd k o -> (a : k) ->
               BSZ k o cb pl pr v -> Maybe (v a)

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

-- Local Variables:
-- idris-interpreter-flags: ("-i" "..")
-- End:
