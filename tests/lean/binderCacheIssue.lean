universe u v w

class Funtype (N : Sort u) (O : outParam (Sort v)) (T : outParam (Sort w)) :=
  pack : O -> N
  unpack : N -> O
  apply : N -> T

class LNot {P : Sort u} (L : P -> Prop) :=
  toFun : (p : P) -> Not (L p)

namespace LNot
variable {P : Sort u} {L : P -> Prop}
abbrev applyFun (K : LNot L) {p} := K.toFun p
abbrev unpackFun (K : LNot L) := K.toFun
instance isFuntype : Funtype (LNot L)
  ((p : P) -> Not (L p)) ({p : P} -> Not (L p)) :=
  {pack := mk, unpack := unpackFun, apply := applyFun}
end LNot

#check LNot.unpackFun
#check LNot.isFuntype.unpack
#check LNot.applyFun
#check LNot.isFuntype.apply
