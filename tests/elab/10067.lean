module

/-!
# `mutual public structure`
-/

namespace Issue10067

mutual
public structure PubStruct where
  val : Nat
  i? : Option PubInduct

public inductive PubInduct
| ofStruct (s : PubStruct)
| alt (val : Nat)
end

/-! Used to be "Unknown constant `PubInduct.alt`" -/
@[expose] public def mkPubInduct (val : Nat) : PubInduct :=
  PubInduct.alt val

def mkPrivatePubInduct (val : Nat) : PubInduct :=
  PubInduct.alt val

/-! Used to be "invalid {...} notation, constructor for `PubStruct` is marked as private" -/
@[expose] public def mkPubStruct (val : Nat) : PubStruct :=
  {val, i? := none}

/-! Used to be "Field `val` from structure `PubStruct` is private" -/
@[expose] public def pubStructVal (s : PubStruct) : Nat :=
  s.val

end Issue10067

/-! Duplicate issue. -/
namespace Issue11116

public structure A where

mutual
public structure B where
end

@[expose] public def testA1 := A.mk
@[expose] public def testA2 : A := {}
-- Used to be "unknown constant B.mk"
@[expose] public def testB1 := B.mk
@[expose] public def testB2 : B := {}

end Issue11116
