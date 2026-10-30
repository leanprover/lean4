/-!
Regression test for #15859: the `[grind hom]` extension must not rewrite `HEq` facts.
An asserted `a ≍ b` has no E-node, and rewriting the `BitVec` equation in the type of a proof
inside it used to produce the internal error "term has not been internalized".
-/

example (a : BitVec 8) (p : a = 1) (h : p ≍ True.intro) : a = 1 := by
  grind

example (a : UInt8) (p : a = 1) (h : p ≍ True.intro) : a = 1 := by
  grind

example (a : Fin 5) (p : a = 1) (h : p ≍ True.intro) : a = 1 := by
  grind

def getOne (x : Option (BitVec 8)) (h : x.getD 0 = 1) : BitVec 8 :=
  match x, h with
  | some v, _ => v
  | none, h => absurd h (by decide)

example (x : Option (BitVec 8)) (h : x.getD 0 = 1) : getOne x h = 1 := by
  unfold getOne
  grind
