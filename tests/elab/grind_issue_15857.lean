/-!
Regression test for #15857: the `[grind hom]` rewriter must not rewrite raw `Nat` literals.
A raw literal from a numeral instance (e.g., `BitVec.instOfNat W 5`) used to be equated with
`OfNat.ofNat Nat 5`, and `grind` treated the two as distinct values, producing a proof the
kernel rejected.
-/

def W : Nat := 4

example (x : BitVec W) (h : x = 5) : x = 5 := by grind

example (x : BitVec W) (h : x = 5) : x.toNat = 5 := by grind

example (x y : BitVec W) (h : x = 5) (h' : y = 3) : x + y = 8 := by grind

def N : Nat := 7
instance : NeZero N := ⟨by decide⟩

example (x : Fin N) (h : x = 5) : x = 5 := by grind
