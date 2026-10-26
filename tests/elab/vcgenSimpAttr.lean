import Lean

/-! The `@[vcgen_simp]` attribute tags `Sym.simp` theorems, both at the declaration and afterwards. -/

def g (n : Nat) : Nat := 0 + n

@[vcgen_simp] theorem g_eq (n : Nat) : g n = n := Nat.zero_add n

attribute [vcgen_simp] Nat.add_zero
