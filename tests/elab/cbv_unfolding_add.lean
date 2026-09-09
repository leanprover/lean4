/-!
  Regression test making sure that partially applied operations with special casing,
  i.e. these supported by `EvalGround.lean` do not get unfolded, but they still are reduced
  in the kernel.

  Reported by Robin Arnez (@rob23oba).
-/

def coolApply (f : Nat → Nat → Nat) (x y : Nat) : Nat := f x y

def coolAdd := coolApply (· + ·)

def coolMul := coolApply (· * ·)

-- The reason we use `conv=>` mode is that we make sure that the proof doesn't go via defeq
example : coolAdd 13499 1341389 = 1354888 := by conv =>
  lhs;
  cbv

example : coolMul 13499 1341389 = 18107410111 := by conv =>
  lhs;
  cbv
