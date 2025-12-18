def as := [-1, 2, 0, -3, 4]

#guard as.map (fun a => ite (GE.ge a 0) [a] []) == [[], [2], [0], [], [4]]

-- Used to fail if we use `withSynthesize` instead of `withSynthesizeLight` at `elabBinRel`
#guard as.map (fun a => ite (a ≥ 0) [a] []) = [[], [2], [0], [], [4]]

example : True :=
  /-
  Requires type annotation at the numeral, otherwise we get a type error at `rfl`
  because `(0 == 1)` does not reduce to `false` until the default instance is applied.
  Possible improvement: before reporting a type mismatch, apply default instances, and try again.
  -/
  have : (0 == (1 : Nat)) = false := rfl
  ⟨⟩
