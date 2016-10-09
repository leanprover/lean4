open tactic

constants (A : Type.{1}) (x y : A)

noncomputable definition f (z : A) : A := z
@[simp] definition f.def (z:A) : f z = z := rfl

definition foo (z₁ z₂ : A) : f z₁ = f z₂ → z₁ = z₂ :=
by do H ← intro `H,
      trace_state,
      rsimp_at H,
      trace_state,
      assumption
