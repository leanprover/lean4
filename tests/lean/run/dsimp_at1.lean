open tactic

constants (A : Type.{1}) (x y : A)

definition f (z : A) : A := z
definition f.def [defeq] (z:A) : f z = z := rfl

definition foo (z₁ z₂ : A) : f z₁ = f z₂ → z₁ = z₂ :=
by do H ← intro "H",
      trace_state,
      dsimp_at H,
      trace_state,
      assumption
