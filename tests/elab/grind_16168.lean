/-! https://github.com/leanprover/lean4/issues/16168

`grind` built a proof of a `Grind.MatchCond` that refuted the equation between a literal
and a pattern variable (`decide ¬3 = a`), which the kernel rejected. -/

def p (s : Nat × Bool) : Nat := match s with | (_, true) => 0 | _ => 1
theorem t₁ : p (3, false) = 1 := by grind [p]

def f₀ (x : Nat) := match (x, 1) with | (a, 0) => a | _ => 7
theorem t₂ : f₀ 3 = 7 := by grind [f₀]

def f₂ (x : Nat) (y : UInt8) : Nat := match (x, y) with | (a, 0) => a | _ => 7
theorem t₃ : f₂ 3 1 = 7 := by grind [f₂]

/-! The literal fields still refute the condition when the pattern variable comes second. -/

def q (s : Bool × Nat) : Nat := match s with | (true, _) => 0 | _ => 1
theorem t₄ : q (false, 3) = 1 := by grind [q]

def g (x : Nat) := match (1, x) with | (0, a) => a | _ => 7
theorem t₅ : g 3 = 7 := by grind [g]
