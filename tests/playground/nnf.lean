open Lean

partial def mkBigAnd (n : Nat) (p : Syntax) : MacroM Syntax :=
  loop 0 n
where
  loop (low high : Nat) : MacroM Syntax := do
    if low == high then
      `($p[natLit! $(quote low)])
    else
      let mid := (low + high)/2
      `($(← loop low mid) ∧ $(← loop (mid + 1) high))

macro "bigAnd! " n:num p:ident : term => mkBigAnd n.toNat p

partial def mkBigOrNot (n : Nat) (p : Syntax) : MacroM Syntax :=
  loop 0 n
where
  loop (low high : Nat) : MacroM Syntax := do
    if low == high then
      `(¬ $p[natLit! $(quote low)])
    else
      let mid := (low + high)/2
      `($(← loop low mid) ∨ $(← loop (mid + 1) high))

macro "bigOrNot! " n:num p:ident : term => mkBigOrNot n.toNat p

@[simp] axiom not_and (p q : Prop) : (¬ (p ∧ q)) = (¬ p ∨ ¬ q)

theorem ex (p : Array Prop) : (¬ bigAnd! 2000 p) = bigOrNot! 2000 p := by
  simp only [not_and]
  rfl

-- #print ex
