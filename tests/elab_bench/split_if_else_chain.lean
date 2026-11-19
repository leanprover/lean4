/-!
`split` on a long `else if` chain.

With `backward.split true`, `split` simplifies the goal with `ite_eq_left`, `ite_eq_right` and a
discharger that uses the hypothesis introduced by the case split. It used to take time exponential
in the length of the chain because the discharger was not marked as well-behaved.
-/

set_option hygiene false in
/-- `chain_test n => tac` runs `tac` on a goal with `n` nested `if`s in the hypothesis `h` and in the target. -/
macro "chain_test " n:num " => " t:tacticSeq : command => do
  let n := n.getNat
  let mut e ← `($(Lean.Syntax.mkNatLit n))
  for i in [0:n] do
    let j := n - 1 - i
    e ← `(if p $(Lean.Syntax.mkNatLit j) then $(Lean.Syntax.mkNatLit j) else $e)
  `(example (p : Nat → Prop) [DecidablePred p] (x : Nat) (h : $e = x) : $e = x := by $t)

/-! One `split` of the hypothesis, and one of the target. -/
chain_test 100 => split at h <;> split <;> first | exact h | contradiction

/-! `split` until there is no `if` in the hypothesis. -/
chain_test 30 => (repeat' split at h) <;> (subst h; simp [*])

/-! The hypothesis introduced by `split` is used in the whole chain. -/

example (p q : Prop) [Decidable p] [Decidable q] (x : Nat)
    (h : (if q then 0 else if p then 1 else if q then 2 else if p then 3 else 4) = x) :
    x = 0 ∨ x = 1 ∨ x = 4 := by
  split at h
  · exact .inl h.symm
  · guard_hyp h : (if p then 1 else if p then 3 else 4) = x
    split at h
    · exact .inr (.inl h.symm)
    · guard_hyp h : 4 = x
      exact .inr (.inr h.symm)
