example (n : Nat) : Nat := by
  guard_hyp n :ₛ Nat
  let m : Nat := 1
  guard_expr 1 =ₛ (by exact 1)
  fail_if_success guard_expr 1 = (by exact 2)
  guard_hyp m := 1
  guard_hyp m : (fun x => x) Nat :=~ id 1
  guard_target = Nat
  have : 1 = 1 := by conv =>
    guard_hyp m := 1
    guard_expr ‹Nat› = m
    fail_if_success guard_target = 1
    lhs
    guard_target = 1
  exact 0

-- Now with a generic type to test that default instances work correctly
example [∀ n, OfNat α n] (n : α) : α := by
  guard_hyp n
  fail_if_success guard_hyp m
  guard_hyp n :ₛ α
  let q : α := 1
  guard_expr (1 : α) =ₛ 1
  fail_if_success guard_expr 1 =ₛ (2 : α)
  fail_if_success guard_expr 1 =ₛ (by exact (2 : α))
  guard_hyp q := 1
  guard_hyp q : α := 1
  guard_hyp q : (fun x => x) α :=~ id 1
  guard_target = α
  have : (1 : α) = 1 := by conv =>
    guard_hyp q := 1
    guard_expr ‹α› = q
    fail_if_success guard_target = 1
    lhs
    guard_target = 1
  exact 0

#guard_expr 1 = 1
#guard_expr 1 =ₛ 1
#guard_expr 2 = 1 + 1

section
variable {α : Type} [∀ n, OfNat α n]
#guard_expr (1 : α) = 1
end

#guard true
#guard 2 == 1 + 1
#guard 2 = 1 + 1

instance (p : Bool → Prop) [DecidablePred p] : Decidable (∀ b, p b) :=
  if h : p false ∧ p true then
    isTrue (by { intro b; cases h; cases b <;> assumption })
  else
    isFalse (by { intro h'; simp [h'] at h })

#guard ∀ (b : Bool), b = !!b
