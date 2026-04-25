def myAdd : Nat → Nat → Nat
  | 0, m => m
  | n+1, m => (myAdd n m).succ

set_option pp.motives.pi false

#print myAdd._f

set_option pp.motives.pi true

#print myAdd._f

set_option linter.unusedVariables false in
theorem ex : ∀ {α β : Sort u} (h : α = β) (a : α), cast h a ≍ a
  | α, _, rfl, a => HEq.refl a

set_option pp.motives.nonConst false

#print ex

set_option pp.motives.nonConst true

#print ex

noncomputable def fact (n : Nat) : Nat :=
  Nat.recOn n 1 (fun n acc => (n+1)*acc)

set_option pp.motives.all false

#print fact

set_option pp.motives.all true

#print fact
