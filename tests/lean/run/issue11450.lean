/-! Regressions from working on #11450 -/


namespace Test

inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β

end Test


inductive Term (L: Nat → Type) (n : Nat) : Nat → Type _
| var  (k: Fin n)                           : Term L n 0
| func (f: L l)                             : Term L n l
| app  (t: Term L n (l + 1)) (s: Term L n 0): Term L n l

/--
info: @[reducible] def Term.var.noConfusion.{u} : {L : Nat → Type} →
  {n : Nat} → (P : Sort u) → (k k_1 : Fin n) → 0 = 0 → Term.var k = Term.var k_1 → (k = k_1 → P) → P
-/
#guard_msgs in
#print sig Term.var.noConfusion
