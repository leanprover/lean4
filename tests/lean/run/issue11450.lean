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
  {n : Nat} → {P : Sort u} → {k k' : Fin n} → Term.var k = Term.var k' → (k = k' → P) → P
-/
#guard_msgs in
#print sig Term.var.noConfusion


def Vector' (α : Type u) (n : Nat) :=
  { l : List α // l.length = n }

inductive HVect : (n : Nat) -> (Vector' (Type v) n) -> Type (v+1)  where
   | Nil  : HVect 0 ⟨ [], simp ⟩
   | Cons : (t : Type v) -> (x : t) -> HVect n ⟨ts, p⟩ -> HVect (n+1) ⟨t::ts, by simp [p]⟩

/--
info: @[reducible] def HVect.Nil.noConfusion.{u, v} : {P : Sort u} →
  {simp simp' : [].length = 0} → HVect.Nil = HVect.Nil → P → P
-/
#guard_msgs in
#print sig HVect.Nil.noConfusion
