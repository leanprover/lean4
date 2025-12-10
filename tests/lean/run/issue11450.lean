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
  {n : Nat} → {P : Sort u} → {k k' : Fin n} → Term.var k = Term.var k' → (k ≍ k' → P) → P
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

inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons : {n : Nat} → (x : α) → (xs : Vec α n) → Vec α (n + 1)

/--
info: Vec.cons.noConfusion.{u_1, u} {α : Type u} {P : Sort u_1} {n : Nat} {x : α} {xs : Vec α n} {n' : Nat} {x' : α}
  {xs' : Vec α n'} (eq_1 : n + 1 = n' + 1) (eq_2 : Vec.cons x xs ≍ Vec.cons x' xs')
  (k : n = n' → x ≍ x' → xs ≍ xs' → P) : P
-/
#guard_msgs in
#check Vec.cons.noConfusion

/--
info: Vec.cons.inj.{u} {α : Type u} {n : Nat} {x : α} {xs : Vec α n} {x✝ : α} {xs✝ : Vec α n} :
  Vec.cons x xs = Vec.cons x✝ xs✝ → x = x✝ ∧ xs = xs✝
-/
#guard_msgs in
#check Vec.cons.inj

theorem Vec.cons.hinj' {α : Type u}
  {x : α} {n : Nat} {xs : Vec α n} {x' : α} {n' : Nat} {xs' : Vec α n'} :
  Vec.cons x xs ≍ Vec.cons x' xs' → (n + 1 = n' + 1 → (x = x' ∧ xs ≍ xs')) := by
  intro h eq_1
  apply Vec.cons.noConfusion eq_1 h (fun _ eq_x eq_xs => ⟨eq_of_heq eq_x, eq_xs⟩)

/--
info: Vec.cons.hinj.{u} {α : Type u} {n : Nat} {x : α} {xs : Vec α n} {α✝ : Type u} {n✝ : Nat} {x✝ : α✝} {xs✝ : Vec α✝ n✝} :
  α = α✝ → n + 1 = n✝ + 1 → Vec.cons x xs ≍ Vec.cons x✝ xs✝ → α = α✝ ∧ n = n✝ ∧ x ≍ x✝ ∧ xs ≍ xs✝
-/
#guard_msgs in
#check Vec.cons.hinj
