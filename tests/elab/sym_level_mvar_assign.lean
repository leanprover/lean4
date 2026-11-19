/-!
`sym` must not create cyclic universe level metavariable assignments (`?u := ?u`, `?u := ?u+1`),
nor overwrite an assigned one. `apply step*` leaves universe level metavariables in the new goals.
-/

/-- `Q A` fixes the universe of `A`, so that no universe level metavariable is left in the proof. -/
def Q.{c} (_ : Sort c) : Prop := True

/-! `?a =?= 0` and then `?a =?= ?a` -/

theorem step {A : Type c} (_ : ∀ (α : Type a) (β : Type c) (p : β × (α × α)), @id (β × (α × α)) p = p)
    (h : Q A) : Q A := h

theorem id_prod_same {α β : Type u} (p : β × (α × α)) : @id (β × (α × α)) p = p := rfl

example : Q Nat := by
  sym =>
    apply step
    · intro α β p
      apply id_prod_same
    · exact True.intro

/-! `?u+1 =?= ?u` has no solution. -/

structure G.{a, b} (α : Type a) : Type (max a b) where
  val : α

theorem step2 {P : Prop} (_ : ∀ (α : Type u) (x : G.{u, u} α), @id (G.{u, u} α) x = x) (h : P) : P := h

theorem id_g_succ {α : Type u} (x : G.{u, u+1} α) : @id (G.{u, u+1} α) x = x := rfl

/-- error: `apply` failed, rule is not applicable -/
#guard_msgs in
example : True := by
  sym =>
    apply step2
    · intro α x
      apply id_g_succ
    · exact True.intro

/-! `?a =?= ?b` and then `?a =?= 1` must solve `?b := 1` instead of overwriting `?a := ?b`. -/

def K.{a, b, c} : Type := (fun (_ : Sort a) (_ : Sort b) (_ : Sort c) => Unit) PUnit PUnit PUnit

theorem step3 {A : Sort c} (_ : ∀ x : K.{a, b, c}, @id K.{a, b, c} x = x) (h : Q A) : Q A := h

theorem id_k (x : K.{u, u, u}) : @id K.{u, u, u} x = x := rfl

example : Q Nat := by
  sym =>
    apply step3
    · intro x
      apply id_k
    · exact True.intro
