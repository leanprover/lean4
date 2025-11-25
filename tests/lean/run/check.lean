import Lean

/-- info: And.intro {a b : Prop} (left : a) (right : b) : a ∧ b -/
#guard_msgs in
#check And.intro

/--
info: @Or.rec : ∀ {a b : Prop} {motive : a ∨ b → Prop},
  (∀ (h : a), motive ⋯) → (∀ (h : b), motive ⋯) → ∀ (t : a ∨ b), motive t
-/
#guard_msgs in
#check @Or.rec

/-- info: Eq.{u_1} {α : Sort u_1} : α → α → Prop -/
#guard_msgs in
#check Eq

/--
info: @Eq.rec : {α : Sort u_2} →
  {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_1} → motive a ⋯ → {a_1 : α} → (t : a = a_1) → motive a_1 t
-/
#guard_msgs in
#check @Eq.rec

/-!
The `#check` command also typechecks the result to help users debug buggy elaborators.
-/
section
open Lean

def expr_1eq1 : Expr := mkApp3 (.const ``Eq [0]) (.const ``Nat []) (mkNatLit 1) (mkNatLit 1)

elab "elab_1eq1" : term => return expr_1eq1

/--
error: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type` in the application
  @Eq Nat
-/
#guard_msgs in #check elab_1eq1

/--
error: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type` in the application
  @Eq Nat
-/
#guard_msgs in #reduce elab_1eq1
end
