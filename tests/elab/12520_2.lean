import Lean
open Lean Meta Elab Tactic

/-! Ensures partial applications of recursors for K-like and structure types are appropriately eta-expanded during type-checking.-/

variable (a : true = true → Bool)

example : (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _) = fun h => a h := rfl
example : (fun h => a h) = a := rfl
example  : (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _) = a := rfl

variable (a : Unit → Bool)
example : @PUnit.rec (fun _ => Bool) (a ()) = a := rfl

variable (a : Bool × Bool → Bool)
example : @Prod.rec Bool Bool (motive := fun _ => Bool) (fun b c => a (b,c)) = fun b => a b := rfl
example : @Prod.rec Bool Bool (motive := fun _ => Bool) (fun b c => a (b,c)) = a := rfl

macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

-- Recursors for K-like types need special care to ensure they only get eta-expanded when the arguments are appropriate (i.e when the major is indeed defeq to the nullary ctor). We make sure these examples fail correctly rather than loop, both in the elaborator and the kernel.

/--
error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  ∀
    (g :
      {α : Sort u_1} →
        {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_2} → motive a ⋯ → {a_1 : α} → (t : a = a_1) → motive a_1 t),
    @Eq.rec = g
-/
#guard_msgs in
example : ∀ g, @Eq.rec = g := rfl

/--
error: (kernel) declaration type mismatch, '_example' has type
  ∀
    {g :
      {α : Sort u_1} →
        {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_2} → motive a ⋯ → {a_1 : α} → (t : a = a_1) → motive a_1 t},
    g = g
but it is expected to have type
  ∀
    {g :
      {α : Sort u_1} →
        {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_2} → motive a ⋯ → {a_1 : α} → (t : a = a_1) → motive a_1 t},
    @Eq.rec = g
-/
#guard_msgs in
example {g}: @Eq.rec = g := by unchecked_rfl

/--
error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  @And.rec = g
-/
#guard_msgs in
example {g}: @And.rec = g := rfl

/--
error: (kernel) declaration type mismatch, '_example' has type
  ∀ {g : {a b : Prop} → {motive : a ∧ b → Sort u_1} → ((left : a) → (right : b) → motive ⋯) → (t : a ∧ b) → motive t},
    g = g
but it is expected to have type
  ∀ {g : {a b : Prop} → {motive : a ∧ b → Sort u_1} → ((left : a) → (right : b) → motive ⋯) → (t : a ∧ b) → motive t},
    @And.rec = g
-/
#guard_msgs in
example {g}: @And.rec = g := by unchecked_rfl

example {g}: @Exists.rec = g := rfl
