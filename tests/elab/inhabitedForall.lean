module

/-!
Tests that `Pi.instInhabited` is the only `Inhabited` instance for function types. A former
instance `Inhabited (α → m α) := ⟨pure⟩` overlapped with it on types like `Nat → Option Nat`,
giving a `default` that disagreed with `Pi.instInhabited` and that lemmas about it did not apply to.
-/

/-- info: Pi.instInhabited -/
#guard_msgs in
#synth Inhabited (Nat → Nat)

/-- info: Pi.instInhabited -/
#guard_msgs in
#synth Inhabited (Nat → Option Nat)

example : (default : Nat → Option Nat) = fun _ => none := rfl
example : (default : Nat → Option Unit) = fun _ => none := rfl
example : (default : Nat → Id Nat) = fun _ => (0 : Nat) := rfl

theorem default_pi {α : Sort u} {β : α → Sort v} [∀ a, Inhabited (β a)] :
    @default (∀ a, β a) _ = fun a : α => @default (β a) _ := rfl

example : (default : Nat → Option Nat) 3 = none := by
  simp only [default_pi]
  rfl

/-! `partial` does not need `Inhabited (α → m α)`, even when `α` may be empty. -/

partial def loopBinder {α : Type} {m : Type → Type} [Monad m] (x : α) : m α := loopBinder x
partial def loopLambda {α : Type} {m : Type → Type} [Monad m] : α → m α := fun x => loopLambda x
