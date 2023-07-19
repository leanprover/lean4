prelude
import Init.Data.List.Basic

@[simp] theorem map_comp_map (f : α → β) (g : β → γ) : List.map g ∘ List.map f = List.map (g ∘ f) :=
  sorry

theorem map_map (f : α → β) (g : β → γ) (xs : List α) : (xs.map f |>.map g) = xs.map (g ∘ f) :=
  sorry

theorem ex1 (f : Nat → Nat) (xs : List Nat) : (xs.map f |>.map f) = xs.map (f ∘ f) := by
  fail_if_success simp
  simp [map_map]
  done

theorem ex2 (f : Nat → Nat) : List.map f ∘ List.map f ∘ List.map f = List.map (f ∘ f ∘ f) := by
  simp

attribute [simp] map_map

theorem ex3 (f : Nat → Nat) (xs : List Nat) : (xs.map f |>.map f |>.map f) = xs.map (fun x => f (f (f x))) := by
  simp [Function.comp]
