/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SimpLemmas
import Init.NotationExtra

namespace Prod

instance [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] : LawfulBEq (α × β) where
  eq_of_beq {a b} (h : a.1 == b.1 && a.2 == b.2) := by
    cases a; cases b
    refine congr (congrArg _ (eq_of_beq ?_)) (eq_of_beq ?_) <;> simp_all
  rfl {a} := by cases a; simp [BEq.beq, LawfulBEq.rfl]

@[simp]
protected theorem «forall» {p : α × β → Prop} : (∀ x, p x) ↔ ∀ a b, p (a, b) :=
  ⟨fun h a b ↦ h (a, b), fun h ⟨a, b⟩ ↦ h a b⟩

@[simp]
protected theorem «exists» {p : α × β → Prop} : (∃ x, p x) ↔ ∃ a b, p (a, b) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩

@[simp] theorem map_id : Prod.map (@id α) (@id β) = id := rfl

@[simp] theorem map_id' : Prod.map (fun a : α => a) (fun b : β => b) = fun x ↦ x := rfl

/--
Composing a `Prod.map` with another `Prod.map` is equal to
a single `Prod.map` of composed functions.
-/
theorem map_comp_map (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
    Prod.map g g' ∘ Prod.map f f' = Prod.map (g ∘ f) (g' ∘ f') :=
  rfl

/--
Composing a `Prod.map` with another `Prod.map` is equal to
a single `Prod.map` of composed functions, fully applied.
-/
theorem map_map (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) (x : α × γ) :
    Prod.map g g' (Prod.map f f' x) = Prod.map (g ∘ f) (g' ∘ f') x :=
  rfl

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap : α × β → β × α := fun p => (p.2, p.1)

@[simp]
theorem swap_swap : ∀ x : α × β, swap (swap x) = x
  | ⟨_, _⟩ => rfl

@[simp]
theorem fst_swap {p : α × β} : (swap p).1 = p.2 :=
  rfl

@[simp]
theorem snd_swap {p : α × β} : (swap p).2 = p.1 :=
  rfl

@[simp]
theorem swap_prod_mk {a : α} {b : β} : swap (a, b) = (b, a) :=
  rfl

@[simp]
theorem swap_swap_eq : swap ∘ swap = @id (α × β) :=
  funext swap_swap

@[simp]
theorem swap_inj {p q : α × β} : swap p = swap q ↔ p = q := by
  cases p; cases q; simp [and_comm]

/--
For two functions `f` and `g`, the composition of `Prod.map f g` with `Prod.swap`
is equal to the composition of `Prod.swap` with `Prod.map g f`.
-/
theorem map_comp_swap (f : α → β) (g : γ → δ) :
    Prod.map f g ∘ Prod.swap = Prod.swap ∘ Prod.map g f := rfl

end Prod
