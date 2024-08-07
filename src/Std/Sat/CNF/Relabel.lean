/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Std.Sat.CNF.Basic

namespace Std
namespace Sat

namespace CNF

namespace Clause

/--
Change the literal type in a `Clause` from `α` to `β` by using `f`.
-/
def relabel (f : α → β) (c : Clause α) : Clause β := c.map (fun (i, n) => (f i, n))

@[simp] theorem eval_relabel {f : α → β} {g : β → Bool} {x : Clause α} :
    (relabel f x).eval g = x.eval (g ∘ f) := by
  induction x <;> simp_all [relabel]

@[simp] theorem relabel_id' : relabel (id : α → α) = id := by funext; simp [relabel]

theorem relabel_congr {x : Clause α} {f g : α → β} (w : ∀ a, Mem a x → f a = g a) :
    relabel f x = relabel g x := by
  simp only [relabel]
  rw [List.map_congr_left]
  intro ⟨i, b⟩ h
  congr
  apply w _ (mem_of h)

-- We need the unapplied equality later.
@[simp] theorem relabel_relabel' : relabel f ∘ relabel g = relabel (f ∘ g) := by
  funext i
  simp only [Function.comp_apply, relabel, List.map_map]
  rfl

end Clause

/-! ### Relabelling

It is convenient to be able to construct a CNF using a more complicated literal type,
but eventually we need to embed in `Nat`.
-/

/--
Change the literal type in a `CNF` formula from `α` to `β` by using `f`.
-/
def relabel (f : α → β) (g : CNF α) : CNF β := g.map (Clause.relabel f)

@[simp] theorem eval_relabel (f : α → β) (g : β → Bool) (x : CNF α) :
    (relabel f x).eval g = x.eval (g ∘ f) := by
  induction x <;> simp_all [relabel]

@[simp] theorem relabel_append : relabel f (g ++ h) = relabel f g ++ relabel f h :=
  List.map_append _ _ _

@[simp] theorem relabel_relabel : relabel f (relabel g x) = relabel (f ∘ g) x := by
  simp only [relabel, List.map_map, Clause.relabel_relabel']

@[simp] theorem relabel_id : relabel id x = x := by simp [relabel]

theorem relabel_congr {x : CNF α} {f g : α → β} (w : ∀ a, Mem a x → f a = g a) :
    relabel f x = relabel g x := by
  dsimp only [relabel]
  rw [List.map_congr_left]
  intro c h
  apply Clause.relabel_congr
  intro a m
  exact w _ (mem_of h m)

theorem sat_relabel {x : CNF α} (h : (g ∘ f) ⊨ x) : g ⊨ (relabel f x) := by
  simp_all [(· ⊨ ·)]

theorem unsat_relabel {x : CNF α} (f : α → β) (h : Unsatisfiable α x) :
    Unsatisfiable β (relabel f x) := by
  simp_all [Unsatisfiable, (· ⊨ ·)]

theorem nonempty_or_impossible (x : CNF α) : Nonempty α ∨ ∃ n, x = List.replicate n [] := by
  induction x with
  | nil => exact Or.inr ⟨0, rfl⟩
  | cons c x ih => match c with
    | [] => cases ih with
      | inl h => left; exact h
      | inr h =>
        obtain ⟨n, rfl⟩ := h
        right
        exact ⟨n + 1, rfl⟩
    | ⟨a, b⟩ :: c => exact Or.inl ⟨a⟩

theorem unsat_relabel_iff {x : CNF α} {f : α → β}
    (w : ∀ {a b}, Mem a x → Mem b x → f a = f b → a = b) :
    Unsatisfiable β (relabel f x) ↔ Unsatisfiable α x := by
  rcases nonempty_or_impossible x with (⟨⟨a₀⟩⟩ | ⟨n, rfl⟩)
  · refine ⟨fun h => ?_, unsat_relabel f⟩
    have em := Classical.propDecidable
    let g : β → α := fun b =>
      if h : ∃ a, Mem a x ∧ f a = b then h.choose else a₀
    have h' := unsat_relabel g h
    suffices w : relabel g (relabel f x) = x by
      rwa [w] at h'
    have : ∀ a, Mem a x → g (f a) = a := by
      intro a h
      dsimp [g]
      rw [dif_pos ⟨a, h, rfl⟩]
      apply w _ h
      · exact (Exists.choose_spec (⟨a, h, rfl⟩ : ∃ a', Mem a' x ∧ f a' = f a)).2
      · exact (Exists.choose_spec (⟨a, h, rfl⟩ : ∃ a', Mem a' x ∧ f a' = f a)).1
    rw [relabel_relabel, relabel_congr, relabel_id]
    exact this
  · cases n <;> simp [Unsatisfiable, (· ⊨ ·), relabel, Clause.relabel, List.replicate_succ]

end CNF

end Sat
end Std
