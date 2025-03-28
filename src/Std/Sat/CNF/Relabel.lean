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
Change the literal type in a `Clause` from `α` to `β` by using `r`.
-/
def relabel (r : α → β) (c : Clause α) : Clause β := c.map (fun (i, n) => (r i, n))

@[simp] theorem eval_relabel {r : α → β} {a : β → Bool} {c : Clause α} :
    (relabel r c).eval a = c.eval (a ∘ r) := by
  induction c <;> simp_all [relabel]

@[simp] theorem relabel_id' : relabel (id : α → α) = id := by funext; simp [relabel]

theorem relabel_congr {c : Clause α} {r1 r2 : α → β} (hw : ∀ v, Mem v c → r1 v = r2 v) :
    relabel r1 c = relabel r2 c := by
  simp only [relabel]
  rw [List.map_congr_left]
  intro ⟨v, p⟩ h
  congr
  apply hw _ (mem_of h)

-- We need the unapplied equality later.
@[simp] theorem relabel_relabel' : relabel r1 ∘ relabel r2 = relabel (r1 ∘ r2) := by
  funext i
  simp only [Function.comp_apply, relabel, List.map_map]
  rfl

end Clause

/-! ### Relabelling

It is convenient to be able to construct a CNF using a more complicated literal type,
but eventually we need to embed in `Nat`.
-/

/--
Change the literal type in a `CNF` formula from `α` to `β` by using `r`.
-/
def relabel (r : α → β) (f : CNF α) : CNF β := f.map (Clause.relabel r)

@[simp] theorem relabel_nil {r : α → β} : relabel r [] = [] := by simp [relabel]
@[simp] theorem relabel_cons {r : α → β} : relabel r (c :: f) = (c.relabel r) :: relabel r f := by
  simp [relabel]

@[simp] theorem eval_relabel (r : α → β) (a : β → Bool) (f : CNF α) :
    (relabel r f).eval a = f.eval (a ∘ r) := by
  induction f <;> simp_all

@[simp] theorem relabel_append : relabel r (f1 ++ f2) = relabel r f1 ++ relabel r f2 :=
  List.map_append

@[simp] theorem relabel_relabel : relabel r1 (relabel r2 f) = relabel (r1 ∘ r2) f := by
  simp only [relabel, List.map_map, Clause.relabel_relabel']

@[simp] theorem relabel_id : relabel id x = x := by simp [relabel]

theorem relabel_congr {f : CNF α} {r1 r2 : α → β} (hw : ∀ v, Mem v f → r1 v = r2 v) :
    relabel r1 f = relabel r2 f := by
  dsimp only [relabel]
  rw [List.map_congr_left]
  intro c h
  apply Clause.relabel_congr
  intro v m
  exact hw _ (mem_of h m)

theorem sat_relabel {f : CNF α} (h : Sat (r1 ∘ r2) f) : Sat r1 (relabel r2 f) := by
  simp_all [sat_def]

theorem unsat_relabel {f : CNF α} (r : α → β) (h : Unsat f) :
    Unsat (relabel r f) := by
  simp_all [unsat_def]

theorem nonempty_or_impossible (f : CNF α) : Nonempty α ∨ ∃ n, f = List.replicate n [] := by
  induction f with
  | nil => exact Or.inr ⟨0, rfl⟩
  | cons c x ih => match c with
    | [] => cases ih with
      | inl h => left; exact h
      | inr h =>
        obtain ⟨n, rfl⟩ := h
        right
        exact ⟨n + 1, rfl⟩
    | ⟨a, b⟩ :: c => exact Or.inl ⟨a⟩

theorem unsat_relabel_iff {f : CNF α} {r : α → β}
    (hw : ∀ {v1 v2}, Mem v1 f → Mem v2 f → r v1 = r v2 → v1 = v2) :
    Unsat (relabel r f) ↔ Unsat f := by
  rcases nonempty_or_impossible f with (⟨⟨a₀⟩⟩ | ⟨n, rfl⟩)
  · refine ⟨fun h => ?_, unsat_relabel r⟩
    have em := Classical.propDecidable
    let g : β → α := fun b =>
      if h : ∃ a, Mem a f ∧ r a = b then h.choose else a₀
    have h' := unsat_relabel g h
    suffices w : relabel g (relabel r f) = f by
      rwa [w] at h'
    have : ∀ a, Mem a f → g (r a) = a := by
      intro v h
      dsimp [g]
      rw [dif_pos ⟨v, h, rfl⟩]
      apply hw _ h
      · exact (Exists.choose_spec (⟨v, h, rfl⟩ : ∃ a', Mem a' f ∧ r a' = r v)).2
      · exact (Exists.choose_spec (⟨v, h, rfl⟩ : ∃ a', Mem a' f ∧ r a' = r v)).1
    rw [relabel_relabel, relabel_congr, relabel_id]
    exact this
  · cases n <;> simp [unsat_def, List.replicate_succ]

end CNF

end Sat
end Std
