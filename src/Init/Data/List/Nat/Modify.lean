/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/

prelude
import Init.Data.List.Nat.TakeDrop

namespace List

/-! ### modifyHead -/

@[simp] theorem modifyHead_modifyHead (l : List α) (f g : α → α) :
    (l.modifyHead f).modifyHead g = l.modifyHead (g ∘ f) := by cases l <;> simp [modifyHead]

/-! ### modify -/

@[simp] theorem modify_nil (f : α → α) (n) : [].modify f n = [] := by cases n <;> rfl

@[simp] theorem modify_zero_cons (f : α → α) (a : α) (l : List α) :
    (a :: l).modify f 0 = f a :: l := rfl

@[simp] theorem modify_succ_cons (f : α → α) (a : α) (l : List α) (n) :
    (a :: l).modify f (n + 1) = a :: l.modify f n := by rfl

theorem modifyTailIdx_id : ∀ n (l : List α), l.modifyTailIdx id n = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | n+1, a :: l => congrArg (cons a) (modifyTailIdx_id n l)

theorem eraseIdx_eq_modifyTailIdx : ∀ n (l : List α), eraseIdx l n = modifyTailIdx tail n l
  | 0, l => by cases l <;> rfl
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (cons _) (eraseIdx_eq_modifyTailIdx _ _)

theorem getElem?_modify (f : α → α) :
    ∀ n (l : List α) m, (modify f n l)[m]? = (fun a => if n = m then f a else a) <$> l[m]?
  | n, l, 0 => by cases l <;> cases n <;> simp
  | n, [], _+1 => by cases n <;> rfl
  | 0, _ :: l, m+1 => by cases h : l[m]? <;> simp [h, modify, m.succ_ne_zero.symm]
  | n+1, a :: l, m+1 => by
    simp only [modify_succ_cons, getElem?_cons_succ, Nat.reduceEqDiff, Option.map_eq_map]
    refine (getElem?_modify f n l m).trans ?_
    cases h' : l[m]? <;> by_cases h : n = m <;>
      simp [h, if_pos, if_neg, Option.map, mt Nat.succ.inj, not_false_iff, h']

@[simp] theorem length_modifyTailIdx (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyTailIdx f n l) = length l
  | 0, _ => H _
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (·+1) (length_modifyTailIdx _ H _ _)

theorem modifyTailIdx_add (f : List α → List α) (n) (l₁ l₂ : List α) :
    modifyTailIdx f (l₁.length + n) (l₁ ++ l₂) = l₁ ++ modifyTailIdx f n l₂ := by
  induction l₁ <;> simp [*, Nat.succ_add]

@[simp] theorem length_modify (f : α → α) : ∀ n l, length (modify f n l) = length l :=
  length_modifyTailIdx _ fun l => by cases l <;> rfl

@[simp] theorem getElem?_modify_eq (f : α → α) (n) (l : List α) :
    (modify f n l)[n]? = f <$> l[n]? := by
  simp only [getElem?_modify, if_pos]

@[simp] theorem getElem?_modify_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) :
    (modify f m l)[n]? = l[n]? := by
  simp only [getElem?_modify, if_neg h, id_map']

theorem getElem_modify (f : α → α) (n) (l : List α) (m) (h : m < (modify f n l).length) :
    (modify f n l)[m] =
      if n = m then f (l[m]'(by simp at h; omega)) else l[m]'(by simp at h; omega) := by
  rw [getElem_eq_iff, getElem?_modify]
  simp at h
  simp [h]

theorem modifyTailIdx_eq_take_drop (f : List α → List α) (H : f [] = []) :
    ∀ n l, modifyTailIdx f n l = take n l ++ f (drop n l)
  | 0, _ => rfl
  | _ + 1, [] => H.symm
  | n + 1, b :: l => congrArg (cons b) (modifyTailIdx_eq_take_drop f H n l)

theorem modify_eq_take_drop (f : α → α) :
    ∀ n l, modify f n l = take n l ++ modifyHead f (drop n l) :=
  modifyTailIdx_eq_take_drop _ rfl

theorem modify_eq_take_cons_drop (f : α → α) {n l} (h : n < length l) :
    modify f n l = take n l ++ f l[n] :: drop (n + 1) l := by
  rw [modify_eq_take_drop, drop_eq_getElem_cons h]; rfl

theorem exists_of_modifyTailIdx (f : List α → List α) {n} {l : List α} (h : n ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n ∧ modifyTailIdx f n l = l₁ ++ f l₂ :=
  have ⟨_, _, eq, hl⟩ : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n :=
    ⟨_, _, (take_append_drop n l).symm, length_take_of_le h⟩
  ⟨_, _, eq, hl, hl ▸ eq ▸ modifyTailIdx_add (n := 0) ..⟩

theorem exists_of_modify (f : α → α) {n} {l : List α} (h : n < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n ∧ modify f n l = l₁ ++ f a :: l₂ :=
  match exists_of_modifyTailIdx _ (Nat.le_of_lt h) with
  | ⟨_, _::_, eq, hl, H⟩ => ⟨_, _, _, eq, hl, H⟩
  | ⟨_, [], eq, hl, _⟩ => nomatch Nat.ne_of_gt h (eq ▸ append_nil _ ▸ hl)

end List
