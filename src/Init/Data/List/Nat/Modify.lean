/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/

module

prelude
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Erase

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/-! ### modifyHead -/

@[simp, grind =] theorem length_modifyHead {f : α → α} {l : List α} : (l.modifyHead f).length = l.length := by
  cases l <;> simp [modifyHead]

theorem modifyHead_eq_set [Inhabited α] (f : α → α) (l : List α) :
    l.modifyHead f = l.set 0 (f (l[0]?.getD default)) := by cases l <;> simp [modifyHead]

@[simp] theorem modifyHead_eq_nil_iff {f : α → α} {l : List α} :
    l.modifyHead f = [] ↔ l = [] := by cases l <;> simp [modifyHead]

@[simp, grind =] theorem modifyHead_modifyHead {l : List α} {f g : α → α} :
    (l.modifyHead f).modifyHead g = l.modifyHead (g ∘ f) := by cases l <;> simp [modifyHead]

@[grind =]
theorem getElem_modifyHead {l : List α} {f : α → α} {i} (h : i < (l.modifyHead f).length) :
    (l.modifyHead f)[i] = if h' : i = 0 then f (l[0]'(by simp at h; omega)) else l[i]'(by simpa using h) := by
  cases l with
  | nil => simp at h
  | cons hd tl => cases i <;> simp

@[simp] theorem getElem_modifyHead_zero {l : List α} {f : α → α} {h} :
    (l.modifyHead f)[0] = f (l[0]'(by simpa using h)) := by simp [getElem_modifyHead]

@[simp] theorem getElem_modifyHead_succ {l : List α} {f : α → α} {n} (h : n + 1 < (l.modifyHead f).length) :
    (l.modifyHead f)[n + 1] = l[n + 1]'(by simpa using h) := by simp [getElem_modifyHead]

@[grind =]
theorem getElem?_modifyHead {l : List α} {f : α → α} {i} :
    (l.modifyHead f)[i]? = if i = 0 then l[i]?.map f else l[i]? := by
  cases l with
  | nil => simp
  | cons hd tl => cases i <;> simp

@[simp] theorem getElem?_modifyHead_zero {l : List α} {f : α → α} :
    (l.modifyHead f)[0]? = l[0]?.map f := by simp [getElem?_modifyHead]

@[simp] theorem getElem?_modifyHead_succ {l : List α} {f : α → α} {n} :
    (l.modifyHead f)[n + 1]? = l[n + 1]? := by simp [getElem?_modifyHead]

@[simp, grind =] theorem head_modifyHead (f : α → α) (l : List α) (h) :
    (l.modifyHead f).head h = f (l.head (by simpa using h)) := by
  cases l with
  | nil => simp at h
  | cons hd tl => simp

@[simp, grind =] theorem head?_modifyHead {l : List α} {f : α → α} :
    (l.modifyHead f).head? = l.head?.map f := by cases l <;> simp

@[simp, grind =] theorem tail_modifyHead {f : α → α} {l : List α} :
    (l.modifyHead f).tail = l.tail := by cases l <;> simp

@[simp, grind =] theorem take_modifyHead {f : α → α} {l : List α} {i} :
    (l.modifyHead f).take i = (l.take i).modifyHead f := by
  cases l <;> cases i <;> simp

@[simp] theorem drop_modifyHead_of_pos {f : α → α} {l : List α} {i} (h : 0 < i) :
    (l.modifyHead f).drop i = l.drop i := by
  cases l <;> cases i <;> simp_all

@[grind =]
theorem eraseIdx_modifyHead_zero {f : α → α} {l : List α} :
    (l.modifyHead f).eraseIdx 0 = l.eraseIdx 0 := by simp

@[simp] theorem eraseIdx_modifyHead_of_pos {f : α → α} {l : List α} {i} (h : 0 < i) :
    (l.modifyHead f).eraseIdx i = (l.eraseIdx i).modifyHead f := by cases l <;> cases i <;> simp_all

@[simp] theorem modifyHead_id : modifyHead (id : α → α) = id := by funext l; cases l <;> simp

@[simp, grind _=_] theorem modifyHead_dropLast {l : List α} {f : α → α} :
    l.dropLast.modifyHead f = (l.modifyHead f).dropLast := by
  rcases l with _|⟨a, l⟩
  · simp
  · rcases l with _|⟨b, l⟩ <;> simp

/-! ### modifyTailIdx -/

@[simp] theorem modifyTailIdx_id : ∀ i (l : List α), l.modifyTailIdx i id = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | n+1, a :: l => congrArg (cons a) (modifyTailIdx_id n l)

theorem eraseIdx_eq_modifyTailIdx : ∀ i (l : List α), eraseIdx l i = l.modifyTailIdx i tail
  | 0, l => by cases l <;> rfl
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (cons _) (eraseIdx_eq_modifyTailIdx _ _)

@[simp, grind =] theorem length_modifyTailIdx (f : List α → List α) (H : ∀ l, (f l).length = l.length) :
    ∀ (l : List α) i, (l.modifyTailIdx i f).length = l.length
  | _, 0 => H _
  | [], _+1 => rfl
  | _ :: _, _+1 => congrArg (·+1) (length_modifyTailIdx _ H _ _)

theorem modifyTailIdx_add (f : List α → List α) (i) (l₁ l₂ : List α) :
    (l₁ ++ l₂).modifyTailIdx (l₁.length + i) f = l₁ ++ l₂.modifyTailIdx i f := by
  induction l₁ <;> simp [*, Nat.succ_add]

theorem modifyTailIdx_eq_take_drop (f : List α → List α) (H : f [] = []) :
    ∀ (l : List α) i, l.modifyTailIdx i f = l.take i ++ f (l.drop i)
  | _, 0 => rfl
  | [], _ + 1 => H.symm
  | b :: l, i + 1 => congrArg (cons b) (modifyTailIdx_eq_take_drop f H l i)

theorem exists_of_modifyTailIdx (f : List α → List α) {i} {l : List α} (h : i ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = i ∧ l.modifyTailIdx i f = l₁ ++ f l₂ := by
  obtain ⟨l₁, l₂, rfl, rfl⟩ : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = i :=
    ⟨_, _, (take_append_drop i l).symm, length_take_of_le h⟩
  exact ⟨l₁, l₂, rfl, rfl, modifyTailIdx_add f 0 l₁ l₂⟩

theorem modifyTailIdx_modifyTailIdx {f g : List α → List α} (i : Nat) :
    ∀ (j) (l : List α),
      (l.modifyTailIdx j f).modifyTailIdx (i + j) g =
        l.modifyTailIdx j (fun l => (f l).modifyTailIdx i g)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => congrArg (List.cons a) (modifyTailIdx_modifyTailIdx i n l)

theorem modifyTailIdx_modifyTailIdx_le {f g : List α → List α} (i j : Nat) (l : List α)
    (h : j ≤ i) :
    (l.modifyTailIdx j f).modifyTailIdx i g =
      l.modifyTailIdx j (fun l => (f l).modifyTailIdx (i - j) g) := by
  rcases Nat.exists_eq_add_of_le h with ⟨m, rfl⟩
  rw [Nat.add_comm, modifyTailIdx_modifyTailIdx, Nat.add_sub_cancel]

theorem modifyTailIdx_modifyTailIdx_self {f g : List α → List α} (i : Nat) (l : List α) :
    (l.modifyTailIdx i f).modifyTailIdx i g = l.modifyTailIdx i (g ∘ f) := by
  rw [modifyTailIdx_modifyTailIdx_le i i l (Nat.le_refl i), Nat.sub_self]; rfl

/-! ### modify -/

@[simp, grind =] theorem modify_nil (f : α → α) (i) : [].modify i f = [] := by cases i <;> rfl

@[simp] theorem modify_zero_cons (f : α → α) (a : α) (l : List α) :
    (a :: l).modify 0 f = f a :: l := rfl

@[simp] theorem modify_succ_cons (f : α → α) (a : α) (l : List α) (i) :
    (a :: l).modify (i + 1) f = a :: l.modify i f := rfl

@[grind =]
theorem modify_cons {f : α → α} {a : α} {l : List α} {i : Nat} :
    (a :: l).modify i f =
      if i = 0 then f a :: l else a :: l.modify (i - 1) f := by
  split <;> rename_i h
  · subst h
    simp
  · match i, h with | i + 1, _ => simp

theorem modifyHead_eq_modify_zero (f : α → α) (l : List α) :
    l.modifyHead f = l.modify 0 f := by cases l <;> simp

@[simp] theorem modify_eq_nil_iff {f : α → α} {i} {l : List α} :
    l.modify i f = [] ↔ l = [] := by cases l <;> cases i <;> simp

@[grind =] theorem getElem?_modify (f : α → α) :
    ∀ i (l : List α) j, (l.modify i f)[j]? = (fun a => if i = j then f a else a) <$> l[j]?
  | n, l, 0 => by cases l <;> cases n <;> simp
  | n, [], _+1 => by cases n <;> rfl
  | 0, _ :: l, j+1 => by cases h : l[j]? <;> simp [h, modify, j.succ_ne_zero.symm]
  | i+1, a :: l, j+1 => by
    simp only [modify_succ_cons, getElem?_cons_succ, Nat.reduceEqDiff, Option.map_eq_map]
    refine (getElem?_modify f i l j).trans ?_
    cases h' : l[j]? <;> by_cases h : i = j <;>
      simp [h, if_pos, if_neg, Option.map, mt Nat.succ.inj, not_false_iff, h']

@[simp, grind =] theorem length_modify (f : α → α) : ∀ (l : List α) i, (l.modify i f).length = l.length :=
  length_modifyTailIdx _ fun l => by cases l <;> rfl

@[simp] theorem getElem?_modify_eq (f : α → α) (i) (l : List α) :
    (l.modify i f)[i]? = f <$> l[i]? := by
  simp only [getElem?_modify, if_pos]

@[simp] theorem getElem?_modify_ne (f : α → α) {i j} (l : List α) (h : i ≠ j) :
    (l.modify i f)[j]? = l[j]? := by
  simp only [getElem?_modify, if_neg h, id_map']

@[grind =] theorem getElem_modify (f : α → α) (i) (l : List α) (j) (h : j < (l.modify i f).length) :
    (l.modify i f)[j] =
      if i = j then f (l[j]'(by simp at h; omega)) else l[j]'(by simp at h; omega) := by
  rw [getElem_eq_iff, getElem?_modify]
  simp at h
  simp [h]

@[simp] theorem getElem_modify_eq (f : α → α) (i) (l : List α) (h) :
    (l.modify i f)[i] = f (l[i]'(by simpa using h)) := by simp [getElem_modify]

@[simp] theorem getElem_modify_ne (f : α → α) {i j} (l : List α) (h : i ≠ j) (h') :
    (l.modify i f)[j] = l[j]'(by simpa using h') := by simp [getElem_modify, h]

theorem modify_eq_self {f : α → α} {i} {l : List α} (h : l.length ≤ i) :
    l.modify i f = l := by
  apply ext_getElem
  · simp
  · intro m h₁ h₂
    simp only [getElem_modify, ite_eq_right_iff]
    intro h
    omega

@[grind =]
theorem modify_modify_eq (f g : α → α) (i) (l : List α) :
    (l.modify i f).modify i g = l.modify i (g ∘ f) := by
  apply ext_getElem
  · simp
  · intro m h₁ h₂
    simp only [getElem_modify, Function.comp_apply]
    split <;> simp

theorem modify_modify_ne (f g : α → α) {i j} (l : List α) (h : i ≠ j) :
    (l.modify i f).modify j g = (l.modify j g).modify i f := by
  apply ext_getElem
  · simp
  · intro m' h₁ h₂
    simp only [getElem_modify, getElem_modify_ne, h₂]
    split <;> split <;> first | rfl | omega

theorem modify_eq_set [Inhabited α] (f : α → α) (i) (l : List α) :
    l.modify i f = l.set i (f (l[i]?.getD default)) := by
  apply ext_getElem
  · simp
  · intro m h₁ h₂
    simp [getElem_modify, getElem_set, h₂]
    split <;> rename_i h
    · subst h
      simp only [length_modify] at h₁
      simp [h₁]
    · rfl

theorem modify_eq_take_drop (f : α → α) :
    ∀ (l : List α) i, l.modify i f = l.take i ++ modifyHead f (l.drop i) :=
  modifyTailIdx_eq_take_drop _ rfl

theorem modify_eq_take_cons_drop {f : α → α} {i} {l : List α} (h : i < l.length) :
    l.modify i f = l.take i ++ f l[i] :: l.drop (i + 1) := by
  rw [modify_eq_take_drop, drop_eq_getElem_cons h]; rfl

theorem exists_of_modify (f : α → α) {i} {l : List α} (h : i < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = i ∧ l.modify i f = l₁ ++ f a :: l₂ :=
  match exists_of_modifyTailIdx _ (Nat.le_of_lt h) with
  | ⟨_, _::_, eq, hl, H⟩ => ⟨_, _, _, eq, hl, H⟩
  | ⟨_, [], eq, hl, _⟩ => nomatch Nat.ne_of_gt h (eq ▸ append_nil _ ▸ hl)

@[simp] theorem modify_id (i) (l : List α) : l.modify i id = l := by
  simp [modify]

@[grind _=_]
theorem take_modify (f : α → α) (i j) (l : List α) :
    (l.modify i f).take j = (l.take j).modify i f := by
  induction j generalizing l i with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons hd tl =>
      cases i with
      | zero => simp
      | succ i => simp [ih]

@[grind =]
theorem drop_modify_of_lt (f : α → α) (i j) (l : List α) (h : i < j) :
    (l.modify i f).drop j = l.drop j := by
  apply ext_getElem
  · simp
  · intro m' h₁ h₂
    simp only [getElem_drop, getElem_modify, ite_eq_right_iff]
    intro h'
    omega

@[grind =]
theorem drop_modify_of_ge (f : α → α) (i j) (l : List α) (h : i ≥ j) :
    (l.modify i f).drop j = (l.drop j).modify (i - j) f  := by
  apply ext_getElem
  · simp
  · intro m' h₁ h₂
    simp [getElem_drop, getElem_modify, ite_eq_right_iff]
    split <;> split <;> first | rfl | omega

theorem eraseIdx_modify_of_eq (f : α → α) (i) (l : List α) :
    (l.modify i f).eraseIdx i = l.eraseIdx i := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro m h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    split <;> split <;> first | rfl | omega

theorem eraseIdx_modify_of_lt (f : α → α) (i j) (l : List α) (h : j < i) :
    (l.modify i f).eraseIdx j = (l.eraseIdx j).modify (i - 1) f := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro k h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    by_cases h' : i - 1 = k
    repeat' split
    all_goals (first | rfl | omega)

theorem eraseIdx_modify_of_gt (f : α → α) (i j) (l : List α) (h : j > i) :
    (l.modify i f).eraseIdx j = (l.eraseIdx j).modify i f := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro k h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    by_cases h' : i = k
    repeat' split
    all_goals (first | rfl | omega)

theorem modify_eraseIdx_of_lt (f : α → α) (i j) (l : List α) (h : j < i) :
    (l.eraseIdx i).modify j f = (l.modify j f).eraseIdx i := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro k h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    by_cases h' : j = k + 1
    repeat' split
    all_goals (first | rfl | omega)

theorem modify_eraseIdx_of_ge (f : α → α) (i j) (l : List α) (h : j ≥ i) :
    (l.eraseIdx i).modify j f = (l.modify (j + 1) f).eraseIdx i := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro k h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    by_cases h' : j + 1 = k + 1
    repeat' split
    all_goals (first | rfl | omega)

end List
