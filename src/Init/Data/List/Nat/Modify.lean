/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/

prelude
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Erase

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/-! ### modifyHead -/

@[simp] theorem length_modifyHead {f : α → α} {l : List α} : (l.modifyHead f).length = l.length := by
  cases l <;> simp [modifyHead]

theorem modifyHead_eq_set [Inhabited α] (f : α → α) (l : List α) :
    l.modifyHead f = l.set 0 (f (l[0]?.getD default)) := by cases l <;> simp [modifyHead]

@[simp] theorem modifyHead_eq_nil_iff {f : α → α} {l : List α} :
    l.modifyHead f = [] ↔ l = [] := by cases l <;> simp [modifyHead]

@[simp] theorem modifyHead_modifyHead {l : List α} {f g : α → α} :
    (l.modifyHead f).modifyHead g = l.modifyHead (g ∘ f) := by cases l <;> simp [modifyHead]

theorem getElem_modifyHead {l : List α} {f : α → α} {i} (h : i < (l.modifyHead f).length) :
    (l.modifyHead f)[i] = if h' : i = 0 then f (l[0]'(by simp at h; omega)) else l[i]'(by simpa using h) := by
  cases l with
  | nil => simp at h
  | cons hd tl => cases i <;> simp

@[simp] theorem getElem_modifyHead_zero {l : List α} {f : α → α} {h} :
    (l.modifyHead f)[0] = f (l[0]'(by simpa using h)) := by simp [getElem_modifyHead]

@[simp] theorem getElem_modifyHead_succ {l : List α} {f : α → α} {n} (h : n + 1 < (l.modifyHead f).length) :
    (l.modifyHead f)[n + 1] = l[n + 1]'(by simpa using h) := by simp [getElem_modifyHead]

theorem getElem?_modifyHead {l : List α} {f : α → α} {i} :
    (l.modifyHead f)[i]? = if i = 0 then l[i]?.map f else l[i]? := by
  cases l with
  | nil => simp
  | cons hd tl => cases i <;> simp

@[simp] theorem getElem?_modifyHead_zero {l : List α} {f : α → α} :
    (l.modifyHead f)[0]? = l[0]?.map f := by simp [getElem?_modifyHead]

@[simp] theorem getElem?_modifyHead_succ {l : List α} {f : α → α} {n} :
    (l.modifyHead f)[n + 1]? = l[n + 1]? := by simp [getElem?_modifyHead]

@[simp] theorem head_modifyHead (f : α → α) (l : List α) (h) :
    (l.modifyHead f).head h = f (l.head (by simpa using h)) := by
  cases l with
  | nil => simp at h
  | cons hd tl => simp

@[simp] theorem head?_modifyHead {l : List α} {f : α → α} :
    (l.modifyHead f).head? = l.head?.map f := by cases l <;> simp

@[simp] theorem tail_modifyHead {f : α → α} {l : List α} :
    (l.modifyHead f).tail = l.tail := by cases l <;> simp

@[simp] theorem take_modifyHead {f : α → α} {l : List α} {i} :
    (l.modifyHead f).take i = (l.take i).modifyHead f := by
  cases l <;> cases i <;> simp

@[simp] theorem drop_modifyHead_of_pos {f : α → α} {l : List α} {i} (h : 0 < i) :
    (l.modifyHead f).drop i = l.drop i := by
  cases l <;> cases i <;> simp_all

theorem eraseIdx_modifyHead_zero {f : α → α} {l : List α} :
    (l.modifyHead f).eraseIdx 0 = l.eraseIdx 0 := by simp

@[simp] theorem eraseIdx_modifyHead_of_pos {f : α → α} {l : List α} {i} (h : 0 < i) :
    (l.modifyHead f).eraseIdx i = (l.eraseIdx i).modifyHead f := by cases l <;> cases i <;> simp_all

@[simp] theorem modifyHead_id : modifyHead (id : α → α) = id := by funext l; cases l <;> simp

@[simp] theorem modifyHead_dropLast {l : List α} {f : α → α} :
    l.dropLast.modifyHead f = (l.modifyHead f).dropLast := by
  rcases l with _|⟨a, l⟩
  · simp
  · rcases l with _|⟨b, l⟩ <;> simp

/-! ### modifyTailIdx -/

@[simp] theorem modifyTailIdx_id : ∀ n (l : List α), l.modifyTailIdx id n = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | n+1, a :: l => congrArg (cons a) (modifyTailIdx_id n l)

theorem eraseIdx_eq_modifyTailIdx : ∀ i (l : List α), eraseIdx l i = modifyTailIdx tail i l
  | 0, l => by cases l <;> rfl
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (cons _) (eraseIdx_eq_modifyTailIdx _ _)

@[simp] theorem length_modifyTailIdx (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyTailIdx f n l) = length l
  | 0, _ => H _
  | _+1, [] => rfl
  | _+1, _ :: _ => congrArg (·+1) (length_modifyTailIdx _ H _ _)

theorem modifyTailIdx_add (f : List α → List α) (n) (l₁ l₂ : List α) :
    modifyTailIdx f (l₁.length + n) (l₁ ++ l₂) = l₁ ++ modifyTailIdx f n l₂ := by
  induction l₁ <;> simp [*, Nat.succ_add]

theorem modifyTailIdx_eq_take_drop (f : List α → List α) (H : f [] = []) :
    ∀ i l, modifyTailIdx f i l = take i l ++ f (drop i l)
  | 0, _ => rfl
  | _ + 1, [] => H.symm
  | n + 1, b :: l => congrArg (cons b) (modifyTailIdx_eq_take_drop f H n l)

theorem exists_of_modifyTailIdx (f : List α → List α) {n} {l : List α} (h : n ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n ∧ modifyTailIdx f n l = l₁ ++ f l₂ :=
  have ⟨_, _, eq, hl⟩ : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n :=
    ⟨_, _, (take_append_drop n l).symm, length_take_of_le h⟩
  ⟨_, _, eq, hl, hl ▸ eq ▸ modifyTailIdx_add (n := 0) ..⟩

theorem modifyTailIdx_modifyTailIdx {f g : List α → List α} (m : Nat) :
    ∀ (n) (l : List α),
      (l.modifyTailIdx f n).modifyTailIdx g (m + n) =
        l.modifyTailIdx (fun l => (f l).modifyTailIdx g m) n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => congrArg (List.cons a) (modifyTailIdx_modifyTailIdx m n l)

theorem modifyTailIdx_modifyTailIdx_le {f g : List α → List α} (m n : Nat) (l : List α)
    (h : n ≤ m) :
    (l.modifyTailIdx f n).modifyTailIdx g m =
      l.modifyTailIdx (fun l => (f l).modifyTailIdx g (m - n)) n := by
  rcases Nat.exists_eq_add_of_le h with ⟨m, rfl⟩
  rw [Nat.add_comm, modifyTailIdx_modifyTailIdx, Nat.add_sub_cancel]

theorem modifyTailIdx_modifyTailIdx_self {f g : List α → List α} (n : Nat) (l : List α) :
    (l.modifyTailIdx f n).modifyTailIdx g n = l.modifyTailIdx (g ∘ f) n := by
  rw [modifyTailIdx_modifyTailIdx_le n n l (Nat.le_refl n), Nat.sub_self]; rfl

/-! ### modify -/

@[simp] theorem modify_nil (f : α → α) (i) : [].modify f i = [] := by cases i <;> rfl

@[simp] theorem modify_zero_cons (f : α → α) (a : α) (l : List α) :
    (a :: l).modify f 0 = f a :: l := rfl

@[simp] theorem modify_succ_cons (f : α → α) (a : α) (l : List α) (i) :
    (a :: l).modify f (i + 1) = a :: l.modify f i := by rfl

theorem modifyHead_eq_modify_zero (f : α → α) (l : List α) :
    l.modifyHead f = l.modify f 0 := by cases l <;> simp

@[simp] theorem modify_eq_nil_iff {f : α → α} {i} {l : List α} :
    l.modify f i = [] ↔ l = [] := by cases l <;> cases i <;> simp

theorem getElem?_modify (f : α → α) :
    ∀ i (l : List α) j, (modify f i l)[j]? = (fun a => if i = j then f a else a) <$> l[j]?
  | n, l, 0 => by cases l <;> cases n <;> simp
  | n, [], _+1 => by cases n <;> rfl
  | 0, _ :: l, j+1 => by cases h : l[j]? <;> simp [h, modify, j.succ_ne_zero.symm]
  | i+1, a :: l, j+1 => by
    simp only [modify_succ_cons, getElem?_cons_succ, Nat.reduceEqDiff, Option.map_eq_map]
    refine (getElem?_modify f i l j).trans ?_
    cases h' : l[j]? <;> by_cases h : i = j <;>
      simp [h, if_pos, if_neg, Option.map, mt Nat.succ.inj, not_false_iff, h']

@[simp] theorem length_modify (f : α → α) : ∀ i l, length (modify f i l) = length l :=
  length_modifyTailIdx _ fun l => by cases l <;> rfl

@[simp] theorem getElem?_modify_eq (f : α → α) (i) (l : List α) :
    (modify f i l)[i]? = f <$> l[i]? := by
  simp only [getElem?_modify, if_pos]

@[simp] theorem getElem?_modify_ne (f : α → α) {i j} (l : List α) (h : i ≠ j) :
    (modify f i l)[j]? = l[j]? := by
  simp only [getElem?_modify, if_neg h, id_map']

theorem getElem_modify (f : α → α) (i) (l : List α) (j) (h : j < (modify f i l).length) :
    (modify f i l)[j] =
      if i = j then f (l[j]'(by simp at h; omega)) else l[j]'(by simp at h; omega) := by
  rw [getElem_eq_iff, getElem?_modify]
  simp at h
  simp [h]

@[simp] theorem getElem_modify_eq (f : α → α) (i) (l : List α) (h) :
    (modify f i l)[i] = f (l[i]'(by simpa using h)) := by simp [getElem_modify]

@[simp] theorem getElem_modify_ne (f : α → α) {i j} (l : List α) (h : i ≠ j) (h') :
    (modify f i l)[j] = l[j]'(by simpa using h') := by simp [getElem_modify, h]

theorem modify_eq_self {f : α → α} {i} {l : List α} (h : l.length ≤ i) :
    l.modify f i = l := by
  apply ext_getElem
  · simp
  · intro m h₁ h₂
    simp only [getElem_modify, ite_eq_right_iff]
    intro h
    omega

theorem modify_modify_eq (f g : α → α) (i) (l : List α) :
    (modify f i l).modify g i = modify (g ∘ f) i l := by
  apply ext_getElem
  · simp
  · intro m h₁ h₂
    simp only [getElem_modify, Function.comp_apply]
    split <;> simp

theorem modify_modify_ne (f g : α → α) {i j} (l : List α) (h : i ≠ j) :
    (modify f i l).modify g j = (l.modify g j).modify f i := by
  apply ext_getElem
  · simp
  · intro m' h₁ h₂
    simp only [getElem_modify, getElem_modify_ne, h₂]
    split <;> split <;> first | rfl | omega

theorem modify_eq_set [Inhabited α] (f : α → α) (i) (l : List α) :
    modify f i l = l.set i (f (l[i]?.getD default)) := by
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
    ∀ i l, modify f i l = take i l ++ modifyHead f (drop i l) :=
  modifyTailIdx_eq_take_drop _ rfl

theorem modify_eq_take_cons_drop {f : α → α} {i} {l : List α} (h : i < l.length) :
    modify f i l = take i l ++ f l[i] :: drop (i + 1) l := by
  rw [modify_eq_take_drop, drop_eq_getElem_cons h]; rfl

theorem exists_of_modify (f : α → α) {i} {l : List α} (h : i < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = i ∧ modify f i l = l₁ ++ f a :: l₂ :=
  match exists_of_modifyTailIdx _ (Nat.le_of_lt h) with
  | ⟨_, _::_, eq, hl, H⟩ => ⟨_, _, _, eq, hl, H⟩
  | ⟨_, [], eq, hl, _⟩ => nomatch Nat.ne_of_gt h (eq ▸ append_nil _ ▸ hl)

@[simp] theorem modify_id (i) (l : List α) : l.modify id i = l := by
  simp [modify]

theorem take_modify (f : α → α) (i j) (l : List α) :
    (modify f i l).take j = (take j l).modify f i := by
  induction j generalizing l i with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons hd tl =>
      cases i with
      | zero => simp
      | succ i => simp [ih]

theorem drop_modify_of_lt (f : α → α) (i j) (l : List α) (h : i < j) :
    (modify f i l).drop j = l.drop j := by
  apply ext_getElem
  · simp
  · intro m' h₁ h₂
    simp only [getElem_drop, getElem_modify, ite_eq_right_iff]
    intro h'
    omega

theorem drop_modify_of_ge (f : α → α) (i j) (l : List α) (h : i ≥ j) :
    (modify f i l).drop j = modify f (i - j) (drop j l) := by
  apply ext_getElem
  · simp
  · intro m' h₁ h₂
    simp [getElem_drop, getElem_modify, ite_eq_right_iff]
    split <;> split <;> first | rfl | omega

theorem eraseIdx_modify_of_eq (f : α → α) (i) (l : List α) :
    (modify f i l).eraseIdx i = l.eraseIdx i := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro m h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    split <;> split <;> first | rfl | omega

theorem eraseIdx_modify_of_lt (f : α → α) (i j) (l : List α) (h : j < i) :
    (modify f i l).eraseIdx j = (l.eraseIdx j).modify f (i - 1) := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro k h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    by_cases h' : i - 1 = k
    repeat' split
    all_goals (first | rfl | omega)

theorem eraseIdx_modify_of_gt (f : α → α) (i j) (l : List α) (h : j > i) :
    (modify f i l).eraseIdx j = (l.eraseIdx j).modify f i := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro k h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    by_cases h' : i = k
    repeat' split
    all_goals (first | rfl | omega)

theorem modify_eraseIdx_of_lt (f : α → α) (i j) (l : List α) (h : j < i) :
    (l.eraseIdx i).modify f j = (l.modify f j).eraseIdx i := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro k h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    by_cases h' : j = k + 1
    repeat' split
    all_goals (first | rfl | omega)

theorem modify_eraseIdx_of_ge (f : α → α) (i j) (l : List α) (h : j ≥ i) :
    (l.eraseIdx i).modify f j = (l.modify f (j + 1)).eraseIdx i := by
  apply ext_getElem
  · simp [length_eraseIdx]
  · intro k h₁ h₂
    simp only [getElem_eraseIdx, getElem_modify]
    by_cases h' : j + 1 = k + 1
    repeat' split
    all_goals (first | rfl | omega)

end List
