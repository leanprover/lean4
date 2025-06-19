-- Note that `grind_list.lean` uses `reset_grind_attrs%` to clear the grind attributes.
-- This file does not: it is testing the grind attributes in the library.

-- This file follows `Data/List/Lemmas.lean`. Indeed, if we decided `grind` is allowed there,
-- it should be possible to replace proofs there with these.
-- (In some cases, the proofs here are now cheating and directly using the same result from the library,
-- but initially I was avoiding this, but haven't bothered writing `grind [-X]` everywhere.)

-- This file only contains those theorems that can be proved "effortlessly" with `grind`.
-- `tests/lean/grind/experiments/list.lean` contains everything from `Data/List/Lemmas.lean`
-- that still resists `grind`!

open List Nat

namespace Hidden

/-! ### nil -/

theorem nil_eq {α} {xs : List α} : [] = xs ↔ xs = [] := by grind

/-! ### length -/

theorem eq_nil_of_length_eq_zero (_ : length l = 0) : l = [] := by grind [length_eq_zero_iff]

theorem ne_nil_of_length_eq_add_one (_ : length l = n + 1) : l ≠ [] := by grind

theorem ne_nil_of_length_pos (_ : 0 < length l) : l ≠ [] := by grind

theorem length_eq_zero_iff : length l = 0 ↔ l = [] := by grind [length_eq_zero_iff]

theorem eq_nil_iff_length_eq_zero : l = [] ↔ length l = 0 := by grind [length_eq_zero_iff]

theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l := by grind

theorem length_pos_iff {l : List α} : 0 < length l ↔ l ≠ [] := by grind [length_eq_zero_iff]

theorem ne_nil_iff_length_pos {l : List α} : l ≠ [] ↔ 0 < length l := by grind [length_eq_zero_iff]

/-! ### cons -/

theorem cons_ne_nil (a : α) (l : List α) : a :: l ≠ [] := by grind

theorem head_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : h₁ = h₂ := by grind

theorem tail_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : t₁ = t₂ := by grind

theorem cons_inj_right (a : α) {l l' : List α} : a :: l = a :: l' ↔ l = l' := by grind

theorem cons_eq_cons {a b : α} {l l' : List α} : a :: l = b :: l' ↔ a = b ∧ l = l' := by grind

theorem singleton_inj {α : Type _} {a b : α} : [a] = [b] ↔ a = b := by grind

/-! ## L[i] and L[i]? -/

/-! ### `get` and `get?`. -/

theorem get_eq_getElem {l : List α} {i : Fin l.length} : l.get i = l[i.1]'i.2 := by grind

/-! ### getElem! -/

theorem getElem!_eq_getElem?_getD [Inhabited α] {l : List α} {i : Nat} :
    l[i]! = (l[i]?).getD (default : α) := by grind

/-! ### getElem? and getElem -/

theorem getElem?_nil {i : Nat} : ([] : List α)[i]? = none := by grind

theorem getElem_cons {l : List α} (w : i < (a :: l).length) :
    (a :: l)[i] = if h : i = 0 then a else l[i-1]'(by grind) := by
  cases i with grind

theorem getElem?_cons_zero {l : List α} : (a::l)[0]? = some a := by grind

theorem getElem?_cons_succ {l : List α} : (a::l)[i+1]? = l[i]? := by grind

theorem getElem?_cons : (a :: l)[i]? = if i = 0 then some a else l[i-1]? := by
  cases i with grind

theorem getElem_of_eq {l l' : List α} (h : l = l') {i : Nat} (w : i < l.length) :
    l[i] = l'[i]'(h ▸ w) := by grind

theorem getElem?_concat_length {l : List α} {a : α} : (l ++ [a])[l.length]? = some a := by
  grind

/-! ### getD -/

theorem getD_eq_getElem?_getD {l : List α} {i : Nat} {a : α} : getD l i a = (l[i]?).getD a := by
  grind

theorem getD_cons_zero : getD (x :: xs) 0 d = x := by grind
theorem getD_cons_succ : getD (x :: xs) (n + 1) d = getD xs n d := by grind


/-! ### mem -/

-- I've gone back and forth on this one. It's an expensive lemma to instantiate merely because we see `a ∈ l`,
-- so globally it is set up with `grind_pattern length_pos_of_mem => a ∈ l, length l`.
-- While it's quite useful as simply `grind →` in this "very eary theory", it doesn't  seem essential?

section length_pos_of_mem

attribute [local grind →] length_pos_of_mem

theorem not_mem_nil {a : α} : ¬ a ∈ [] := by grind

theorem mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l := by grind

theorem mem_cons_self {a : α} {l : List α} : a ∈ a :: l := by grind

theorem mem_concat_self {xs : List α} {a : α} : a ∈ xs ++ [a] := by grind

theorem mem_append_cons_self : a ∈ xs ++ a :: ys := by grind

theorem eq_append_cons_of_mem {a : α} {xs : List α} (h : a ∈ xs) :
    ∃ as bs, xs = as ++ a :: bs ∧ a ∉ as := by
  induction xs with
  | nil => grind
  | cons x xs ih =>
    simp at h
    cases h with
    | inl h => exact ⟨[], xs, by grind⟩
    | inr h =>
      by_cases h' : a = x
      · exact ⟨[], xs, by grind⟩
      · obtain ⟨as, bs, rfl, h⟩ := ih h
        exact ⟨x :: as, bs, rfl, by grind⟩

theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := by grind

theorem exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
  exists_mem_of_length_pos (by grind [length_eq_zero_iff])

theorem mem_dite_nil_left {x : α} [Decidable p] {l : ¬ p → List α} :
    (x ∈ if h : p then [] else l h) ↔ ∃ h : ¬ p, x ∈ l h := by grind

theorem mem_dite_nil_right {x : α} [Decidable p] {l : p → List α} :
    (x ∈ if h : p then l h else []) ↔ ∃ h : p, x ∈ l h := by grind

theorem mem_ite_nil_left {x : α} [Decidable p] {l : List α} :
    (x ∈ if p then [] else l) ↔ ¬ p ∧ x ∈ l := by grind

theorem mem_ite_nil_right {x : α} [Decidable p] {l : List α} :
    (x ∈ if p then l else []) ↔ p ∧ x ∈ l := by grind

theorem eq_of_mem_singleton : a ∈ [b] → a = b := by grind

theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b := by grind

theorem forall_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∀ x, x ∈ a :: l → p x) ↔ p a ∧ ∀ x, x ∈ l → p x := by grind

theorem forall_mem_ne {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l := by grind

theorem forall_mem_ne' {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a' = a) ↔ a ∉ l := by grind

theorem exists_mem_nil (p : α → Prop) : ¬ (∃ x, ∃ _ : x ∈ @nil α, p x) := by grind

theorem forall_mem_nil (p : α → Prop) : ∀ (x) (_ : x ∈ @nil α), p x := by grind

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ (x) (_ : x ∈ [a]), p x) ↔ p a := by grind

theorem mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False := by grind

theorem mem_singleton_self (a : α) : a ∈ [a] := by grind

theorem mem_of_mem_cons_of_mem : ∀ {a b : α} {l : List α}, a ∈ b :: l → b ∈ l → a ∈ l := by grind

theorem eq_or_ne_mem_of_mem {a b : α} {l : List α} (h' : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) := by grind

theorem ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by grind

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l := by grind

theorem ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b :: l → a ≠ b := by grind

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : a ∉ b :: l → a ∉ l := by grind

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y :: l := by grind

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : a ∉ y :: l → a ≠ y ∧ a ∉ l := by grind

theorem mem_of_getElem {l : List α} {i : Nat} {h} {a : α} (e : l[i] = a) : a ∈ l := by grind

theorem mem_of_getElem? {l : List α} {i : Nat} {a : α} (e : l[i]? = some a) : a ∈ l := by grind

theorem elem_eq_contains [BEq α] {a : α} {l : List α} :
    elem a l = l.contains a := by grind

theorem decide_mem_cons [BEq α] [LawfulBEq α] {l : List α} :
    decide (y ∈ a :: l) = (y == a || decide (y ∈ l)) := by grind

theorem elem_iff [BEq α] [LawfulBEq α] {a : α} {as : List α} :
    elem a as = true ↔ a ∈ as := by grind

theorem contains_iff [BEq α] [LawfulBEq α] {a : α} {as : List α} :
    as.contains a = true ↔ a ∈ as := by grind

theorem elem_eq_mem [BEq α] [LawfulBEq α] (a : α) (as : List α) :
    elem a as = decide (a ∈ as) := by grind

theorem contains_eq_mem [BEq α] [LawfulBEq α] (a : α) (as : List α) :
    as.contains a = decide (a ∈ as) := by grind

theorem contains_cons [BEq α] {a : α} {b : α} {l : List α} :
    (a :: l).contains b = (b == a || l.contains b) := by grind

end length_pos_of_mem

/-! ### `isEmpty` -/

theorem isEmpty_iff {l : List α} : l.isEmpty ↔ l = [] := by grind

theorem isEmpty_eq_false_iff {l : List α} : l.isEmpty = false ↔ l ≠ [] := by grind

theorem isEmpty_iff_length_eq_zero {l : List α} : l.isEmpty ↔ l.length = 0 := by grind [length_eq_zero_iff]

/-! ### any / all -/

theorem any_beq [BEq α] {l : List α} {a : α} : (l.any fun x => a == x) = l.contains a := by
  induction l with grind

/-! ### set -/

theorem set_nil {i : Nat} {a : α} : [].set i a = [] := by grind
theorem set_cons_zero {x : α} {xs : List α} {a : α} :
  (x :: xs).set 0 a = a :: xs := by grind
theorem set_cons_succ {x : α} {xs : List α} {i : Nat} {a : α} :
  (x :: xs).set (i + 1) a = x :: xs.set i a := by grind

theorem getElem_set_self {l : List α} {i : Nat} {a : α} (h : i < (l.set i a).length) :
    (l.set i a)[i] = a := by grind

theorem getElem?_set_self {l : List α} {i : Nat} {a : α} (h : i < l.length) :
    (l.set i a)[i]? = some a := by grind

theorem getElem_set_ne {l : List α} {i j : Nat} (h : i ≠ j) {a : α}
    (hj : j < (l.set i a).length) :
    (l.set i a)[j] = l[j]'(by grind) := by grind

theorem getElem?_set_ne {l : List α} {i j : Nat} (h : i ≠ j) {a : α}  :
    (l.set i a)[j]? = l[j]? := by grind

theorem getElem_set {l : List α} {i j} {a} (h) :
    (set l i a)[j]'h = if i = j then a else l[j]'(by grind) := by grind

theorem getElem?_set {l : List α} {i j : Nat} {a : α} :
    (l.set i a)[j]? = if i = j then if i < l.length then some a else none else l[j]? := by grind

theorem set_eq_of_length_le {l : List α} {i : Nat} (h : l.length ≤ i) {a : α} :
    l.set i a = l := by
  induction l generalizing i with
  | nil => grind
  | cons a l ih => cases i with grind

theorem set_eq_nil_iff {l : List α} (i : Nat) (a : α) : l.set i a = [] ↔ l = [] := by
  cases l with cases i with grind

theorem set_comm (a b : α) {i j : Nat} {l : List α} (h : i ≠ j) :
    (l.set i a).set j b = (l.set j b).set i a := by grind +extAll

theorem set_set (a : α) {b : α} {l : List α} {i : Nat} :  (l.set i a).set i b = l.set i b := by
  cases l with cases i with grind +extAll

theorem set_set' (a : α) {b : α} {l : List α} {i : Nat} : (l.set i a).set i b = l.set i b := by grind +extAll

theorem mem_or_eq_of_mem_set' {l : List α} {i : Nat} {a b : α} : a ∈ l.set i b → a ∈ l ∨ a = b := by
  grind

/-! ### BEq -/

theorem beq_nil_eq [BEq α] {l : List α} : (l == []) = l.isEmpty := by grind

theorem nil_beq_eq [BEq α] {l : List α} : ([] == l) = l.isEmpty := by grind

theorem cons_beq_cons [BEq α] {a b : α} {l₁ l₂ : List α} :
    (a :: l₁ == b :: l₂) = (a == b && l₁ == l₂) := by grind

theorem concat_beq_concat [BEq α] {a b : α} {l₁ l₂ : List α} :
    (l₁ ++ [a] == l₂ ++ [b]) = (l₁ == l₂ && a == b) := by
  induction l₁ generalizing l₂ with cases l₂ with grind

theorem length_eq_of_beq [BEq α] {l₁ l₂ : List α} (h : l₁ == l₂) : l₁.length = l₂.length := by
  induction l₁ generalizing l₂ with cases l₂ with grind

theorem replicate_beq_replicate [BEq α] {a b : α} {n : Nat} :
    (replicate n a == replicate n b) = (n == 0 || a == b) := by
  induction n with grind

/-! ### getLast -/

theorem getElem_length_sub_one_eq_getLast {l : List α} (h : l.length - 1 < l.length) :
    l[l.length - 1] = getLast l (by grind) := by grind

theorem getLast_cons {a : α} {l : List α} (h : l ≠ nil) :
    getLast (a :: l) (by grind) = getLast l h := by
  induction l with grind

theorem getLastD_eq_getLast? {a l} : @getLastD α l a = (getLast? l).getD a := by grind

theorem getLast_singleton {a} (h) : @getLast α [a] h = a := by grind

/-! ### getLast? -/

theorem getLast?_singleton {a : α} : getLast? [a] = a := by grind

theorem getLast?_eq_getLast {l : List α} h : l.getLast? = some (l.getLast h) := by
  cases l with grind

theorem getLast?_eq_getElem? {l : List α} : l.getLast? = l[l.length - 1]? := by
  cases l with grind

theorem getLast_eq_iff_getLast?_eq_some {xs : List α} (h) :
    xs.getLast h = a ↔ xs.getLast? = some a := by
  grind [getLast?_eq_getLast]

theorem getLast?_cons {a : α} : (a::l).getLast? = l.getLast?.getD a := by
  cases l with grind

theorem getLast?_cons_cons : (a :: b :: l).getLast? = (b :: l).getLast? := by grind

theorem getLast?_concat {l : List α} {a : α} : (l ++ [a]).getLast? = some a := by grind

theorem getLastD_concat {a b} {l : List α} : (l ++ [b]).getLastD a = b := by grind

/-! ### getLast! -/

theorem getLast!_nil [Inhabited α] : ([] : List α).getLast! = default := by grind

theorem getLast!_eq_getLast?_getD [Inhabited α] {l : List α} : getLast! l = (getLast? l).getD default := by
  cases l with grind

theorem getLast!_eq_getElem! [Inhabited α] {l : List α} : l.getLast! = l[l.length - 1]! := by
  cases l with grind [→ getLast!_of_getLast?]

/-! ## Head and tail -/

/-! ### head -/

theorem head?_singleton {a : α} : head? [a] = some a := by grind

theorem head?_eq_getElem? {l : List α} : l.head? = l[0]? := by induction l with grind

theorem head_eq_getElem {l : List α} (h : l ≠ []) : head l h = l[0]'(by grind [length_eq_zero_iff]) := by
  cases l with grind

theorem getElem_zero_eq_head {l : List α} (h : 0 < l.length) :
    l[0] = head l (by grind) := by
  cases l with grind

theorem head_eq_iff_head?_eq_some {xs : List α} (h) : xs.head h = a ↔ xs.head? = some a := by
  cases xs with grind

theorem head?_eq_none_iff : l.head? = none ↔ l = [] := by
  cases l with grind

theorem head?_eq_some_iff {xs : List α} {a : α} : xs.head? = some a ↔ ∃ ys, xs = a :: ys := by
  cases xs with grind

theorem isSome_head? : l.head?.isSome ↔ l ≠ [] := by
  cases l with grind

theorem mem_of_mem_head? {l : List α} {a : α} : a ∈ l.head? → a ∈ l := by
  cases l with grind

theorem head_mem_head? {l : List α} (h : l ≠ []) : head l h ∈ head? l := by
  cases l with grind

theorem head?_concat {a : α} : (l ++ [a]).head? = l.head?.getD a := by
  cases l with grind

theorem head?_concat_concat : (l ++ [a, b]).head? = (l ++ [a]).head? := by
  cases l with grind

/-! ### headD -/

/-- `simp` unfolds `headD` in terms of `head?` and `Option.getD`. -/
theorem headD_eq_head?_getD {l : List α} : headD l a = (head? l).getD a := by
  cases l with grind

/-! ### tailD -/

/-- `simp` unfolds `tailD` in terms of `tail?` and `Option.getD`. -/
theorem tailD_eq_tail? {l l' : List α} : tailD l l' = (tail? l).getD l' := by
  cases l with grind

/-! ### tail -/

theorem length_tail {l : List α} : l.tail.length = l.length - 1 := by cases l with grind

theorem tail_eq_tailD {l : List α} : l.tail = tailD l [] := by cases l with grind

theorem mem_of_mem_tail {a : α} {l : List α} (h : a ∈ tail l) : a ∈ l := by
  induction l with grind

theorem ne_nil_of_tail_ne_nil {l : List α} : l.tail ≠ [] → l ≠ [] := by
  cases l with grind

theorem getElem_tail {l : List α} {i : Nat} (h : i < l.tail.length) :
    (tail l)[i] = l[i + 1]'(by grind) := by
  cases l with grind

theorem getElem?_tail {l : List α} {i : Nat} :
    (tail l)[i]? = l[i + 1]? := by
  cases l with grind

theorem set_tail {l : List α} {i : Nat} {a : α} :
    l.tail.set i a = (l.set (i + 1) a).tail := by
  cases l with grind

theorem one_lt_length_of_tail_ne_nil {l : List α} (h : l.tail ≠ []) : 1 < l.length := by
  cases l with grind [length_eq_zero_iff]

/-! ## Basic operations -/

/-! ### map -/

theorem length_map {as : List α} (f : α → β) : (as.map f).length = as.length := by
  fun_induction List.map with grind

theorem getElem?_map {f : α → β} {l : List α} {i : Nat} : (map f l)[i]? = Option.map f l[i]? := by
  fun_induction List.map generalizing i
  · grind
  · cases i with grind

theorem map_id_fun : map (id : α → α) = id := by
  funext l
  induction l with grind

theorem map_id_fun' : map (fun (a : α) => a) = id := by
  funext l
  induction l with grind

theorem map_id (l : List α) : map (id : α → α) l = l := by
  induction l with grind

theorem map_id' (l : List α) : map (fun (a : α) => a) l = l := by
  induction l with grind

theorem map_id'' {f : α → α} (h : ∀ x, f x = x) (l : List α) : map f l = l := by
  induction l with grind

theorem map_singleton {f : α → β} {a : α} : map f [a] = [f a] := by grind

theorem map_eq_nil_iff {f : α → β} {l : List α} : map f l = [] ↔ l = [] := by
  cases l with grind

-- FIXME
attribute [local grind] List.map_inj_left in
theorem map_inj_left {f g : α → β} : map f l = map g l ↔ ∀ a ∈ l, f a = g a := by
  induction l with grind

theorem map_eq_cons_iff' {f : α → β} {l : List α} :
    map f l = b :: l₂ ↔ l.head?.map f = some b ∧ l.tail?.map (map f) = some l₂ := by
  induction l with grind

theorem map_eq_singleton_iff {f : α → β} {l : List α} {b : β} :
    map f l = [b] ↔ ∃ a, l = [a] ∧ f a = b := by
  grind [map_eq_cons_iff]

-- FIXME
attribute [local grind] List.map_inj_left in
theorem map_eq_map_iff : map f l = map g l ↔ ∀ a ∈ l, f a = g a := by
  induction l with grind

theorem map_eq_iff : map f l = l' ↔ ∀ i : Nat, l'[i]? = l[i]?.map f := by
  grind +extAll

theorem map_eq_foldr {f : α → β} {l : List α} : map f l = foldr (fun a bs => f a :: bs) [] l := by
  induction l <;> grind

theorem map_set {f : α → β} {l : List α} {i : Nat} {a : α} :
    (l.set i a).map f = (l.map f).set i (f a) := by
  grind +extAll

theorem head_map {f : α → β} {l : List α} (w) :
    (map f l).head w = f (l.head (by grind)) := by
  cases l with grind

theorem head?_map {f : α → β} {l : List α} : (map f l).head? = l.head?.map f := by
  cases l with grind

theorem map_tail? {f : α → β} {l : List α} : (tail? l).map (map f) = tail? (map f l) := by
  cases l with grind

theorem map_tail {f : α → β} {l : List α} :
    map f l.tail = (map f l).tail := by
  cases l with grind

theorem headD_map {f : α → β} {l : List α} {a : α} : (map f l).headD (f a) = f (l.headD a) := by
  cases l with grind

theorem getLastD_map {f : α → β} {l : List α} {a : α} : (map f l).getLastD (f a) = f (l.getLastD a) := by
  grind

theorem map_map {g : β → γ} {f : α → β} {l : List α} :
    map g (map f l) = map (g ∘ f) l := by induction l with grind

/-! ### filter -/

theorem filter_cons_of_pos {p : α → Bool} {a : α} {l} (pa : p a) :
    filter p (a :: l) = a :: filter p l := by grind [filter]

theorem filter_cons_of_neg {p : α → Bool} {a : α} {l} (pa : ¬ p a) :
    filter p (a :: l) = filter p l := by grind [filter]

theorem filter_cons :
    (x :: xs : List α).filter p = if p x then x :: (xs.filter p) else xs.filter p := by
  grind [filter]

theorem length_filter_le (p : α → Bool) (l : List α) :
    (l.filter p).length ≤ l.length := by
  induction l with grind

theorem filter_eq_self {l} : filter p l = l ↔ ∀ a ∈ l, p a := by
  induction l with simp

theorem mem_filter : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  induction as with grind


theorem forall_mem_filter {l : List α} {p : α → Bool} {P : α → Prop} :
    (∀ (i) (_ : i ∈ l.filter p), P i) ↔ ∀ (j) (_ : j ∈ l), p j → P j := by
  grind

theorem filter_filter {l} : filter p (filter q l) = filter (fun a => p a && q a) l := by
  induction l with grind

theorem foldl_filter {p : α → Bool} {f : β → α → β} {l : List α} {init : β} :
    (l.filter p).foldl f init = l.foldl (fun x y => if p y then f x y else x) init := by
  induction l generalizing init with grind

theorem foldr_filter {p : α → Bool} {f : α → β → β} {l : List α} {init : β} :
    (l.filter p).foldr f init = l.foldr (fun x y => if p x then f x y else y) init := by
  induction l generalizing init with grind

theorem filter_map {f : β → α} {p : α → Bool} {l : List β} :
    filter p (map f l) = map f (filter (p ∘ f) l) := by
  induction l with grind

theorem map_filter_eq_foldr {f : α → β} {p : α → Bool} {as : List α} :
    map f (filter p as) = foldr (fun a bs => bif p a then f a :: bs else bs) [] as := by
  induction as with grind

theorem filter_append {p : α → Bool} (l₁ l₂ : List α) :
    filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂ := by
  induction l₁ with grind

theorem head_filter_of_pos {p : α → Bool} {l : List α} (w : l ≠ []) (h : p (l.head w)) :
    (filter p l).head ((ne_nil_of_mem (mem_filter.2 ⟨head_mem w, h⟩))) = l.head w := by
  cases l with grind

/-! ### filterMap -/

theorem filterMap_cons_none {f : α → Option β} {a : α} {l : List α} (h : f a = none) :
    filterMap f (a :: l) = filterMap f l := by grind

theorem filterMap_cons_some {f : α → Option β} {a : α} {l : List α} {b : β} (h : f a = some b) :
    filterMap f (a :: l) = b :: filterMap f l := by grind

theorem filterMap_eq_map {f : α → β} : filterMap (some ∘ f) = map f := by
  funext l; induction l with grind

theorem filterMap_eq_map' {f : α → β} : filterMap (fun x => some (f x)) = map f := by
  funext l; induction l with grind

theorem filterMap_some_fun : filterMap (some : α → Option α) = id := by
  funext l; induction l with grind

theorem filterMap_some {l : List α} : filterMap some l = l := by
  induction l with grind

theorem map_filterMap_some_eq_filter_map_isSome {f : α → Option β} {l : List α} :
    (l.filterMap f).map some = (l.map f).filter fun b => b.isSome := by
  induction l with grind

theorem length_filterMap_le (f : α → Option β) (l : List α) :
    (filterMap f l).length ≤ l.length := by
  induction l with grind

theorem filterMap_filterMap {f : α → Option β} {g : β → Option γ} {l : List α} :
    filterMap g (filterMap f l) = filterMap (fun x => (f x).bind g) l := by
  induction l with grind

theorem map_filterMap {f : α → Option β} {g : β → γ} {l : List α} :
    map g (filterMap f l) = filterMap (fun x => (f x).map g) l := by
  induction l with grind

theorem filterMap_map {f : α → β} {g : β → Option γ} {l : List α} :
    filterMap g (map f l) = filterMap (g ∘ f) l := by
  induction l with grind

theorem filterMap_filter {p : α → Bool} {f : α → Option β} {l : List α} :
    filterMap f (filter p l) = filterMap (fun x => if p x then f x else none) l := by
  induction l with grind

theorem forall_mem_filterMap {f : α → Option β} {l : List α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ filterMap f l), P i) ↔ ∀ (j) (_ : j ∈ l) (b), f j = some b → P b := by
  grind

theorem filterMap_append {l l' : List α} {f : α → Option β} :
    filterMap f (l ++ l') = filterMap f l ++ filterMap f l' := by
  induction l with grind

theorem head_filterMap_of_eq_some {f : α → Option β} {l : List α} (w : l ≠ []) {b : β} (h : f (l.head w) = some b) :
    (filterMap f l).head ((ne_nil_of_mem (mem_filterMap.2 ⟨_, head_mem w, h⟩))) =
      b := by
  cases l with grind

/-! ### append -/

theorem nil_append_fun : (([] : List α) ++ ·) = id := by grind

theorem cons_append_fun {a : α} {as : List α} :
    (fun bs => ((a :: as) ++ bs)) = fun bs => a :: (as ++ bs) := by grind

theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s with grind

theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t := by grind

theorem getElem_append {l₁ l₂ : List α} {i : Nat} (h : i < (l₁ ++ l₂).length) :
    (l₁ ++ l₂)[i] = if h' : i < l₁.length then l₁[i] else l₂[i - l₁.length]'(by grind) := by
  grind

theorem getElem?_append_left {l₁ l₂ : List α} {i : Nat} (hn : i < l₁.length) :
    (l₁ ++ l₂)[i]? = l₁[i]? := by grind

theorem getElem?_append_right : ∀ {l₁ l₂ : List α} {i : Nat}, l₁.length ≤ i →
  (l₁ ++ l₂)[i]? = l₂[i - l₁.length]?
| [], _, _, _ => by grind
| a :: l, _, i+1, h₁ => by grind

theorem getElem?_append {l₁ l₂ : List α} {i : Nat} :
    (l₁ ++ l₂)[i]? = if i < l₁.length then l₁[i]? else l₂[i - l₁.length]? := by
  grind

theorem getElem_append_left' {l₁ : List α} {i : Nat} (hi : i < l₁.length) (l₂ : List α) :
    l₁[i] = (l₁ ++ l₂)[i]'(by grind) := by grind

theorem singleton_append : [x] ++ l = x :: l := by grind

theorem getLast_concat {a : α} {l : List α} : getLast (l ++ [a]) (by grind) = a := by
  induction l with grind

theorem append_eq_nil_iff : p ++ q = [] ↔ p = [] ∧ q = [] := by grind

theorem nil_eq_append_iff : [] = a ++ b ↔ a = [] ∧ b = [] := by grind

theorem append_ne_nil_of_left_ne_nil {s : List α} (h : s ≠ []) (t : List α) : s ++ t ≠ [] := by grind

theorem append_ne_nil_of_right_ne_nil (s : List α) : t ≠ [] → s ++ t ≠ [] := by grind

theorem cons_eq_append_iff :
    x :: cs = as ++ bs ↔ (as = [] ∧ bs = x :: cs) ∨ (∃ as', as = x :: as' ∧ cs = as' ++ bs) := by
  grind [append_eq_cons_iff]

theorem append_eq_singleton_iff :
    a ++ b = [x] ↔ (a = [] ∧ b = [x]) ∨ (a = [x] ∧ b = []) := by
  cases a with cases b with grind [append_eq_nil_iff]

theorem singleton_eq_append_iff :
    [x] = a ++ b ↔ (a = [] ∧ b = [x]) ∨ (a = [x] ∧ b = []) := by
  cases a with cases b with grind [append_eq_nil_iff]

theorem head_append {l₁ l₂ : List α} (w : l₁ ++ l₂ ≠ []) :
    head (l₁ ++ l₂) w =
      if h : l₁.isEmpty then
        head l₂ (by grind)
      else
        head l₁ (by grind) := by grind

theorem head_append_left {l₁ l₂ : List α} (h : l₁ ≠ []) :
    head (l₁ ++ l₂) (fun h => by grind) = head l₁ h := by grind

theorem head_append_right {l₁ l₂ : List α} (w : l₁ ++ l₂ ≠ []) (h : l₁ = []) :
    head (l₁ ++ l₂) w = head l₂ (by grind) := by grind

theorem head?_append {l : List α} : (l ++ l').head? = l.head?.or l'.head? := by
  cases l with grind

theorem tail?_append {l l' : List α} : (l ++ l').tail? = (l.tail?.map (· ++ l')).or l'.tail? := by
  cases l with grind

theorem head_append_of_ne_nil {l : List α} {w₁} (w₂) :
    head (l ++ l') w₁ = head l w₂ := by
  cases l with grind

theorem tail?_append_of_ne_nil {l l' : List α} (_ : l ≠ []) : (l ++ l').tail? = some (l.tail ++ l') := by
  cases l with grind

theorem tail_append {l l' : List α} : (l ++ l').tail = if l.isEmpty then l'.tail else l.tail ++ l' := by
  cases l with grind

theorem tail_append_of_ne_nil {xs ys : List α} (h : xs ≠ []) :
    (xs ++ ys).tail = xs.tail ++ ys := by
  grind

theorem set_append {s t : List α} :
    (s ++ t).set i x = if i < s.length then s.set i x ++ t else s ++ t.set (i - s.length) x := by
  induction s generalizing i with
  | nil => grind [-List.set_append]
  | cons a as ih => cases i with grind (splits := 12) [-List.set_append]

theorem set_append_left {s t : List α} (i : Nat) (x : α) (h : i < s.length) :
    (s ++ t).set i x = s.set i x ++ t := by grind

theorem set_append_right {s t : List α} (i : Nat) (x : α) (h : s.length ≤ i) :
    (s ++ t).set i x = s ++ t.set (i - s.length) x := by grind

theorem append_eq_filterMap_iff {f : α → Option β} :
    L₁ ++ L₂ = filterMap f l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filterMap f l₁ = L₁ ∧ filterMap f l₂ = L₂ := by
  grind [filterMap_eq_append_iff]

theorem append_eq_filter_iff {p : α → Bool} :
    L₁ ++ L₂ = filter p l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filter p l₁ = L₁ ∧ filter p l₂ = L₂ := by
  grind [filter_eq_append_iff]

theorem map_append {f : α → β} {l₁ l₂} : map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  induction l₁ with grind

theorem append_eq_map_iff {f : α → β} :
    L₁ ++ L₂ = map f l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = L₁ ∧ map f l₂ = L₂ := by
  grind [map_eq_append_iff]

/-! ### flatten -/

theorem length_flatten {L : List (List α)} : L.flatten.length = (L.map length).sum := by
  induction L with grind

theorem flatten_singleton {l : List α} : [l].flatten = l := by grind

theorem nil_eq_flatten_iff {L : List (List α)} : [] = L.flatten ↔ ∀ l ∈ L, l = [] := by
  grind [flatten_eq_nil_iff]

theorem flatten_eq_flatMap {L : List (List α)} : flatten L = L.flatMap id := by
  induction L with grind

theorem head?_flatten {L : List (List α)} : (flatten L).head? = L.findSome? fun l => l.head? := by
  induction L with grind

theorem map_flatten {f : α → β} {L : List (List α)} :
    (flatten L).map f = (map (map f) L).flatten := by
  induction L with grind

theorem filterMap_flatten {f : α → Option β} {L : List (List α)} :
    filterMap f (flatten L) = flatten (map (filterMap f) L) := by
  induction L with grind

theorem filter_flatten {p : α → Bool} {L : List (List α)} :
    filter p (flatten L) = flatten (map (filter p) L) := by
  induction L with grind

theorem flatten_append {L₁ L₂ : List (List α)} : flatten (L₁ ++ L₂) = flatten L₁ ++ flatten L₂ := by
  induction L₁ with grind

theorem flatten_concat {L : List (List α)} {l : List α} : flatten (L ++ [l]) = flatten L ++ l := by
  grind

theorem flatten_flatten {L : List (List (List α))} : flatten (flatten L) = flatten (map flatten L) := by
  induction L with grind

theorem singleton_eq_flatten_iff {xs : List (List α)} {y : α} :
    [y] = xs.flatten ↔ ∃ as bs, xs = as ++ [y] :: bs ∧ (∀ l, l ∈ as → l = []) ∧ (∀ l, l ∈ bs → l = []) := by
  grind [flatten_eq_singleton_iff]

theorem append_eq_flatten_iff {xs : List (List α)} {ys zs : List α} :
    ys ++ zs = xs.flatten ↔
      (∃ as bs, xs = as ++ bs ∧ ys = as.flatten ∧ zs = bs.flatten) ∨
        ∃ as bs c cs ds, xs = as ++ (bs ++ c :: cs) :: ds ∧ ys = as.flatten ++ bs ∧
          zs = c :: cs ++ ds.flatten := by
  grind [flatten_eq_append_iff]

/-! ### flatMap -/

theorem exists_of_mem_flatMap {b : β} {l : List α} {f : α → List β} :
    b ∈ l.flatMap f → ∃ a, a ∈ l ∧ b ∈ f a := by grind

theorem mem_flatMap_of_mem {b : β} {l : List α} {f : α → List β} {a} (al : a ∈ l) (h : b ∈ f a) :
    b ∈ l.flatMap f := by grind

theorem forall_mem_flatMap {p : β → Prop} {l : List α} {f : α → List β} :
    (∀ (x) (_ : x ∈ l.flatMap f), p x) ↔ ∀ (a) (_ : a ∈ l) (b) (_ : b ∈ f a), p b := by
  grind

theorem flatMap_singleton (f : α → List β) (x : α) : [x].flatMap f = f x := by grind

theorem flatMap_singleton' (l : List α) : (l.flatMap fun x => [x]) = l := by
  induction l with grind

theorem head?_flatMap {l : List α} {f : α → List β} :
    (l.flatMap f).head? = l.findSome? fun a => (f a).head? := by
  induction l with grind

theorem flatMap_append {xs ys : List α} {f : α → List β} :
    (xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap f := by
  induction xs with grind

theorem flatMap_assoc {l : List α} {f : α → List β} {g : β → List γ} :
    (l.flatMap f).flatMap g = l.flatMap fun x => (f x).flatMap g := by
  induction l with grind

theorem filterMap_flatMap {l : List α} {g : α → List β} {f : β → Option γ} :
    (l.flatMap g).filterMap f = l.flatMap fun a => (g a).filterMap f := by
  induction l with grind

theorem filter_flatMap {l : List α} {g : α → List β} {f : β → Bool} :
    (l.flatMap g).filter f = l.flatMap fun a => (g a).filter f := by
  induction l with grind

/-! ### replicate -/

theorem replicate_one : replicate 1 a = [a] := by grind

theorem replicate_succ' : replicate (n + 1) a = replicate n a ++ [a] := by
  induction n with grind

theorem mem_replicate {a b : α} {n} : b ∈ replicate n a ↔ n ≠ 0 ∧ b = a := by
  cases n with grind

theorem eq_of_mem_replicate {a b : α} {n} (h : b ∈ replicate n a) : b = a := by grind

theorem forall_mem_replicate {p : α → Prop} {a : α} {n} :
    (∀ b, b ∈ replicate n a → p b) ↔ n = 0 ∨ p a := by grind

theorem replicate_succ_ne_nil {n : Nat} {a : α} : replicate (n+1) a ≠ [] := by grind

theorem replicate_eq_nil_iff {n : Nat} (a : α) : replicate n a = [] ↔ n = 0 := by
  cases n with grind

theorem getElem?_replicate_of_lt {n : Nat} {i : Nat} (h : i < n) : (replicate n a)[i]? = some a := by
  grind

theorem head?_replicate {a : α} {n : Nat} : (replicate n a).head? = if n = 0 then none else some a := by
  cases n with grind

theorem head_replicate (w : replicate n a ≠ []) : (replicate n a).head w = a := by
  cases n with grind

theorem tail_replicate {n : Nat} {a : α} : (replicate n a).tail = replicate (n - 1) a := by
  cases n with grind

theorem set_replicate_self : (replicate n a).set i a = replicate n a := by
  grind +extAll

theorem replicate_append_replicate : replicate n a ++ replicate m a = replicate (n + m) a := by
  grind +extAll

theorem replicate_eq_append_iff {l₁ l₂ : List α} {a : α} :
    replicate n a = l₁ ++ l₂ ↔
      l₁.length + l₂.length = n ∧ l₁ = replicate l₁.length a ∧ l₂ = replicate l₂.length a := by
  grind [append_eq_replicate_iff]

theorem map_replicate : (replicate n a).map f = replicate n (f a) := by
  grind +extAll

theorem filter_replicate_of_pos (h : p a) : (replicate n a).filter p = replicate n a := by grind

theorem filter_replicate_of_neg (h : ¬ p a) : (replicate n a).filter p = [] := by grind

theorem flatten_replicate_nil : (replicate n ([] : List α)).flatten = [] := by
  induction n with grind

theorem flatten_replicate_singleton : (replicate n [a]).flatten = replicate n a := by
  induction n with grind

theorem flatMap_replicate {β} {f : α → List β} : (replicate n a).flatMap f = (replicate n (f a)).flatten := by
  induction n with grind

theorem isEmpty_replicate : (replicate n a).isEmpty = decide (n = 0) := by
  cases n with grind

/-! ### reverse -/

theorem length_reverse {as : List α} : (as.reverse).length = as.length := by
  induction as with grind

theorem mem_reverse {x : α} {as : List α} : x ∈ reverse as ↔ x ∈ as := by
  grind [reverse, mem_reverseAux]

theorem reverse_eq_nil_iff {xs : List α} : xs.reverse = [] ↔ xs = [] := by
  cases xs with grind

theorem reverse_ne_nil_iff {xs : List α} : xs.reverse ≠ [] ↔ xs ≠ [] := by
  grind [reverse_eq_nil_iff]

theorem isEmpty_reverse {xs : List α} : xs.reverse.isEmpty = xs.isEmpty := by
  cases xs with grind

theorem reverseAux_reverseAux_nil {as bs : List α} : reverseAux (reverseAux as bs) [] = reverseAux bs as := by
  induction as generalizing bs with grind [reverseAux]

theorem reverse_eq_iff {as bs : List α} : as.reverse = bs ↔ as = bs.reverse := by
  grind

theorem getLast?_eq_head?_reverse {xs : List α} : xs.getLast? = xs.reverse.head? := by
  grind

theorem head?_eq_getLast?_reverse {xs : List α} : xs.head? = xs.reverse.getLast? := by
  grind

theorem map_reverse {f : α → β} {l : List α} : l.reverse.map f = (l.map f).reverse := by
  induction l with grind

theorem filter_reverse {p : α → Bool} {l : List α} : (l.reverse.filter p) = (l.filter p).reverse := by
  induction l with grind


theorem reverse_append {as bs : List α} : (as ++ bs).reverse = bs.reverse ++ as.reverse := by
  induction as with grind

theorem reverse_eq_append_iff {xs ys zs : List α} :
    xs.reverse = ys ++ zs ↔ xs = zs.reverse ++ ys.reverse := by grind

theorem reverse_concat {l : List α} {a : α} : (l ++ [a]).reverse = a :: l.reverse := by
  grind (ematch := 6)

theorem reverse_eq_concat {xs ys : List α} {a : α} :
    xs.reverse = ys ++ [a] ↔ xs = a :: ys.reverse := by grind

theorem reverse_flatten {L : List (List α)} :
    L.flatten.reverse = (L.map reverse).reverse.flatten := by
  induction L with grind

theorem flatten_reverse {L : List (List α)} :
    L.reverse.flatten = (L.map reverse).flatten.reverse := by
  induction L with grind

theorem reverse_flatMap {β} {l : List α} {f : α → List β} : (l.flatMap f).reverse = l.reverse.flatMap (reverse ∘ f) := by
  induction l with grind

theorem flatMap_reverse {β} {l : List α} {f : α → List β} : (l.reverse.flatMap f) = (l.flatMap (reverse ∘ f)).reverse := by
  induction l with grind


/-! ### foldl and foldr -/

theorem foldr_cons_eq_append {l : List α} {f : α → β} {l' : List β} :
    l.foldr (fun x ys => f x :: ys) l' = l.map f ++ l' := by
  induction l with grind

/-- Variant of `foldr_cons_eq_append` specalized to `f = id`. -/
theorem foldr_cons_eq_append' {l l' : List β} :
    l.foldr cons l' = l ++ l' := by
  induction l with grind

theorem foldl_flip_cons_eq_append {l : List α} {f : α → β} {l' : List β} :
    l.foldl (fun xs y => f y :: xs) l' = (l.map f).reverse ++ l' := by
  induction l generalizing l' with grind

theorem foldr_append_eq_append {l : List α} {f : α → List β} {l' : List β} :
    l.foldr (f · ++ ·) l' = (l.map f).flatten ++ l' := by
  induction l with grind

theorem foldl_append_eq_append {l : List α} {f : α → List β} {l' : List β} :
    l.foldl (· ++ f ·) l' = l' ++ (l.map f).flatten := by
  induction l generalizing l' with grind

theorem foldr_flip_append_eq_append {l : List α} {f : α → List β} {l' : List β} :
    l.foldr (fun x ys => ys ++ f x) l' = l' ++ (l.map f).reverse.flatten := by
  induction l generalizing l' with grind

theorem foldl_flip_append_eq_append {l : List α} {f : α → List β} {l' : List β} :
    l.foldl (fun xs y => f y ++ xs) l' = (l.map f).reverse.flatten ++ l' := by
  induction l generalizing l' with grind

theorem foldr_cons_nil {l : List α} : l.foldr cons [] = l := by grind

theorem foldl_map {f : β₁ → β₂} {g : α → β₂ → α} {l : List β₁} {init : α} :
    (l.map f).foldl g init = l.foldl (fun x y => g x (f y)) init := by
  induction l generalizing init with grind

theorem foldr_map {f : α₁ → α₂} {g : α₂ → β → β} {l : List α₁} {init : β} :
    (l.map f).foldr g init = l.foldr (fun x y => g (f x) y) init := by
  induction l generalizing init with grind

theorem foldl_filterMap {f : α → Option β} {g : γ → β → γ} {l : List α} {init : γ} :
    (l.filterMap f).foldl g init = l.foldl (fun x y => match f y with | some b => g x b | none => x) init := by
  induction l generalizing init with grind

theorem foldr_filterMap {f : α → Option β} {g : β → γ → γ} {l : List α} {init : γ} :
    (l.filterMap f).foldr g init = l.foldr (fun x y => match f x with | some b => g b y | none => y) init := by
  induction l generalizing init with grind

theorem foldl_map_hom {g : α → β} {f : α → α → α} {f' : β → β → β} {a : α} {l : List α}
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (l.map g).foldl f' (g a) = g (l.foldl f a) := by
  induction l generalizing a with grind

theorem foldr_map_hom {g : α → β} {f : α → α → α} {f' : β → β → β} {a : α} {l : List α}
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (l.map g).foldr f' (g a) = g (l.foldr f a) := by
  induction l generalizing a with grind

theorem foldl_flatten {f : β → α → β} {b : β} {L : List (List α)} :
    (flatten L).foldl f b = L.foldl (fun b l => l.foldl f b) b := by
  induction L generalizing b with grind

theorem foldr_flatten {f : α → β → β} {b : β} {L : List (List α)} :
    (flatten L).foldr f b = L.foldr (fun l b => l.foldr f b) b := by
  induction L with grind

theorem foldl_hom (f : α₁ → α₂) {g₁ : α₁ → β → α₁} {g₂ : α₂ → β → α₂} {l : List β} {init : α₁}
    (H : ∀ x y, g₂ (f x) y = f (g₁ x y)) : l.foldl g₂ (f init) = f (l.foldl g₁ init) := by
  induction l generalizing init with grind

theorem foldr_hom (f : β₁ → β₂) {g₁ : α → β₁ → β₁} {g₂ : α → β₂ → β₂} {l : List α} {init : β₁}
    (H : ∀ x y, g₂ x (f y) = f (g₁ x y)) : l.foldr g₂ (f init) = f (l.foldr g₁ init) := by
  induction l with grind

theorem foldl_rel {l : List α} {f g : β → α → β} {a b : β} {r : β → β → Prop}
    (h : r a b) (h' : ∀ (a : α), a ∈ l → ∀ (c c' : β), r c c' → r (f c a) (g c' a)) :
    r (l.foldl (fun acc a => f acc a) a) (l.foldl (fun acc a => g acc a) b) := by
  induction l generalizing a b with grind

theorem foldr_rel {l : List α} {f g : α → β → β} {a b : β} {r : β → β → Prop}
    (h : r a b) (h' : ∀ (a : α), a ∈ l → ∀ (c c' : β), r c c' → r (f a c) (g a c')) :
    r (l.foldr (fun a acc => f a acc) a) (l.foldr (fun a acc => g a acc) b) := by
  induction l generalizing a b with grind

/-! #### Further results about `getLast` and `getLast?` -/

theorem getLast_append {l : List α} (h : l ++ l' ≠ []) :
    (l ++ l').getLast h =
      if h' : l'.isEmpty then
        l.getLast (by grind)
      else
        l'.getLast (by grind) := by grind

theorem getLast_append_right {l : List α} (h : l' ≠ []) :
    (l ++ l').getLast (fun h => by grind) = l'.getLast h := by grind

theorem getLast_append_left {l : List α} (w : l ++ l' ≠ []) (h : l' = []) :
    (l ++ l').getLast w = l.getLast (by grind) := by grind

theorem getLast?_replicate {a : α} {n : Nat} :
    (replicate n a).getLast? = if n = 0 then none else some a := by grind

theorem getLast_replicate (w : replicate n a ≠ []) : (replicate n a).getLast w = a := by grind

theorem getLast_eq_head_reverse {l : List α} (h : l ≠ []) :
    l.getLast h = l.reverse.head (by simp_all) := by grind

/-! ## List membership -/

/-! ### elem / contains -/

theorem contains_eq_any_beq [BEq α] {l : List α} {a : α} : l.contains a = l.any (a == ·) := by
  induction l with grind

theorem contains_iff_mem [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    l.contains a ↔ a ∈ l := by
  grind


/-! ## Sublists -/

/-! ### partition -/

theorem mem_partition : a ∈ l ↔ a ∈ (partition p l).1 ∨ a ∈ (partition p l).2 := by
  grind


/-! ### dropLast -/

theorem length_dropLast {xs : List α} : xs.dropLast.length = xs.length - 1 := by
  induction xs with simp

theorem getElem?_dropLast {xs : List α} {i : Nat} :
    xs.dropLast[i]? = if i < xs.length - 1 then xs[i]? else none := by
  grind [getElem?_eq_getElem]

theorem head_dropLast {xs : List α} (h) :
    xs.dropLast.head h = xs.head (by rintro rfl; simp at h) := by
  cases xs with
  | nil => grind
  | cons x xs => cases xs with grind

theorem getLast_dropLast {xs : List α} (h) :
   xs.dropLast.getLast h = xs[xs.length - 2]'(by grind [length_eq_zero_iff]) := by
  grind

theorem map_dropLast {f : α → β} {l : List α} : l.dropLast.map f = (l.map f).dropLast := by
  induction l with grind +extAll

theorem dropLast_append {l₁ l₂ : List α} :
    (l₁ ++ l₂).dropLast = if l₂.isEmpty then l₁.dropLast else l₁ ++ l₂.dropLast := by
  grind +extAll (splits := 12) [length_eq_zero_iff]

theorem dropLast_append_cons : dropLast (l₁ ++ b :: l₂) = l₁ ++ dropLast (b :: l₂) := by
  grind +extAll

-- theorem dropLast_concat : dropLast (l₁ ++ [b]) = l₁ := by grind

theorem dropLast_replicate {n : Nat} {a : α} : dropLast (replicate n a) = replicate (n - 1) a := by
  grind +extAll


/-! ## Manipulating elements -/

/-! ### replace -/
section replace
variable [BEq α]

theorem replace_cons_self [LawfulBEq α] {a : α} : (a::as).replace a b = b::as := by grind

theorem replace_of_not_mem [LawfulBEq α] {l : List α} (h : a ∉ l) : l.replace a b = l := by
  induction l with grind

theorem length_replace {l : List α} : (l.replace a b).length = l.length := by
  induction l with grind

theorem getElem?_replace_of_ne [LawfulBEq α] {l : List α} {i : Nat} (h : l[i]? ≠ some a) :
    (l.replace a b)[i]? = l[i]? := by
  grind

theorem getElem_replace_of_ne [LawfulBEq α] {l : List α} {i : Nat} {h : i < l.length} (h' : l[i] ≠ a) :
    (l.replace a b)[i]'(by simpa) = l[i]'(h) := by grind

theorem replace_append [LawfulBEq α] {l₁ l₂ : List α} :
    (l₁ ++ l₂).replace a b = if a ∈ l₁ then l₁.replace a b ++ l₂ else l₁ ++ l₂.replace a b := by
  induction l₁ with grind

theorem replace_append_left [LawfulBEq α] {l₁ l₂ : List α} (h : a ∈ l₁) :
    (l₁ ++ l₂).replace a b = l₁.replace a b ++ l₂ := by grind

theorem replace_append_right [LawfulBEq α] {l₁ l₂ : List α} (h : ¬ a ∈ l₁) :
    (l₁ ++ l₂).replace a b = l₁ ++ l₂.replace a b := by grind

theorem replace_replicate_self [LawfulBEq α] {a : α} (h : 0 < n) :
    (replicate n a).replace a b = b :: replicate (n - 1) a := by
  cases n with grind

end replace

/-! ### insert -/

section insert
variable [BEq α]

theorem insert_nil (a : α) : [].insert a = [a] := by grind [List.insert]

variable [LawfulBEq α]

theorem insert_of_mem {l : List α} (h : a ∈ l) : l.insert a = l := by
  grind [List.insert]

theorem insert_of_not_mem {l : List α} (h : a ∉ l) : l.insert a = a :: l := by
  grind [List.insert]

theorem mem_insert_iff {l : List α} : a ∈ l.insert b ↔ a = b ∨ a ∈ l := by
  if h : b ∈ l then grind [insert_of_mem]
  else grind [insert_of_not_mem]

theorem mem_insert_self {a : α} {l : List α} : a ∈ l.insert a := by grind

theorem mem_insert_of_mem {l : List α} (h : a ∈ l) : a ∈ l.insert b := by grind

theorem eq_or_mem_of_mem_insert {l : List α} (h : a ∈ l.insert b) : a = b ∨ a ∈ l := by grind

theorem length_insert_of_mem {l : List α} (h : a ∈ l) :
    length (l.insert a) = length l := by grind [List.insert]

theorem length_insert_of_not_mem {l : List α} (h : a ∉ l) :
    length (l.insert a) = length l + 1 := by grind [List.insert]

theorem length_insert {l : List α} :
    (l.insert a).length = l.length + if a ∈ l then 0 else 1 := by
  grind [List.insert]

theorem length_le_length_insert {l : List α} {a : α} : l.length ≤ (l.insert a).length := by
  grind

theorem length_insert_pos {l : List α} {a : α} : 0 < (l.insert a).length := by
  grind

theorem insert_eq {l : List α} {a : α} : l.insert a = if a ∈ l then l else a :: l := by
  grind [List.insert]

theorem getElem?_insert_zero {l : List α} {a : α} :
    (l.insert a)[0]? = if a ∈ l then l[0]? else some a := by
  grind [List.insert]

theorem getElem?_insert_succ {l : List α} {a : α} {i : Nat} :
    (l.insert a)[i+1]? = if a ∈ l then l[i+1]? else l[i]? := by
  grind [List.insert]

theorem insert_append {l₁ l₂ : List α} {a : α} :
    (l₁ ++ l₂).insert a = if a ∈ l₂ then l₁ ++ l₂ else l₁.insert a ++ l₂ := by
  grind [List.insert]

theorem insert_append_of_mem_left {l₁ l₂ : List α} (h : a ∈ l₂) :
    (l₁ ++ l₂).insert a = l₁ ++ l₂ := by
  grind

theorem insert_append_of_not_mem_left {l₁ l₂ : List α} (h : ¬ a ∈ l₂) :
    (l₁ ++ l₂).insert a = l₁.insert a ++ l₂ := by
  grind

theorem insert_replicate_self {a : α} (h : 0 < n) : (replicate n a).insert a = replicate n a := by
  grind [List.insert]

theorem insert_replicate_ne {a b : α} (h : !b == a) :
    (replicate n a).insert b = b :: replicate n a := by
  grind [List.insert]

end insert


/-! ## Logic -/

/-! ### any / all -/

theorem not_any_eq_all_not {l : List α} {p : α → Bool} : (!l.any p) = l.all fun a => !p a := by
  induction l with grind

theorem not_all_eq_any_not {l : List α} {p : α → Bool} : (!l.all p) = l.any fun a => !p a := by
  induction l with grind

theorem and_any_distrib_left {l : List α} {p : α → Bool} {q : Bool} :
    (q && l.any p) = l.any fun a => q && p a := by
  induction l with grind

theorem and_any_distrib_right {l : List α} {p : α → Bool} {q : Bool} :
    (l.any p && q) = l.any fun a => p a && q := by
  induction l with grind

theorem or_all_distrib_left {l : List α} {p : α → Bool} {q : Bool} :
    (q || l.all p) = l.all fun a => q || p a := by
  induction l with grind

theorem or_all_distrib_right {l : List α} {p : α → Bool} {q : Bool} :
    (l.all p || q) = l.all fun a => p a || q := by
  induction l with grind

theorem any_eq_not_all_not {l : List α} {p : α → Bool} : l.any p = !l.all (!p .) := by
  induction l with grind

theorem all_eq_not_any_not {l : List α} {p : α → Bool} : l.all p = !l.any (!p .) := by
  induction l with grind

theorem any_map {l : List α} {p : β → Bool} : (l.map f).any p = l.any (p ∘ f) := by
  induction l with grind

theorem all_map {l : List α} {p : β → Bool} : (l.map f).all p = l.all (p ∘ f) := by
  induction l with grind

theorem any_filter {l : List α} {p q : α → Bool} :
    (filter p l).any q = l.any fun a => p a && q a := by
  induction l with grind

theorem all_filter {l : List α} {p q : α → Bool} :
    (filter p l).all q = l.all fun a => !(p a) || q a := by
  induction l with grind

theorem any_filterMap {l : List α} {f : α → Option β} {p : β → Bool} :
    (filterMap f l).any p = l.any fun a => match f a with | some b => p b | none => false := by
  induction l with grind

theorem all_filterMap {l : List α} {f : α → Option β} {p : β → Bool} :
    (filterMap f l).all p = l.all fun a => match f a with | some b => p b | none => true := by
  induction l with grind

theorem any_append {xs ys : List α} : (xs ++ ys).any f = (xs.any f || ys.any f) := by
  induction xs with grind

theorem all_append {xs ys : List α} : (xs ++ ys).all f = (xs.all f && ys.all f) := by
  induction xs with grind

theorem any_flatten {l : List (List α)} : l.flatten.any f = l.any (any · f) := by
  induction l with grind

theorem all_flatten {l : List (List α)} : l.flatten.all f = l.all (all · f) := by
  induction l with grind

theorem any_flatMap {l : List α} {f : α → List β} :
    (l.flatMap f).any p = l.any fun a => (f a).any p := by
  induction l with grind

theorem all_flatMap {l : List α} {f : α → List β} :
    (l.flatMap f).all p = l.all fun a => (f a).all p := by
  induction l with grind

theorem any_reverse {l : List α} : l.reverse.any f = l.any f := by
  induction l with grind

theorem all_reverse {l : List α} : l.reverse.all f = l.all f := by
  induction l with grind


end Hidden

/-! Additional examples -/

example {xs : List α} {i : Nat} (h : i < xs.length) : xs.take i ++ xs[i] :: xs.drop (i + 1) = xs := by
  apply List.ext_getElem <;> grind (splits := 10)

example : (List.range 1).sum = 0 := by grind
