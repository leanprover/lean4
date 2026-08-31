-- Note that `grind_list.lean` uses `reset_grind_attrs%` to clear the grind attributes.
-- This file does not: it is testing the grind attributes in the library.

-- This file follows `Data/List/Lemmas.lean`. Indeed, if we decided `grind` is allowed there,
-- it should be possible to replace proofs there with these.
-- (In some cases, the proofs here are now cheating and directly using the same result from the library,
-- but initially I was avoiding this, but haven't bothered writing `grind [-X]` everywhere.)

open List Nat

namespace Hidden


/-! ### getElem? and getElem -/

theorem getElem?_eq_some_iff {l : List α} : l[i]? = some a ↔ ∃ h : i < l.length, l[i] = a := by
  induction l with grind

theorem some_eq_getElem?_iff {l : List α} : some a = l[i]? ↔ ∃ h : i < l.length, l[i] = a := by
  grind

theorem some_getElem_eq_getElem?_iff {xs : List α} {i : Nat} (h : i < xs.length) :
    (some xs[i] = xs[i]?) ↔ True := by
  grind

theorem getElem?_eq_some_getElem_iff {xs : List α} {i : Nat} (h : i < xs.length) :
    (xs[i]? = some xs[i]) ↔ True := by
  grind

theorem getElem_eq_iff {l : List α} {i : Nat} (h : i < l.length) : l[i] = x ↔ l[i]? = some x := by
  grind

theorem getElem_eq_getElem?_get {l : List α} {i : Nat} (h : i < l.length) :
    l[i] = l[i]?.get (by simp [h]) := by
  grind

theorem getD_getElem? {l : List α} {i : Nat} {d : α} :
    l[i]?.getD d = if p : i < l.length then l[i]'p else d := by
  grind

theorem getElem_singleton {a : α} {i : Nat} (h : i < 1) : [a][i] = a := by grind

theorem getElem?_singleton {a : α} {i : Nat} : [a][i]? = if i = 0 then some a else none := by
  grind

theorem getElem_zero {l : List α} (h : 0 < l.length) : l[0] = l.head (length_pos_iff.mp h) := by
  grind

theorem ext_getElem {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i]'h₁ = l₂[i]'h₂) : l₁ = l₂ :=
  ext_getElem? (by grind)

theorem getElem_concat_length {l : List α} {a : α} {i : Nat} (h : i = l.length) (w) :
    (l ++ [a])[i]'w = a := by
  grind

/-! ### mem -/

theorem exists_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∃ x, ∃ _ : x ∈ a :: l, p x) ↔ p a ∨ ∃ x, ∃ _ : x ∈ l, p x := by grind

theorem getElem?_of_mem {a} {l : List α} (h : a ∈ l) : ∃ i : Nat, l[i]? = some a := by
  let ⟨n, _, e⟩ := getElem_of_mem h
  exact ⟨n, by grind⟩

/-! ### any / all -/

theorem any_eq {l : List α} : l.any p = decide (∃ x, x ∈ l ∧ p x) := by grind

theorem all_eq {l : List α} : l.all p = decide (∀ x, x ∈ l → p x) := by grind

theorem decide_exists_mem {l : List α} {p : α → Prop} [DecidablePred p] :
    decide (∃ x, x ∈ l ∧ p x) = l.any p := by
  grind

theorem decide_forall_mem {l : List α} {p : α → Prop} [DecidablePred p] :
    decide (∀ x, x ∈ l → p x) = l.all p := by
  grind

theorem any_eq_true {l : List α} : l.any p = true ↔ ∃ x, x ∈ l ∧ p x := by
  grind

theorem all_eq_true {l : List α} : l.all p = true ↔ ∀ x, x ∈ l → p x := by
  grind

theorem any_eq_false {l : List α} : l.any p = false ↔ ∀ x, x ∈ l → ¬p x := by
  grind

theorem all_eq_false {l : List α} : l.all p = false ↔ ∃ x, x ∈ l ∧ ¬p x := by
  grind

/-! ### any / all -/

theorem all_bne [BEq α] {l : List α} : (l.all fun x => a != x) = !l.contains a := by
  induction l <;> grind [bne]

/-! ### set -/

theorem getElem?_set_self' {l : List α} {i : Nat} {a : α} :
    (set l i a)[i]? = Function.const _ a <$> l[i]? := by
  grind

theorem getElem?_set' {l : List α} {i j : Nat} {a : α} :
    (set l i a)[j]? = if i = j then Function.const _ a <$> l[j]? else l[j]? := by
  grind

/-! ### getLast -/

theorem _root_.List.length_pos_of_ne_nil {l : List α} (h : l ≠ []) : 0 < l.length := by
  grind

theorem getLast_eq_getLastD {a l} (h) : @getLast α (a::l) h = getLastD l a := by
  grind

theorem getLast!_cons_eq_getLastD [Inhabited α] : @getLast! α _ (a::l) = getLastD l a := by
  grind

theorem getElem_cons_length {x : α} {xs : List α} {i : Nat} (h : i = xs.length) :
    (x :: xs)[i]'(by simp [h]) = (x :: xs).getLast (cons_ne_nil x xs) := by
  grind

/-! ### getLast? -/

theorem getLast_eq_iff_getLast?_eq_some {xs : List α} (h) :
    xs.getLast h = a ↔ xs.getLast? = some a := by
  grind

/-! ### getLast! -/

theorem getLast!_nil [Inhabited α] : ([] : List α).getLast! = default := by grind

theorem getLast!_eq_getLast?_getD [Inhabited α] {l : List α} : getLast! l = (getLast? l).getD default := by
  cases l with grind

theorem getLast!_eq_getElem! [Inhabited α] {l : List α} : l.getLast! = l[l.length - 1]! := by
  cases l with grind

/-! ### map -/

theorem mem_map {f : α → β} {l : List α} : b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b := by
  induction l with grind

theorem forall_mem_map {f : α → β} {l : List α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ l.map f), P i) ↔ ∀ (j) (_ : j ∈ l), P (f j) := by
  grind

example {f : α → β} (w : ∀ x y, f x = f y → x = y) (x y : α) (h : f x = f y) : x = y := by
  grind

theorem map_inj_right {f : α → β} (w : ∀ x y, f x = f y → x = y) : map f l = map f l' ↔ l = l' := by
  induction l generalizing l' with grind [cases List]

theorem map_eq_cons_iff {f : α → β} {l : List α} :
    map f l = b :: l₂ ↔ ∃ a l₁, l = a :: l₁ ∧ f a = b ∧ map f l₁ = l₂ := by
  cases l with grind

theorem getLast_map {f : α → β} {l : List α} (h) :
    getLast (map f l) h = f (getLast l (by simpa using h)) := by
  cases l with grind

theorem getLast?_map {f : α → β} {l : List α} : (map f l).getLast? = l.getLast?.map f := by
  cases l with grind

/-! ### filter -/

theorem length_filter_eq_length_iff {l} : (filter p l).length = l.length ↔ ∀ a ∈ l, p a := by
  induction l with grind

theorem filterMap_length_eq_length {l} :
    (filterMap f l).length = l.length ↔ ∀ a ∈ l, (f a).isSome := by
  induction l with grind

theorem filterMap_eq_filter {p : α → Bool} :
    filterMap (Option.guard (p ·)) = filter p := by
  funext l
  induction l with grind

theorem mem_filterMap {f : α → Option β} {l : List α} {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b := by
  induction l with grind

theorem filterMap_eq_nil_iff {l} : filterMap f l = [] ↔ ∀ a ∈ l, f a = none := by
  constructor
  · grind
  · induction l with grind

/-! ### append -/

theorem append_of_mem {a : α} {l : List α} : a ∈ l → ∃ s t : List α, l = s ++ a :: t
  | .head l => ⟨[], l, rfl⟩
  | .tail b h => let ⟨s, t, h'⟩ := append_of_mem h; ⟨b::s, t, by grind⟩

theorem mem_iff_append {a : α} {l : List α} : a ∈ l ↔ ∃ s t : List α, l = s ++ a :: t :=
  ⟨append_of_mem, by grind⟩

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
    (∀ (x) (_ : x ∈ l₁ ++ l₂), p x) ↔ (∀ (x) (_ : x ∈ l₁), p x) ∧ (∀ (x) (_ : x ∈ l₂), p x) := by
  grind

theorem getElem_append_right' (l₁ : List α) {l₂ : List α} {i : Nat} (hi : i < l₂.length) :
    l₂[i] = (l₁ ++ l₂)[i + l₁.length]'(by grind) := by
  grind

theorem getElem_of_append {l : List α} (eq : l = l₁ ++ a :: l₂) (h : l₁.length = i) :
    l[i]'(by grind) = a := by
  grind

theorem append_eq_append_iff {ws xs ys zs : List α} :
    ws ++ xs = ys ++ zs ↔ (∃ as, ys = ws ++ as ∧ xs = as ++ zs) ∨ ∃ bs, ws = ys ++ bs ∧ zs = bs ++ xs := by
  induction ws generalizing ys with
  | nil => grind
  | cons a as ih => cases ys with grind

theorem concat_append {a : α} {l₁ l₂ : List α} : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by grind

theorem append_concat {a : α} {l₁ l₂ : List α} : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by
  grind

theorem map_concat {f : α → β} {a : α} {l : List α} : map f (concat l a) = concat (map f l) (f a) := by
  induction l with grind

/-! ### flatMap -/

theorem flatMap_map (f : α → β) (g : β → List γ) (l : List α) :
    (map f l).flatMap g = l.flatMap (fun a => g (f a)) := by
  induction l with grind

theorem flatMap_eq_foldl {f : α → List β} {l : List α} :
    l.flatMap f = l.foldl (fun acc a => acc ++ f a) [] := by
  suffices ∀ l', l' ++ l.flatMap f = l.foldl (fun acc a => acc ++ f a) l' by grind
  intro l'
  induction l generalizing l' with grind

/-! ### replicate -/

theorem getElem?_replicate : (replicate n a)[i]? = if i < n then some a else none := by
  grind

theorem filter_replicate : (replicate n a).filter p = if p a then replicate n a else [] := by
  cases n with grind

theorem filterMap_replicate {f : α → Option β} :
    (replicate n a).filterMap f = match f a with | none => [] | .some b => replicate n b := by
  induction n with grind

theorem sum_replicate_nat {n : Nat} {a : Nat} : (replicate n a).sum = n * a := by
  induction n with grind

/-! ### reverse -/

theorem getElem?_reverse' : ∀ {l : List α} {i j}, i + j + 1 = length l →
    l.reverse[i]? = l[j]?
  | [], _, _, _ => by grind
  | a::l, i, 0, h => by grind
  | a::l, i, j+1, h => by grind

theorem getElem?_reverse {l : List α} {i} (h : i < length l) :
    l.reverse[i]? = l[l.length - 1 - i]? := by grind

theorem getElem_reverse {l : List α} {i} (h : i < l.reverse.length) :
    l.reverse[i] = l[l.length - 1 - i]'(by grind) := by
  grind

theorem getLast?_reverse {l : List α} : l.reverse.getLast? = l.head? := by
  cases l with grind

theorem head?_reverse {l : List α} : l.reverse.head? = l.getLast? := by
  grind

theorem mem_of_mem_getLast? {l : List α} {a : α} (h : a ∈ getLast? l) : a ∈ l := by
  grind

theorem filterMap_reverse {f : α → Option β} {l : List α} : (l.reverse.filterMap f) = (l.filterMap f).reverse := by
  induction l with grind

/-! ### foldlM and foldrM -/

theorem foldlM_pure [Monad m] [LawfulMonad m] {f : β → α → β} {b : β} {l : List α} :
    l.foldlM (m := m) (pure <| f · ·) b = pure (l.foldl f b) := by
  induction l generalizing b with grind

theorem foldrM_pure [Monad m] [LawfulMonad m] {f : α → β → β} {b : β} {l : List α} :
    l.foldrM (m := m) (pure <| f · ·) b = pure (l.foldr f b) := by
  induction l generalizing b with grind

/-! ### foldl and foldr -/

theorem foldl_eq_foldr_reverse {l : List α} {f : β → α → β} {b : β} :
    l.foldl f b = l.reverse.foldr (fun x y => f y x) b := by grind

theorem foldr_eq_foldl_reverse {l : List α} {f : α → β → β} {b : β} :
    l.foldr f b = l.reverse.foldl (fun x y => f y x) b := by grind

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op]
    {l : List α} {a₁ a₂} : l.foldl op (op a₁ a₂) = op a₁ (l.foldl op a₂) := by
  induction l generalizing a₁ a₂ with grind

theorem foldl_add_const {l : List α} {a b : Nat} :
    l.foldl (fun x _ => x + a) b = b + a * l.length := by
  induction l generalizing b with grind

theorem foldr_add_const {l : List α} {a b : Nat} :
    l.foldr (fun _ x => x + a) b = b + a * l.length := by
  induction l generalizing b with grind

/-! #### Further results about `getLast` and `getLast?` -/

theorem head_reverse {l : List α} (h : l.reverse ≠ []) :
    l.reverse.head h = getLast l (by simp_all) := by
  induction l with grind

theorem mem_of_getLast? {xs : List α} {a : α} (h : xs.getLast? = some a) : a ∈ xs := by
  grind

theorem getLast_reverse {l : List α} (h : l.reverse ≠ []) :
    l.reverse.getLast h = l.head (by simp_all) := by
  grind

theorem head_eq_getLast_reverse {l : List α} (h : l ≠ []) :
    l.head h = l.reverse.getLast (by simp_all) := by
  grind

theorem getLast_append_of_ne_nil {l : List α} (h₁) (h₂ : l' ≠ []) :
    (l ++ l').getLast h₁ = l'.getLast h₂ := by
  grind

theorem getLast?_append {l l' : List α} : (l ++ l').getLast? = l'.getLast?.or l.getLast? := by
  grind

/-! ### leftpad -/

theorem leftpad_prefix {n : Nat} {a : α} {l : List α} :
    replicate (n - length l) a <+: leftpad n a l := by
  grind

theorem leftpad_suffix {n : Nat} {a : α} {l : List α} : l <:+ (leftpad n a l) := by
  grind

/-! ### elem / contains -/

theorem elem_cons_self [BEq α] [LawfulBEq α] {a : α} : (a::as).elem a = true := by grind

theorem contains_iff_exists_mem_beq [BEq α] {l : List α} {a : α} :
    l.contains a ↔ ∃ a' ∈ l, a == a' := by
  induction l with grind

/-! ### dropLast -/

theorem length_dropLast {xs : List α} : xs.dropLast.length = xs.length - 1 := by
  induction xs with grind

theorem getElem_dropLast : ∀ {xs : List α} {i : Nat} (h : i < xs.dropLast.length),
    xs.dropLast[i] = xs[i]'(by grind)
  | _ :: _ :: _, 0, _ => by grind
  | _ :: _ :: _, _ + 1, h => by grind

theorem head?_dropLast {xs : List α} : xs.dropLast.head? = if 1 < xs.length then xs.head? else none := by
  cases xs with
  | nil => grind
  | cons x xs => cases xs with grind

theorem getLast?_dropLast {xs : List α} :
    xs.dropLast.getLast? = if xs.length ≤ 1 then none else xs[xs.length - 2]? := by
  grind

/-! ### replace -/
section replace
variable [BEq α]

theorem getElem?_replace [LawfulBEq α] {l : List α} {i : Nat} :
    (l.replace a b)[i]? = if l[i]? == some a then if a ∈ l.take i then some a else some b else l[i]? := by
  induction l generalizing i with cases i with grind

theorem getElem_replace [LawfulBEq α] {l : List α} {i : Nat} (h : i < l.length) :
    (l.replace a b)[i]'(by grind) = if l[i] == a then if a ∈ l.take i then a else b else l[i] := by
  grind

theorem head?_replace {l : List α} {a b : α} :
    (l.replace a b).head? = match l.head? with
      | none => none
      | some x => some (if a == x then b else x) := by
  cases l with grind

theorem replace_take {l : List α} {i : Nat} :
    (l.take i).replace a b = (l.replace a b).take i := by
  induction l generalizing i with
  | nil => grind
  | cons x xs ih => cases i with grind

theorem replace_replicate_ne [LawfulBEq α] {a b c : α} (h : !b == a) :
    (replicate n a).replace b c = replicate n a := by
  grind [replace_of_not_mem]

end replace

/-! ### insert -/

section insert
variable [BEq α]

variable [LawfulBEq α]

theorem getElem?_insert {l : List α} {a : α} {i : Nat} :
    (l.insert a)[i]? = if a ∈ l then l[i]? else if i = 0 then some a else l[i-1]? := by
  grind

theorem getElem_insert {l : List α} {a : α} {i : Nat} (h : i < l.length) :
    (l.insert a)[i]'(Nat.lt_of_lt_of_le h length_le_length_insert) =
      if a ∈ l then l[i] else if i = 0 then a else l[i-1]'(Nat.lt_of_le_of_lt (Nat.pred_le _) h) := by
  grind

end insert

/-! ### any / all -/

theorem any_replicate {n : Nat} {a : α} :
    (replicate n a).any f = if n = 0 then false else f a := by
  cases n with grind

theorem all_replicate {n : Nat} {a : α} :
    (replicate n a).all f = if n = 0 then true else f a := by
  cases n with grind

theorem any_insert [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    (l.insert a).any f = (f a || l.any f) := by
  grind

theorem all_insert [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    (l.insert a).all f = (f a && l.all f) := by
  grind

end Hidden
