/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.Bool
import Init.Data.Option.Lemmas
import Init.Data.List.BasicAux
import Init.Data.List.Control
import Init.Control.Lawful.Basic
import Init.BinderPredicates

/-! # Theorems about `List` operations.

For each `List` operation, we would like theorems describing the following, when relevant:
* if it is a "convenience" function, a `@[simp]` lemma reducing it to more basic operations
  (e.g. `List.partition_eq_filter_filter`), and otherwise:
* any special cases of equational lemmas that require additional hypotheses
* lemmas for special cases of the arguments (e.g. `List.map_id`)
* the length of the result `(f L).length`
* the `i`-th element, described via `(f L)[i]` and/or `(f L)[i]?` (these should typically be `@[simp]`)
* consequences for `f L` of the fact `x ∈ L` or `x ∉ L`
* conditions characterising `x ∈ f L` (often but not always `@[simp]`)
* injectivity statements, or congruence statements of the form `p L M → f L = f M`.
* conditions characterising the result, i.e. of the form `f L = M ↔ p M` for some predicate `p`,
  along with special cases of `M` (e.g. `List.append_eq_nil : L ++ M = [] ↔ L = [] ∧ M = []`)
* negative characterisations are also useful, e.g. `List.cons_ne_nil`
* interactions with all previously described `List` operations where possible
  (some of these should be `@[simp]`, particularly if the result can be described by a single operation)
* characterising `(∀ (i) (_ : i ∈ f L), P i)`, for some predicate `P`

Of course for any individual operation, not all of these will be relevant or helpful, so some judgement is required.

General principles for `simp` normal forms for `List` operations:
* Conversion operations (e.g. `toArray`, or `length`) should be moved inwards aggressively,
  to make the conversion effective.
* Similarly, operations which work on elements should be moved inwards in preference to
  "structural" operations on the list, e.g. we prefer to simplify
  `List.map f (L ++ M) ~> (List.map f L) ++ (List.map f M)`,
  `List.map f L.reverse ~> (List.map f L).reverse`, and
  `List.map f (L.take n) ~> (List.map f L).take n`.
* Arithmetic operations are "light", so e.g. we prefer to simplify `drop i (drop j L)` to `drop (i + j) L`,
  rather than the other way round.
* Function compositions are "light", so we prefer to simplify `(L.map f).map g` to `L.map (g ∘ f)`.
* We try to avoid non-linear left hand sides (i.e. with subexpressions appearing multiple times),
  but this is only a weak preference.
* Generally, we prefer that the right hand side does not introduce duplication,
  however generally duplication of higher order arguments (functions, predicates, etc) is allowed,
  as we expect to be able to compute these once they reach ground terms.

See also
* `Init.Data.List.Attach` for definitions and lemmas about `List.attach` and `List.pmap`.
* `Init.Data.List.Count` for lemmas about `List.countP` and `List.count`.
* `Init.Data.List.Erase` for lemmas about `List.eraseP` and `List.erase`.
* `Init.Data.List.Find` for lemmas about `List.find?`, `List.findSome?`, `List.findIdx`,
  `List.findIdx?`, and `List.indexOf`
* `Init.Data.List.MinMax` for lemmas about `List.min?` and `List.max?`.
* `Init.Data.List.Pairwise` for lemmas about `List.Pairwise` and `List.Nodup`.
* `Init.Data.List.Sublist` for lemmas about `List.Subset`, `List.Sublist`, `List.IsPrefix`,
  `List.IsSuffix`, and `List.IsInfix`.
* `Init.Data.List.TakeDrop` for additional lemmas about `List.take` and `List.drop`.
* `Init.Data.List.Zip` for lemmas about `List.zip`, `List.zipWith`, `List.zipWithAll`,
  and `List.unzip`.

Further results, which first require developing further automation around `Nat`, appear in
* `Init.Data.List.Nat.Basic`: miscellaneous lemmas
* `Init.Data.List.Nat.Range`: `List.range` and `List.enum`
* `Init.Data.List.Nat.TakeDrop`: `List.take` and `List.drop`

Also
* `Init.Data.List.Monadic` for addiation lemmas about `List.mapM` and `List.forM`.

-/
namespace List

open Nat

/-! ## Preliminaries -/

/-! ### nil -/

@[simp] theorem nil_eq {α} {xs : List α} : [] = xs ↔ xs = [] := by
  cases xs <;> simp

/-! ### cons -/

theorem cons_ne_nil (a : α) (l : List α) : a :: l ≠ [] := nofun

@[simp]
theorem cons_ne_self (a : α) (l : List α) : a :: l ≠ l := mt (congrArg length) (Nat.succ_ne_self _)

@[simp] theorem ne_cons_self {a : α} {l : List α} : l ≠ a :: l := by
  rw [ne_eq, eq_comm]
  simp

theorem head_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : h₁ = h₂ := (cons.inj H).1

theorem tail_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : t₁ = t₂ := (cons.inj H).2

theorem cons_inj_right (a : α) {l l' : List α} : a :: l = a :: l' ↔ l = l' :=
  ⟨tail_eq_of_cons_eq, congrArg _⟩

@[deprecated (since := "2024-06-15")] abbrev cons_inj := @cons_inj_right

theorem cons_eq_cons {a b : α} {l l' : List α} : a :: l = b :: l' ↔ a = b ∧ l = l' :=
  List.cons.injEq .. ▸ .rfl

theorem exists_cons_of_ne_nil : ∀ {l : List α}, l ≠ [] → ∃ b L, l = b :: L
  | c :: l', _ => ⟨c, l', rfl⟩

theorem singleton_inj {α : Type _} {a b : α} : [a] = [b] ↔ a = b := by
  simp

/-! ### length -/

theorem eq_nil_of_length_eq_zero (_ : length l = 0) : l = [] := match l with | [] => rfl

theorem ne_nil_of_length_eq_add_one (_ : length l = n + 1) : l ≠ [] := fun _ => nomatch l

@[deprecated ne_nil_of_length_eq_add_one (since := "2024-06-16")]
abbrev ne_nil_of_length_eq_succ := @ne_nil_of_length_eq_add_one

theorem ne_nil_of_length_pos (_ : 0 < length l) : l ≠ [] := fun _ => nomatch l

@[simp] theorem length_eq_zero : length l = 0 ↔ l = [] :=
  ⟨eq_nil_of_length_eq_zero, fun h => h ▸ rfl⟩

theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
  | _::_, _ => Nat.zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
  | _::_, _ => ⟨_, .head ..⟩

theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
  ⟨exists_mem_of_length_pos, fun ⟨_, h⟩ => length_pos_of_mem h⟩

theorem exists_mem_of_length_eq_add_one :
    ∀ {l : List α}, l.length = n + 1 → ∃ a, a ∈ l
  | _::_, _ => ⟨_, .head ..⟩

theorem exists_cons_of_length_pos : ∀ {l : List α}, 0 < l.length → ∃ h t, l = h :: t
  | _::_, _ => ⟨_, _, rfl⟩

theorem length_pos_iff_exists_cons :
    ∀ {l : List α}, 0 < l.length ↔ ∃ h t, l = h :: t :=
  ⟨exists_cons_of_length_pos, fun ⟨_, _, eq⟩ => eq ▸ Nat.succ_pos _⟩

theorem exists_cons_of_length_eq_add_one :
    ∀ {l : List α}, l.length = n + 1 → ∃ h t, l = h :: t
  | _::_, _ => ⟨_, _, rfl⟩

theorem length_pos {l : List α} : 0 < length l ↔ l ≠ [] :=
  Nat.pos_iff_ne_zero.trans (not_congr length_eq_zero)

theorem length_eq_one {l : List α} : length l = 1 ↔ ∃ a, l = [a] :=
  ⟨fun h => match l, h with | [_], _ => ⟨_, rfl⟩, fun ⟨_, h⟩ => by simp [h]⟩

/-! ## L[i] and L[i]? -/

/-! ### `get` and `get?`.

We simplify `l.get i` to `l[i.1]'i.2` and `l.get? i` to `l[i]?`.
-/

theorem get_cons_zero : get (a::l) (0 : Fin (l.length + 1)) = a := rfl

theorem get_cons_succ {as : List α} {h : i + 1 < (a :: as).length} :
  (a :: as).get ⟨i+1, h⟩ = as.get ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

theorem get_cons_succ' {as : List α} {i : Fin as.length} :
  (a :: as).get i.succ = as.get i := rfl

@[deprecated (since := "2024-07-09")]
theorem get_cons_cons_one : (a₁ :: a₂ :: as).get (1 : Fin (as.length + 2)) = a₂ := rfl

theorem get_mk_zero : ∀ {l : List α} (h : 0 < l.length), l.get ⟨0, h⟩ = l.head (length_pos.mp h)
  | _::_, _ => rfl

theorem get?_zero (l : List α) : l.get? 0 = l.head? := by cases l <;> rfl

theorem get?_len_le : ∀ {l : List α} {n}, length l ≤ n → l.get? n = none
  | [], _, _ => rfl
  | _ :: l, _+1, h => get?_len_le (l := l) <| Nat.le_of_succ_le_succ h

theorem get?_eq_get : ∀ {l : List α} {n} (h : n < l.length), l.get? n = some (get l ⟨n, h⟩)
  | _ :: _, 0, _ => rfl
  | _ :: l, _+1, _ => get?_eq_get (l := l) _

theorem get?_eq_some : l.get? n = some a ↔ ∃ h, get l ⟨n, h⟩ = a :=
  ⟨fun e =>
    have : n < length l := Nat.gt_of_not_le fun hn => by cases get?_len_le hn ▸ e
    ⟨this, by rwa [get?_eq_get this, Option.some.injEq] at e⟩,
  fun ⟨_, e⟩ => e ▸ get?_eq_get _⟩

theorem get?_eq_none : l.get? n = none ↔ length l ≤ n :=
  ⟨fun e => Nat.ge_of_not_lt (fun h' => by cases e ▸ get?_eq_some.2 ⟨h', rfl⟩), get?_len_le⟩

@[simp] theorem get?_eq_getElem? (l : List α) (i : Nat) : l.get? i = l[i]? := by
  simp only [getElem?, decidableGetElem?]; split
  · exact (get?_eq_get ‹_›)
  · exact (get?_eq_none.2 <| Nat.not_lt.1 ‹_›)

@[simp] theorem get_eq_getElem (l : List α) (i : Fin l.length) : l.get i = l[i.1]'i.2 := rfl

theorem getElem?_eq_some {l : List α} : l[i]? = some a ↔ ∃ h : i < l.length, l[i]'h = a := by
  simpa using get?_eq_some

/--
If one has `l.get i` in an expression (with `i : Fin l.length`) and `h : l = l'`,
`rw [h]` will give a "motive it not type correct" error, as it cannot rewrite the
`i : Fin l.length` to `Fin l'.length` directly. The theorem `get_of_eq` can be used to make
such a rewrite, with `rw [get_of_eq h]`.
-/
theorem get_of_eq {l l' : List α} (h : l = l') (i : Fin l.length) :
    get l i = get l' ⟨i, h ▸ i.2⟩ := by cases h; rfl

/-! ### getD

We simplify away `getD`, replacing `getD l n a` with `(l[n]?).getD a`.
Because of this, there is only minimal API for `getD`.
-/

@[simp] theorem getD_eq_getElem?_getD (l) (n) (a : α) : getD l n a = (l[n]?).getD a := by
  simp [getD]

@[deprecated getD_eq_getElem?_getD (since := "2024-06-12")]
theorem getD_eq_get? : ∀ l n (a : α), getD l n a = (get? l n).getD a := by simp

/-! ### get!

We simplify `l.get! n` to `l[n]!`.
-/

theorem get!_of_get? [Inhabited α] : ∀ {l : List α} {n}, get? l n = some a → get! l n = a
  | _a::_, 0, rfl => rfl
  | _::l, _+1, e => get!_of_get? (l := l) e

theorem get!_eq_getD [Inhabited α] : ∀ (l : List α) n, l.get! n = l.getD n default
  | [], _      => rfl
  | _a::_, 0   => rfl
  | _a::l, n+1 => get!_eq_getD l n

theorem get!_len_le [Inhabited α] : ∀ {l : List α} {n}, length l ≤ n → l.get! n = (default : α)
  | [], _, _ => rfl
  | _ :: l, _+1, h => get!_len_le (l := l) <| Nat.le_of_succ_le_succ h

@[simp] theorem get!_eq_getElem! [Inhabited α] (l : List α) (n) : l.get! n = l[n]! := by
  simp [get!_eq_getD]
  rfl

/-! ### getElem! -/

@[simp] theorem getElem!_nil [Inhabited α] {n : Nat} : ([] : List α)[n]! = default := rfl

@[simp] theorem getElem!_cons_zero [Inhabited α] {l : List α} : (a::l)[0]! = a := by
  rw [getElem!_pos] <;> simp

@[simp] theorem getElem!_cons_succ [Inhabited α] {l : List α} : (a::l)[n+1]! = l[n]! := by
  by_cases h : n < l.length
  · rw [getElem!_pos, getElem!_pos] <;> simp_all [Nat.succ_lt_succ_iff]
  · rw [getElem!_neg, getElem!_neg] <;> simp_all [Nat.succ_lt_succ_iff]

/-! ### getElem? and getElem -/

@[simp] theorem getElem?_eq_getElem {l : List α} {n} (h : n < l.length) : l[n]? = some l[n] := by
  simp only [getElem?_def, h, ↓reduceDIte]

theorem getElem?_eq_some_iff {l : List α} : l[n]? = some a ↔ ∃ h : n < l.length, l[n] = a := by
  simp only [← get?_eq_getElem?, get?_eq_some, get_eq_getElem]

theorem some_eq_getElem?_iff {l : List α} : some a = l[n]? ↔ ∃ h : n < l.length, l[n] = a := by
  rw [eq_comm, getElem?_eq_some_iff]

@[simp] theorem getElem?_eq_none_iff : l[n]? = none ↔ length l ≤ n := by
  simp only [← get?_eq_getElem?, get?_eq_none]

@[simp] theorem none_eq_getElem?_iff {l : List α} {n : Nat} : none = l[n]? ↔ length l ≤ n := by
  simp [eq_comm (a := none)]

theorem getElem?_eq_none (h : length l ≤ n) : l[n]? = none := getElem?_eq_none_iff.mpr h

theorem getElem?_eq (l : List α) (i : Nat) :
    l[i]? = if h : i < l.length then some l[i] else none := by
  split <;> simp_all

@[simp] theorem some_getElem_eq_getElem?_iff {α} (xs : List α) (i : Nat) (h : i < xs.length) :
    (some xs[i] = xs[i]?) ↔ True := by
  simp [h]

@[simp] theorem getElem?_eq_some_getElem_iff {α} (xs : List α) (i : Nat) (h : i < xs.length) :
    (xs[i]? = some xs[i]) ↔ True := by
  simp [h]

theorem getElem_eq_iff {l : List α} {n : Nat} {h : n < l.length} : l[n] = x ↔ l[n]? = some x := by
  simp only [getElem?_eq_some_iff]
  exact ⟨fun w => ⟨h, w⟩, fun h => h.2⟩

theorem getElem_eq_getElem?_get (l : List α) (i : Nat) (h : i < l.length) :
    l[i] = l[i]?.get (by simp [getElem?_eq_getElem, h]) := by
  simp [getElem_eq_iff]

@[deprecated getElem_eq_getElem?_get (since := "2024-09-04")] abbrev getElem_eq_getElem? :=
  @getElem_eq_getElem?_get

@[simp] theorem getElem?_nil {n : Nat} : ([] : List α)[n]? = none := rfl

theorem getElem?_cons_zero {l : List α} : (a::l)[0]? = some a := by simp

@[simp] theorem getElem?_cons_succ {l : List α} : (a::l)[n+1]? = l[n]? := by
  simp only [← get?_eq_getElem?]
  rfl

theorem getElem?_cons : (a :: l)[i]? = if i = 0 then some a else l[i-1]? := by
  cases i <;> simp

theorem getElem?_len_le : ∀ {l : List α} {n}, length l ≤ n → l[n]? = none
  | [], _, _ => rfl
  | _ :: l, _+1, h => by
    rw [getElem?_cons_succ, getElem?_len_le (l := l) <| Nat.le_of_succ_le_succ h]

/--
If one has `l[i]` in an expression and `h : l = l'`,
`rw [h]` will give a "motive it not type correct" error, as it cannot rewrite the
implicit `i < l.length` to `i < l'.length` directly. The theorem `getElem_of_eq` can be used to make
such a rewrite, with `rw [getElem_of_eq h]`.
-/
theorem getElem_of_eq {l l' : List α} (h : l = l') {i : Nat} (w : i < l.length) :
    l[i] = l'[i]'(h ▸ w) := by cases h; rfl

@[simp] theorem getElem_singleton (a : α) (h : i < 1) : [a][i] = a :=
  match i, h with
  | 0, _ => rfl

@[deprecated getElem_singleton (since := "2024-06-12")]
theorem get_singleton (a : α) (n : Fin 1) : get [a] n = a := by simp

theorem getElem_zero {l : List α} (h : 0 < l.length) : l[0] = l.head (length_pos.mp h) :=
  match l, h with
  | _ :: _, _ => rfl

theorem getElem!_of_getElem? [Inhabited α] : ∀ {l : List α} {n : Nat}, l[n]? = some a → l[n]! = a
  | _a::_, 0, _ => by
    rw [getElem!_pos] <;> simp_all
  | _::l, _+1, e => by
    simp at e
    simp_all [getElem!_of_getElem? (l := l) e]

@[ext] theorem ext_getElem? {l₁ l₂ : List α} (h : ∀ n : Nat, l₁[n]? = l₂[n]?) : l₁ = l₂ :=
  ext_get? fun n => by simp_all

theorem ext_getElem {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ (n : Nat) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁[n]'h₁ = l₂[n]'h₂) : l₁ = l₂ :=
  ext_getElem? fun n =>
    if h₁ : n < length l₁ then by
      simp_all [getElem?_eq_getElem]
    else by
      have h₁ := Nat.le_of_not_lt h₁
      rw [getElem?_len_le h₁, getElem?_len_le]; rwa [← hl]

theorem ext_get {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ n h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩) : l₁ = l₂ :=
  ext_getElem hl (by simp_all)

@[simp] theorem getElem_concat_length : ∀ (l : List α) (a : α) (i) (_ : i = l.length) (w), (l ++ [a])[i]'w = a
  | [], a, _, h, _ => by subst h; simp
  | _ :: l, a, _, h, _ => by simp [getElem_concat_length, h]

theorem getElem?_concat_length (l : List α) (a : α) : (l ++ [a])[l.length]? = some a := by
  simp

@[deprecated getElem?_concat_length (since := "2024-06-12")]
theorem get?_concat_length (l : List α) (a : α) : (l ++ [a]).get? l.length = some a := by simp

/-! ### mem -/

@[simp] theorem not_mem_nil (a : α) : ¬ a ∈ [] := nofun

@[simp] theorem mem_cons : a ∈ (b :: l) ↔ a = b ∨ a ∈ l :=
  ⟨fun h => by cases h <;> simp [Membership.mem, *],
   fun | Or.inl rfl => by constructor | Or.inr h => by constructor; assumption⟩

theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l := .head ..

theorem mem_concat_self (xs : List α) (a : α) : a ∈ xs ++ [a] :=
  mem_append_of_mem_right xs (mem_cons_self a _)

theorem mem_append_cons_self : a ∈ xs ++ a :: ys := mem_append_of_mem_right _ (mem_cons_self _ _)

theorem eq_append_cons_of_mem {a : α} {xs : List α} (h : a ∈ xs) :
    ∃ as bs, xs = as ++ a :: bs ∧ a ∉ as := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    simp at h
    cases h with
    | inl h => exact ⟨[], xs, by simp_all⟩
    | inr h =>
      by_cases h' : a = x
      · subst h'
        exact ⟨[], xs, by simp⟩
      · obtain ⟨as, bs, rfl, h⟩ := ih h
        exact ⟨x :: as, bs, rfl, by simp_all⟩

theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := .tail _

theorem exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
  exists_mem_of_length_pos (length_pos.2 h)

theorem eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  cases l <;> simp [-not_or]

@[simp] theorem mem_dite_nil_left {x : α} [Decidable p] {l : ¬ p → List α} :
    (x ∈ if h : p then [] else l h) ↔ ∃ h : ¬ p, x ∈ l h := by
  split <;> simp_all

@[simp] theorem mem_dite_nil_right {x : α} [Decidable p] {l : p → List α} :
    (x ∈ if h : p then l h else []) ↔ ∃ h : p, x ∈ l h := by
  split <;> simp_all

@[simp] theorem mem_ite_nil_left {x : α} [Decidable p] {l : List α} :
    (x ∈ if p then [] else l) ↔ ¬ p ∧ x ∈ l := by
  split <;> simp_all

@[simp] theorem mem_ite_nil_right {x : α} [Decidable p] {l : List α} :
    (x ∈ if p then l else []) ↔ p ∧ x ∈ l := by
  split <;> simp_all

theorem eq_of_mem_singleton : a ∈ [b] → a = b
  | .head .. => rfl

@[simp 1100] theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
  ⟨eq_of_mem_singleton, (by simp [·])⟩

theorem forall_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∀ x, x ∈ a :: l → p x) ↔ p a ∧ ∀ x, x ∈ l → p x :=
  ⟨fun H => ⟨H _ (.head ..), fun _ h => H _ (.tail _ h)⟩,
   fun ⟨H₁, H₂⟩ _ => fun | .head .. => H₁ | .tail _ h => H₂ _ h⟩

theorem forall_mem_ne {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

theorem forall_mem_ne' {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a' = a) ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

theorem exists_mem_nil (p : α → Prop) : ¬ (∃ x, ∃ _ : x ∈ @nil α, p x) := nofun

theorem forall_mem_nil (p : α → Prop) : ∀ (x) (_ : x ∈ @nil α), p x := nofun

theorem exists_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∃ x, ∃ _ : x ∈ a :: l, p x) ↔ p a ∨ ∃ x, ∃ _ : x ∈ l, p x := by simp

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ (x) (_ : x ∈ [a]), p x) ↔ p a := by
  simp only [mem_singleton, forall_eq]

theorem mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False := by simp

theorem mem_singleton_self (a : α) : a ∈ [a] := mem_cons_self _ _

theorem mem_of_mem_cons_of_mem : ∀ {a b : α} {l : List α}, a ∈ b :: l → b ∈ l → a ∈ l
  | _, _, _, .head .., h | _, _, _, .tail _ h, _ => h

theorem eq_or_ne_mem_of_mem {a b : α} {l : List α} (h' : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) :=
  (Classical.em _).imp_right fun h => ⟨h, (mem_cons.1 h').resolve_left h⟩

theorem ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by cases h <;> nofun

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
  Or.elim (mem_cons.mp h₂) (absurd · h₁) (·)

theorem ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b :: l → a ≠ b := mt (· ▸ .head _)

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : a ∉ b :: l → a ∉ l := mt (.tail _)

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y :: l :=
  mt ∘ mem_of_ne_of_mem

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : a ∉ y :: l → a ≠ y ∧ a ∉ l :=
  fun p => ⟨ne_of_not_mem_cons p, not_mem_of_not_mem_cons p⟩

theorem getElem_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ (n : Nat) (h : n < l.length), l[n]'h = a
  | _, _ :: _, .head .. => ⟨0, Nat.succ_pos _, rfl⟩
  | _, _ :: _, .tail _ m => let ⟨n, h, e⟩ := getElem_of_mem m; ⟨n+1, Nat.succ_lt_succ h, e⟩

theorem get_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n, get l n = a := by
  obtain ⟨n, h, e⟩ := getElem_of_mem h
  exact ⟨⟨n, h⟩, e⟩

theorem getElem?_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n : Nat, l[n]? = some a :=
  let ⟨n, _, e⟩ := getElem_of_mem h; ⟨n, e ▸ getElem?_eq_getElem _⟩

theorem get?_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n, l.get? n = some a :=
  let ⟨⟨n, _⟩, e⟩ := get_of_mem h; ⟨n, e ▸ get?_eq_get _⟩

theorem get_mem : ∀ (l : List α) n h, get l ⟨n, h⟩ ∈ l
  | _ :: _, 0, _ => .head ..
  | _ :: l, _+1, _ => .tail _ (get_mem l ..)

theorem getElem?_mem {l : List α} {n : Nat} {a : α} (e : l[n]? = some a) : a ∈ l :=
  let ⟨_, e⟩ := getElem?_eq_some_iff.1 e; e ▸ getElem_mem ..

theorem get?_mem {l : List α} {n a} (e : l.get? n = some a) : a ∈ l :=
  let ⟨_, e⟩ := get?_eq_some.1 e; e ▸ get_mem ..

theorem mem_iff_getElem {a} {l : List α} : a ∈ l ↔ ∃ (n : Nat) (h : n < l.length), l[n]'h = a :=
  ⟨getElem_of_mem, fun ⟨_, _, e⟩ => e ▸ getElem_mem ..⟩

theorem mem_iff_get {a} {l : List α} : a ∈ l ↔ ∃ n, get l n = a :=
  ⟨get_of_mem, fun ⟨_, e⟩ => e ▸ get_mem ..⟩

theorem mem_iff_getElem? {a} {l : List α} : a ∈ l ↔ ∃ n : Nat, l[n]? = some a := by
  simp [getElem?_eq_some_iff, mem_iff_getElem]

theorem mem_iff_get? {a} {l : List α} : a ∈ l ↔ ∃ n, l.get? n = some a := by
  simp [getElem?_eq_some_iff, Fin.exists_iff, mem_iff_get]

theorem forall_getElem {l : List α} {p : α → Prop} :
    (∀ (n : Nat) h, p (l[n]'h)) ↔ ∀ a, a ∈ l → p a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [length_cons, mem_cons, forall_eq_or_imp]
    constructor
    · intro w
      constructor
      · exact w 0 (by simp)
      · apply ih.1
        intro n h
        simpa using w (n+1) (Nat.add_lt_add_right h 1)
    · rintro ⟨h, w⟩
      rintro (_ | n) h
      · simpa
      · apply w
        simp only [getElem_cons_succ]
        exact getElem_mem (lt_of_succ_lt_succ h)

@[simp] theorem decide_mem_cons [BEq α] [LawfulBEq α] {l : List α} :
    decide (y ∈ a :: l) = (y == a || decide (y ∈ l)) := by
  cases h : y == a <;> simp_all

theorem elem_iff [BEq α] [LawfulBEq α] {a : α} {as : List α} :
    elem a as = true ↔ a ∈ as := ⟨mem_of_elem_eq_true, elem_eq_true_of_mem⟩

@[simp] theorem elem_eq_mem [BEq α] [LawfulBEq α] (a : α) (as : List α) :
    elem a as = decide (a ∈ as) := by rw [Bool.eq_iff_iff, elem_iff, decide_eq_true_iff]

/-! ### `isEmpty` -/

theorem isEmpty_iff {l : List α} : l.isEmpty ↔ l = [] := by
  cases l <;> simp

theorem isEmpty_eq_false_iff_exists_mem {xs : List α} :
    (List.isEmpty xs = false) ↔ ∃ x, x ∈ xs := by
  cases xs <;> simp

theorem isEmpty_iff_length_eq_zero {l : List α} : l.isEmpty ↔ l.length = 0 := by
  rw [isEmpty_iff, length_eq_zero]

@[simp] theorem isEmpty_eq_true {l : List α} : l.isEmpty ↔ l = [] := by
  cases l <;> simp

@[simp] theorem isEmpty_eq_false {l : List α} : l.isEmpty = false ↔ l ≠ [] := by
  cases l <;> simp

/-! ### any / all -/

theorem any_beq [BEq α] [LawfulBEq α] {l : List α} : (l.any fun x => a == x) ↔ a ∈ l := by
  induction l <;> simp_all

theorem any_beq' [BEq α] [LawfulBEq α] {l : List α} : (l.any fun x => x == a) ↔ a ∈ l := by
  induction l <;> simp_all [eq_comm (a := a)]

theorem all_bne [BEq α] [LawfulBEq α] {l : List α} : (l.all fun x => a != x) ↔ a ∉ l := by
  induction l <;> simp_all

theorem all_bne' [BEq α] [LawfulBEq α] {l : List α} : (l.all fun x => x != a) ↔ a ∉ l := by
  induction l <;> simp_all [eq_comm (a := a)]

theorem any_eq {l : List α} : l.any p = decide (∃ x, x ∈ l ∧ p x) := by induction l <;> simp [*]

theorem all_eq {l : List α} : l.all p = decide (∀ x, x ∈ l → p x) := by induction l <;> simp [*]

theorem decide_exists_mem {l : List α} {p : α → Prop} [DecidablePred p] :
    decide (∃ x, x ∈ l ∧ p x) = l.any p := by
  simp [any_eq]

theorem decide_forall_mem {l : List α} {p : α → Prop} [DecidablePred p] :
    decide (∀ x, x ∈ l → p x) = l.all p := by
  simp [all_eq]

@[simp] theorem any_eq_true {l : List α} : l.any p = true ↔ ∃ x, x ∈ l ∧ p x := by
  simp only [any_eq, decide_eq_true_eq]

@[simp] theorem all_eq_true {l : List α} : l.all p = true ↔ ∀ x, x ∈ l → p x := by
  simp only [all_eq, decide_eq_true_eq]

@[simp] theorem any_eq_false {l : List α} : l.any p = false ↔ ∀ x, x ∈ l → ¬p x := by
  simp [any_eq]

@[simp] theorem all_eq_false {l : List α} : l.all p = false ↔ ∃ x, x ∈ l ∧ ¬p x := by
  simp [all_eq]

/-! ### set -/

-- As `List.set` is defined in `Init.Prelude`, we write the basic simplification lemmas here.
@[simp] theorem set_nil (n : Nat) (a : α) : [].set n a = [] := rfl
@[simp] theorem set_cons_zero (x : α) (xs : List α) (a : α) :
  (x :: xs).set 0 a = a :: xs := rfl
@[simp] theorem set_cons_succ (x : α) (xs : List α) (n : Nat) (a : α) :
  (x :: xs).set (n + 1) a = x :: xs.set n a := rfl

@[simp] theorem getElem_set_self {l : List α} {i : Nat} {a : α} (h : i < (l.set i a).length) :
    (l.set i a)[i] = a :=
  match l, i with
  | [], _ => by
    simp at h
  | _ :: _, 0 => by simp
  | _ :: l, i + 1 => by simp [getElem_set_self]

@[deprecated getElem_set_self (since := "2024-09-04")] abbrev getElem_set_eq := @getElem_set_self

@[deprecated getElem_set_self (since := "2024-06-12")]
theorem get_set_eq {l : List α} {i : Nat} {a : α} (h : i < (l.set i a).length) :
    (l.set i a).get ⟨i, h⟩ = a := by
  simp

@[simp] theorem getElem?_set_self {l : List α} {i : Nat} {a : α} (h : i < l.length) :
    (l.set i a)[i]? = some a := by
  simp_all [getElem?_eq_some_iff]

@[deprecated getElem?_set_self (since := "2024-09-04")] abbrev getElem?_set_eq := @getElem?_set_self

/-- This differs from `getElem?_set_self` by monadically mapping `Function.const _ a` over the `Option`
returned by `l[i]?`. -/
theorem getElem?_set_self' {l : List α} {i : Nat} {a : α} :
    (set l i a)[i]? = Function.const _ a <$> l[i]? := by
  by_cases h : i < l.length
  · simp [getElem?_set_self h, getElem?_eq_getElem h]
  · simp only [Nat.not_lt] at h
    simpa [getElem?_eq_none_iff.2 h]

@[simp] theorem getElem_set_ne {l : List α} {i j : Nat} (h : i ≠ j) {a : α}
    (hj : j < (l.set i a).length) :
    (l.set i a)[j] = l[j]'(by simp at hj; exact hj) :=
  match l, i, j with
  | [], _, _ => by simp
  | _ :: _, 0, 0 => by contradiction
  | _ :: _, 0, _ + 1 => by simp
  | _ :: _, _ + 1, 0 => by simp
  | _ :: l, i + 1, j + 1 => by
    have g : i ≠ j := h ∘ congrArg (· + 1)
    simp [getElem_set_ne g]

@[deprecated getElem_set_ne (since := "2024-06-12")]
theorem get_set_ne {l : List α} {i j : Nat} (h : i ≠ j) {a : α}
    (hj : j < (l.set i a).length) :
    (l.set i a).get ⟨j, hj⟩ = l.get ⟨j, by simp at hj; exact hj⟩ := by
  simp [h]

@[simp] theorem getElem?_set_ne {l : List α} {i j : Nat} (h : i ≠ j) {a : α}  :
    (l.set i a)[j]? = l[j]? := by
  by_cases hj : j < (l.set i a).length
  · rw [getElem?_eq_getElem hj, getElem?_eq_getElem (by simp_all)]
    simp_all
  · rw [getElem?_eq_none (by simp_all), getElem?_eq_none (by simp_all)]

theorem getElem_set {l : List α} {m n} {a} (h) :
    (set l m a)[n]'h = if m = n then a else l[n]'(length_set .. ▸ h) := by
  if h : m = n then
    subst m; simp only [getElem_set_self, ↓reduceIte]
  else
    simp [h]

@[deprecated getElem_set (since := "2024-06-12")]
theorem get_set {l : List α} {m n} {a : α} (h) :
    (set l m a).get ⟨n, h⟩ = if m = n then a else l.get ⟨n, length_set .. ▸ h⟩ := by
  simp [getElem_set]

theorem getElem?_set {l : List α} {i j : Nat} {a : α} :
    (l.set i a)[j]? = if i = j then if i < l.length then some a else none else l[j]? := by
  if h : i = j then
    subst h
    rw [if_pos rfl]
    split <;> rename_i h
    · simp only [getElem?_set_self (by simpa), h]
    · simp_all
  else
    simp [h]

/-- This differs from `getElem?_set` by monadically mapping `Function.const _ a`
over the `Option` returned by `l[j]`? -/
theorem getElem?_set' {l : List α} {i j : Nat} {a : α} :
    (set l i a)[j]? = if i = j then Function.const _ a <$> l[j]? else l[j]? := by
  by_cases i = j
  · simp only [getElem?_set_self', Option.map_eq_map, ↓reduceIte, *]
  · simp only [ne_eq, not_false_eq_true, getElem?_set_ne, ↓reduceIte, *]

theorem set_eq_of_length_le {l : List α} {n : Nat} (h : l.length ≤ n) {a : α} :
    l.set n a = l := by
  induction l generalizing n with
  | nil => simp_all
  | cons a l ih =>
    induction n
    · simp_all
    · simp only [set_cons_succ, cons.injEq, true_and]
      rw [ih]
      exact Nat.succ_le_succ_iff.mp h

@[simp] theorem set_eq_nil_iff {l : List α} (n : Nat) (a : α) : l.set n a = [] ↔ l = [] := by
  cases l <;> cases n <;> simp [set]

@[deprecated set_eq_nil_iff (since := "2024-09-05")] abbrev set_eq_nil := @set_eq_nil_iff

theorem set_comm (a b : α) : ∀ {n m : Nat} (l : List α), n ≠ m →
    (l.set n a).set m b = (l.set m b).set n a
  | _, _, [], _ => by simp
  | _+1, 0, _ :: _, _ => by simp [set]
  | 0, _+1, _ :: _, _ => by simp [set]
  | _+1, _+1, _ :: t, h =>
    congrArg _ <| set_comm a b t fun h' => h <| Nat.succ_inj'.mpr h'

@[simp]
theorem set_set (a b : α) : ∀ (l : List α) (n : Nat), (l.set n a).set n b = l.set n b
  | [], _ => by simp
  | _ :: _, 0 => by simp [set]
  | _ :: _, _+1 => by simp [set, set_set]

theorem mem_set (l : List α) (n : Nat) (h : n < l.length) (a : α) :
    a ∈ l.set n a := by
  simp [mem_iff_getElem]
  exact ⟨n, (by simpa using h), by simp⟩

theorem mem_or_eq_of_mem_set : ∀ {l : List α} {n : Nat} {a b : α}, a ∈ l.set n b → a ∈ l ∨ a = b
  | _ :: _, 0, _, _, h => ((mem_cons ..).1 h).symm.imp_left (.tail _)
  | _ :: _, _+1, _, _, .head .. => .inl (.head ..)
  | _ :: _, _+1, _, _, .tail _ h => (mem_or_eq_of_mem_set h).imp_left (.tail _)

-- See also `set_eq_take_append_cons_drop` in `Init.Data.List.TakeDrop`.

/-! ### BEq -/

@[simp] theorem reflBEq_iff [BEq α] : ReflBEq (List α) ↔ ReflBEq α := by
  constructor
  · intro h
    constructor
    intro a
    suffices ([a] == [a]) = true by
      simpa only [List.instBEq, List.beq, Bool.and_true]
    simp
  · intro h
    constructor
    intro a
    induction a with
    | nil => simp only [List.instBEq, List.beq]
    | cons a as ih =>
      simp [List.instBEq, List.beq]
      exact ih

@[simp] theorem lawfulBEq_iff [BEq α] : LawfulBEq (List α) ↔ LawfulBEq α := by
  constructor
  · intro h
    constructor
    · intro a b h
      apply singleton_inj.1
      apply eq_of_beq
      simp only [List.instBEq, List.beq]
      simpa
    · intro a
      suffices ([a] == [a]) = true by
        simpa only [List.instBEq, List.beq, Bool.and_true]
      simp
  · intro h
    constructor
    · intro a b h
      simpa using h
    · intro a
      simp

/-! ### Lexicographic ordering -/

protected theorem lt_irrefl [LT α] (lt_irrefl : ∀ x : α, ¬x < x) (l : List α) : ¬l < l := by
  induction l with
  | nil => nofun
  | cons a l ih => intro
    | .head _ _ h => exact lt_irrefl _ h
    | .tail _ _ h => exact ih h

protected theorem lt_trans [LT α] [DecidableRel (@LT.lt α _)]
    (lt_trans : ∀ {x y z : α}, x < y → y < z → x < z)
    (le_trans : ∀ {x y z : α}, ¬x < y → ¬y < z → ¬x < z)
    {l₁ l₂ l₃ : List α} (h₁ : l₁ < l₂) (h₂ : l₂ < l₃) : l₁ < l₃ := by
  induction h₁ generalizing l₃ with
  | nil => let _::_ := l₃; exact List.lt.nil ..
  | @head a l₁ b l₂ ab =>
    match h₂ with
    | .head l₂ l₃ bc => exact List.lt.head _ _ (lt_trans ab bc)
    | .tail _ cb ih =>
      exact List.lt.head _ _ <| Decidable.by_contra (le_trans · cb ab)
  | @tail a l₁ b l₂ ab ba h₁ ih2 =>
    match h₂ with
    | .head l₂ l₃ bc =>
      exact List.lt.head _ _ <| Decidable.by_contra (le_trans ba · bc)
    | .tail bc cb ih =>
      exact List.lt.tail (le_trans ab bc) (le_trans cb ba) (ih2 ih)

protected theorem lt_antisymm [LT α]
    (lt_antisymm : ∀ {x y : α}, ¬x < y → ¬y < x → x = y)
    {l₁ l₂ : List α} (h₁ : ¬l₁ < l₂) (h₂ : ¬l₂ < l₁) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b l₂ => cases h₁ (.nil ..)
  | cons a l₁ ih =>
    cases l₂ with
    | nil => cases h₂ (.nil ..)
    | cons b l₂ =>
      have ab : ¬a < b := fun ab => h₁ (.head _ _ ab)
      cases lt_antisymm ab (fun ba => h₂ (.head _ _ ba))
      rw [ih (fun ll => h₁ (.tail ab ab ll)) (fun ll => h₂ (.tail ab ab ll))]

/-! ### foldlM and foldrM -/

@[simp] theorem foldlM_reverse [Monad m] (l : List α) (f : β → α → m β) (b) :
    l.reverse.foldlM f b = l.foldrM (fun x y => f y x) b := rfl

@[simp] theorem foldlM_append [Monad m] [LawfulMonad m] (f : β → α → m β) (b) (l l' : List α) :
    (l ++ l').foldlM f b = l.foldlM f b >>= l'.foldlM f := by
  induction l generalizing b <;> simp [*]

@[simp] theorem foldrM_cons [Monad m] [LawfulMonad m] (a : α) (l) (f : α → β → m β) (b) :
    (a :: l).foldrM f b = l.foldrM f b >>= f a := by
  simp only [foldrM]
  induction l <;> simp_all

theorem foldl_eq_foldlM (f : β → α → β) (b) (l : List α) :
    l.foldl f b = l.foldlM (m := Id) f b := by
  induction l generalizing b <;> simp [*, foldl]

theorem foldr_eq_foldrM (f : α → β → β) (b) (l : List α) :
    l.foldr f b = l.foldrM (m := Id) f b := by
  induction l <;> simp [*, foldr]

/-! ### foldl and foldr -/

@[simp] theorem foldr_cons_eq_append (l : List α) : l.foldr cons l' = l ++ l' := by
  induction l <;> simp [*]

@[deprecated foldr_cons_eq_append (since := "2024-08-22")] abbrev foldr_self_append := @foldr_cons_eq_append

@[simp] theorem foldl_flip_cons_eq_append (l : List α) : l.foldl (fun x y => y :: x) l' = l.reverse ++ l' := by
  induction l generalizing l' <;> simp [*]

theorem foldr_cons_nil (l : List α) : l.foldr cons [] = l := by simp

@[deprecated foldr_cons_nil (since := "2024-09-04")] abbrev foldr_self := @foldr_cons_nil

theorem foldl_map (f : β₁ → β₂) (g : α → β₂ → α) (l : List β₁) (init : α) :
    (l.map f).foldl g init = l.foldl (fun x y => g x (f y)) init := by
  induction l generalizing init <;> simp [*]

theorem foldr_map (f : α₁ → α₂) (g : α₂ → β → β) (l : List α₁) (init : β) :
    (l.map f).foldr g init = l.foldr (fun x y => g (f x) y) init := by
  induction l generalizing init <;> simp [*]

theorem foldl_filterMap (f : α → Option β) (g : γ → β → γ) (l : List α) (init : γ) :
    (l.filterMap f).foldl g init = l.foldl (fun x y => match f y with | some b => g x b | none => x) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filterMap_cons, foldl_cons]
    cases f a <;> simp [ih]

theorem foldr_filterMap (f : α → Option β) (g : β → γ → γ) (l : List α) (init : γ) :
    (l.filterMap f).foldr g init = l.foldr (fun x y => match f x with | some b => g b y | none => y) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filterMap_cons, foldr_cons]
    cases f a <;> simp [ih]

theorem foldl_map' (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (l.map g).foldl f' (g a) = g (l.foldl f a) := by
  induction l generalizing a
  · simp
  · simp [*, h]

theorem foldr_map' (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (l.map g).foldr f' (g a) = g (l.foldr f a) := by
  induction l generalizing a
  · simp
  · simp [*, h]

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] :
    ∀ {l : List α} {a₁ a₂}, l.foldl op (op a₁ a₂) = op a₁ (l.foldl op a₂)
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ => by
    simp only [foldl_cons, ha.assoc]
    rw [foldl_assoc]

theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] :
    ∀ {l : List α} {a₁ a₂}, l.foldr op (op a₁ a₂) = op (l.foldr op a₁) a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ => by
    simp only [foldr_cons, ha.assoc]
    rw [foldr_assoc]

theorem foldl_hom (f : α₁ → α₂) (g₁ : α₁ → β → α₁) (g₂ : α₂ → β → α₂) (l : List β) (init : α₁)
    (H : ∀ x y, g₂ (f x) y = f (g₁ x y)) : l.foldl g₂ (f init) = f (l.foldl g₁ init) := by
  induction l generalizing init <;> simp [*, H]

theorem foldr_hom (f : β₁ → β₂) (g₁ : α → β₁ → β₁) (g₂ : α → β₂ → β₂) (l : List α) (init : β₁)
    (H : ∀ x y, g₂ x (f y) = f (g₁ x y)) : l.foldr g₂ (f init) = f (l.foldr g₁ init) := by
  induction l <;> simp [*, H]

/--
Prove a proposition about the result of `List.foldl`,
by proving it for the initial data,
and the implication that the operation applied to any element of the list preserves the property.

The motive can take values in `Sort _`, so this may be used to construct data,
as well as to prove propositions.
-/
def foldlRecOn {motive : β → Sort _} : ∀ (l : List α) (op : β → α → β) (b : β) (_ : motive b)
    (_ : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ l), motive (op b a)), motive (List.foldl op b l)
  | [], _, _, hb, _ => hb
  | hd :: tl, op, b, hb, hl =>
    foldlRecOn tl op (op b hd) (hl b hb hd (mem_cons_self hd tl))
      fun y hy x hx => hl y hy x (mem_cons_of_mem hd hx)

@[simp] theorem foldlRecOn_nil {motive : β → Sort _} (hb : motive b)
    (hl : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ []), motive (op b a)) :
    foldlRecOn [] op b hb hl = hb := rfl

@[simp] theorem foldlRecOn_cons {motive : β → Sort _} (hb : motive b)
    (hl : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ x :: l), motive (op b a)) :
    foldlRecOn (x :: l) op b hb hl =
      foldlRecOn l op (op b x) (hl b hb x (mem_cons_self x l))
        (fun b c a m => hl b c a (mem_cons_of_mem x m)) :=
  rfl

/--
Prove a proposition about the result of `List.foldr`,
by proving it for the initial data,
and the implication that the operation applied to any element of the list preserves the property.

The motive can take values in `Sort _`, so this may be used to construct data,
as well as to prove propositions.
-/
def foldrRecOn {motive : β → Sort _} : ∀ (l : List α) (op : α → β → β) (b : β) (_ : motive b)
    (_ : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ l), motive (op a b)), motive (List.foldr op b l)
  | nil, _, _, hb, _ => hb
  | x :: l, op, b, hb, hl =>
    hl (foldr op b l)
      (foldrRecOn l op b hb fun b c a m => hl b c a (mem_cons_of_mem x m)) x (mem_cons_self x l)

@[simp] theorem foldrRecOn_nil {motive : β → Sort _} (hb : motive b)
    (hl : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ []), motive (op a b)) :
    foldrRecOn [] op b hb hl = hb := rfl

@[simp] theorem foldrRecOn_cons {motive : β → Sort _} (hb : motive b)
    (hl : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ x :: l), motive (op a b)) :
    foldrRecOn (x :: l) op b hb hl =
      hl _ (foldrRecOn l op b hb fun b c a m => hl b c a (mem_cons_of_mem x m))
        x (mem_cons_self x l) :=
  rfl

/--
We can prove that two folds over the same list are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the list,
preserves the relation.
-/
theorem foldl_rel {l : List α} {f g : β → α → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ l → ∀ (c c' : β), r c c' → r (f c a) (g c' a)) :
    r (l.foldl (fun acc a => f acc a) a) (l.foldl (fun acc a => g acc a) b) := by
  induction l generalizing a b with
  | nil => simp_all
  | cons a l ih =>
    simp only [foldl_cons]
    apply ih
    · simp_all
    · exact fun a m c c' h => h' _ (by simp_all) _ _ h

/--
We can prove that two folds over the same list are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the list,
preserves the relation.
-/
theorem foldr_rel {l : List α} {f g : α → β → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ l → ∀ (c c' : β), r c c' → r (f a c) (g a c')) :
    r (l.foldr (fun a acc => f a acc) a) (l.foldr (fun a acc => g a acc) b) := by
  induction l generalizing a b with
  | nil => simp_all
  | cons a l ih =>
    simp only [foldr_cons]
    apply h'
    · simp
    · exact ih h fun a m c c' h => h' _ (by simp_all) _ _ h

@[simp] theorem foldl_add_const (l : List α) (a b : Nat) :
    l.foldl (fun x _ => x + a) b = b + a * l.length := by
  induction l generalizing b with
  | nil => simp
  | cons y l ih =>
    simp only [foldl_cons, ih, length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      Nat.add_comm a]

@[simp] theorem foldr_add_const (l : List α) (a b : Nat) :
    l.foldr (fun _ x => x + a) b = b + a * l.length := by
  induction l generalizing b with
  | nil => simp
  | cons y l ih =>
    simp only [foldr_cons, ih, length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc]

/-! ### getLast -/

theorem getLast_eq_getElem : ∀ (l : List α) (h : l ≠ []),
    getLast l h = l[l.length - 1]'(by
      match l with
      | [] => contradiction
      | a :: l => exact Nat.le_refl _)
  | [_], _ => rfl
  | _ :: _ :: _, _ => by
    simp [getLast, get, Nat.succ_sub_succ, getLast_eq_getElem]

@[deprecated getLast_eq_getElem (since := "2024-07-15")]
theorem getLast_eq_get (l : List α) (h : l ≠ []) :
    getLast l h = l.get ⟨l.length - 1, by
      match l with
      | [] => contradiction
      | a :: l => exact Nat.le_refl _⟩ := by
  simp [getLast_eq_getElem]

theorem getLast_cons {a : α} {l : List α} : ∀ (h : l ≠ nil),
    getLast (a :: l) (cons_ne_nil a l) = getLast l h := by
  induction l <;> intros; {contradiction}; rfl

theorem getLast_eq_getLastD (a l h) : @getLast α (a::l) h = getLastD l a := by
  cases l <;> rfl

@[simp] theorem getLastD_eq_getLast? (a l) : @getLastD α l a = (getLast? l).getD a := by
  cases l <;> rfl

@[simp] theorem getLast_singleton (a h) : @getLast α [a] h = a := rfl

theorem getLast!_cons_eq_getLastD [Inhabited α] : @getLast! α _ (a::l) = getLastD l a := by
  simp [getLast!, getLast_eq_getLastD]

@[simp] theorem getLast_mem : ∀ {l : List α} (h : l ≠ []), getLast l h ∈ l
  | [], h => absurd rfl h
  | [_], _ => .head ..
  | _::a::l, _ => .tail _ <| getLast_mem (cons_ne_nil a l)

theorem getLast_mem_getLast? : ∀ {l : List α} (h : l ≠ []), getLast l h ∈ getLast? l
  | [], h => by contradiction
  | _ :: _, _ => rfl

theorem getLastD_mem_cons : ∀ (l : List α) (a : α), getLastD l a ∈ a::l
  | [], _ => .head ..
  | _::_, _ => .tail _ <| getLast_mem _

theorem getElem_cons_length (x : α) (xs : List α) (n : Nat) (h : n = xs.length) :
    (x :: xs)[n]'(by simp [h]) = (x :: xs).getLast (cons_ne_nil x xs) := by
  rw [getLast_eq_getElem]; cases h; rfl

@[deprecated getElem_cons_length (since := "2024-06-12")]
theorem get_cons_length (x : α) (xs : List α) (n : Nat) (h : n = xs.length) :
    (x :: xs).get ⟨n, by simp [h]⟩ = (x :: xs).getLast (cons_ne_nil x xs) := by
  simp [getElem_cons_length, h]

/-! ### getLast? -/

@[simp] theorem getLast?_singleton (a : α) : getLast? [a] = a := rfl

theorem getLast?_eq_getLast : ∀ l h, @getLast? α l = some (getLast l h)
  | [], h => nomatch h rfl
  | _ :: _, _ => rfl

theorem getLast?_eq_getElem? : ∀ (l : List α), getLast? l = l[l.length - 1]?
  | [] => rfl
  | a::l => by
    rw [getLast?_eq_getLast (a::l) nofun, getLast_eq_getElem, getElem?_eq_getElem]

theorem getLast_eq_iff_getLast?_eq_some {xs : List α} (h) :
    xs.getLast h = a ↔ xs.getLast? = some a := by
  rw [getLast?_eq_getLast _ h]
  simp

-- `getLast?_eq_none_iff`, `getLast?_eq_some_iff`, `getLast?_isSome`, and `getLast_mem`
-- are proved later once more `reverse` theorems are available.

theorem getLast?_cons {a : α} : (a::l).getLast? = l.getLast?.getD a := by
  cases l <;> simp [getLast?, getLast]

@[simp] theorem getLast?_cons_cons : (a :: b :: l).getLast? = (b :: l).getLast? := by
  simp [getLast?_cons]

@[deprecated getLast?_eq_getElem? (since := "2024-07-07")]
theorem getLast?_eq_get? (l : List α) : getLast? l = l.get? (l.length - 1) := by
  simp [getLast?_eq_getElem?]

theorem getLast?_concat (l : List α) : getLast? (l ++ [a]) = some a := by
  simp [getLast?_eq_getElem?, Nat.succ_sub_succ]

theorem getLastD_concat (a b l) : @getLastD α (l ++ [b]) a = b := by
  rw [getLastD_eq_getLast?, getLast?_concat]; rfl

/-! ### getLast! -/

theorem getLast!_nil [Inhabited α] : ([] : List α).getLast! = default := rfl

@[simp] theorem getLast!_eq_getLast?_getD [Inhabited α] {l : List α} : getLast! l = (getLast? l).getD default := by
  cases l with
  | nil => simp [getLast!_nil]
  | cons _ _ => simp [getLast!, getLast?_eq_getLast]

theorem getLast!_of_getLast? [Inhabited α] : ∀ {l : List α}, getLast? l = some a → getLast! l = a
  | _ :: _, rfl => rfl

theorem getLast!_eq_getElem! [Inhabited α] {l : List α} : l.getLast! = l[l.length - 1]! := by
  cases l with
  | nil => simp
  | cons _ _ =>
    apply getLast!_of_getLast?
    rw [getElem!_pos, getElem_cons_length (h := by simp)]
    rfl

/-! ## Head and tail -/

/-! ### head -/

theorem head?_singleton (a : α) : head? [a] = some a := by simp

set_option linter.unusedVariables false in -- See https://github.com/leanprover/lean4/issues/5259
theorem head!_of_head? [Inhabited α] : ∀ {l : List α}, head? l = some a → head! l = a
  | _ :: _, rfl => rfl

theorem head?_eq_head : ∀ {l} h, @head? α l = some (head l h)
  | _ :: _, _ => rfl

theorem head?_eq_getElem? : ∀ l : List α, head? l = l[0]?
  | [] => rfl
  | a :: l => by simp

theorem head_eq_getElem (l : List α) (h : l ≠ []) : head l h = l[0]'(length_pos.mpr h) := by
  cases l with
  | nil => simp at h
  | cons _ _ => simp

theorem head_eq_iff_head?_eq_some {xs : List α} (h) : xs.head h = a ↔ xs.head? = some a := by
  cases xs with
  | nil => simp at h
  | cons x xs => simp

@[simp] theorem head?_eq_none_iff : l.head? = none ↔ l = [] := by
  cases l <;> simp

theorem head?_eq_some_iff {xs : List α} {a : α} : xs.head? = some a ↔ ∃ ys, xs = a :: ys := by
  cases xs <;> simp_all

@[simp] theorem head?_isSome : l.head?.isSome ↔ l ≠ [] := by
  cases l <;> simp

@[simp] theorem head_mem : ∀ {l : List α} (h : l ≠ []), head l h ∈ l
  | [], h => absurd rfl h
  | _::_, _ => .head ..

theorem mem_of_mem_head? : ∀ {l : List α} {a : α}, a ∈ l.head? → a ∈ l := by
  intro l a h
  cases l with
  | nil => simp at h
  | cons b l =>
    simp at h
    cases h
    exact mem_cons_self a l

theorem head_mem_head? : ∀ {l : List α} (h : l ≠ []), head l h ∈ head? l
  | [], h => by contradiction
  | _ :: _, _ => rfl

theorem head?_concat {a : α} : (l ++ [a]).head? = l.head?.getD a := by
  cases l <;> simp

theorem head?_concat_concat : (l ++ [a, b]).head? = (l ++ [a]).head? := by
  cases l <;> simp

/-! ### headD -/

/-- `simp` unfolds `headD` in terms of `head?` and `Option.getD`. -/
@[simp] theorem headD_eq_head?_getD {l : List α} : headD l a = (head? l).getD a := by
  cases l <;> simp [headD]

/-! ### tailD -/

/-- `simp` unfolds `tailD` in terms of `tail?` and `Option.getD`. -/
@[simp] theorem tailD_eq_tail? (l l' : List α) : tailD l l' = (tail? l).getD l' := by
  cases l <;> rfl

/-! ### tail -/

@[simp] theorem length_tail (l : List α) : length (tail l) = length l - 1 := by cases l <;> rfl

theorem tail_eq_tailD (l) : @tail α l = tailD l [] := by cases l <;> rfl

theorem tail_eq_tail? (l) : @tail α l = (tail? l).getD [] := by simp [tail_eq_tailD]

theorem mem_of_mem_tail {a : α} {l : List α} (h : a ∈ tail l) : a ∈ l := by
  induction l <;> simp_all

theorem ne_nil_of_tail_ne_nil {l : List α} : l.tail ≠ [] → l ≠ [] := by
  cases l <;> simp

@[simp] theorem getElem_tail (l : List α) (i : Nat) (h : i < l.tail.length) :
    (tail l)[i] = l[i + 1]'(add_lt_of_lt_sub (by simpa using h)) := by
  cases l with
  | nil => simp at h
  | cons _ l => simp

@[simp] theorem getElem?_tail (l : List α) (i : Nat) :
    (tail l)[i]? = l[i + 1]? := by
  cases l <;> simp

@[simp] theorem set_tail (l : List α) (i : Nat) (a : α) :
    l.tail.set i a = (l.set (i + 1) a).tail := by
  cases l <;> simp

theorem one_lt_length_of_tail_ne_nil {l : List α} (h : l.tail ≠ []) : 1 < l.length := by
  cases l with
  | nil => simp at h
  | cons _ l =>
    simp only [tail_cons, ne_eq] at h
    exact Nat.lt_add_of_pos_left (length_pos.mpr h)

@[simp] theorem head_tail (l : List α) (h : l.tail ≠ []) :
    (tail l).head h = l[1]'(one_lt_length_of_tail_ne_nil h) := by
  cases l with
  | nil => simp at h
  | cons _ l => simp [head_eq_getElem]

@[simp] theorem head?_tail (l : List α) : (tail l).head? = l[1]? := by
  simp [head?_eq_getElem?]

@[simp] theorem getLast_tail (l : List α) (h : l.tail ≠ []) :
    (tail l).getLast h = l.getLast (ne_nil_of_tail_ne_nil h) := by
  simp only [getLast_eq_getElem, length_tail, getElem_tail]
  congr
  match l with
  | _ :: _ :: l => simp

theorem getLast?_tail (l : List α) : (tail l).getLast? = if l.length = 1 then none else l.getLast? := by
  match l with
  | [] => simp
  | [a] => simp
  | _ :: _ :: l =>
    simp only [tail_cons, length_cons, getLast?_cons_cons]
    rw [if_neg]
    rintro ⟨⟩

/-! ## Basic operations -/

/-! ### map -/

@[simp] theorem map_id_fun : map (id : α → α) = id := by
  funext l
  induction l <;> simp_all

/-- `map_id_fun'` differs from `map_id_fun` by representing the identity function as a lambda, rather than `id`. -/
@[simp] theorem map_id_fun' : map (fun (a : α) => a) = id := map_id_fun

-- This is not a `@[simp]` lemma because `map_id_fun` will apply.
theorem map_id (l : List α) : map (id : α → α) l = l := by
  induction l <;> simp_all

/-- `map_id'` differs from `map_id` by representing the identity function as a lambda, rather than `id`. -/
-- This is not a `@[simp]` lemma because `map_id_fun'` will apply.
theorem map_id' (l : List α) : map (fun (a : α) => a) l = l := map_id l

/-- Variant of `map_id`, with a side condition that the function is pointwise the identity. -/
theorem map_id'' {f : α → α} (h : ∀ x, f x = x) (l : List α) : map f l = l := by
  simp [show f = id from funext h]

theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] := rfl

@[simp] theorem length_map (as : List α) (f : α → β) : (as.map f).length = as.length := by
  induction as with
  | nil => simp [List.map]
  | cons _ as ih => simp [List.map, ih]

@[simp] theorem getElem?_map (f : α → β) : ∀ (l : List α) (n : Nat), (map f l)[n]? = Option.map f l[n]?
  | [], _ => rfl
  | _ :: _, 0 => by simp
  | _ :: l, n+1 => by simp [getElem?_map f l n]

@[deprecated getElem?_map (since := "2024-06-12")]
theorem get?_map (f : α → β) : ∀ l n, (map f l).get? n = (l.get? n).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n+1 => get?_map f l n

@[simp] theorem getElem_map (f : α → β) {l} {n : Nat} {h : n < (map f l).length} :
    (map f l)[n] = f (l[n]'(length_map l f ▸ h)) :=
  Option.some.inj <| by rw [← getElem?_eq_getElem, getElem?_map, getElem?_eq_getElem]; rfl

@[deprecated getElem_map (since := "2024-06-12")]
theorem get_map (f : α → β) {l n} :
    get (map f l) n = f (get l ⟨n, length_map l f ▸ n.2⟩) := by
  simp

@[simp] theorem mem_map {f : α → β} : ∀ {l : List α}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b
  | [] => by simp
  | _ :: l => by simp [mem_map (l := l), eq_comm (a := b)]

theorem exists_of_mem_map (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b := mem_map.1 h

theorem mem_map_of_mem (f : α → β) (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

theorem forall_mem_map {f : α → β} {l : List α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ l.map f), P i) ↔ ∀ (j) (_ : j ∈ l), P (f j) := by
  simp

@[deprecated forall_mem_map (since := "2024-07-25")] abbrev forall_mem_map_iff := @forall_mem_map

@[simp] theorem map_inj_left {f g : α → β} : map f l = map g l ↔ ∀ a ∈ l, f a = g a := by
  induction l <;> simp_all

theorem map_congr_left (h : ∀ a ∈ l, f a = g a) : map f l = map g l :=
  map_inj_left.2 h

theorem map_inj : map f = map g ↔ f = g := by
  constructor
  · intro h; ext a; replace h := congrFun h [a]; simpa using h
  · intro h; subst h; rfl

@[simp] theorem map_eq_nil_iff {f : α → β} {l : List α} : map f l = [] ↔ l = [] := by
  constructor <;> exact fun _ => match l with | [] => rfl

@[deprecated map_eq_nil_iff (since := "2024-09-05")] abbrev map_eq_nil := @map_eq_nil_iff

theorem eq_nil_of_map_eq_nil {f : α → β} {l : List α} (h : map f l = []) : l = [] :=
  map_eq_nil_iff.mp h

theorem map_eq_cons_iff {f : α → β} {l : List α} :
    map f l = b :: l₂ ↔ ∃ a l₁, l = a :: l₁ ∧ f a = b ∧ map f l₁ = l₂ := by
  cases l
  case nil => simp
  case cons a l₁ =>
    simp only [map_cons, cons.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨a, l₁, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · rintro ⟨a, l₁, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
      constructor <;> rfl

@[deprecated map_eq_cons_iff (since := "2024-09-05")] abbrev map_eq_cons := @map_eq_cons_iff

theorem map_eq_cons_iff' {f : α → β} {l : List α} :
    map f l = b :: l₂ ↔ l.head?.map f = some b ∧ l.tail?.map (map f) = some l₂ := by
  induction l <;> simp_all

@[deprecated map_eq_cons' (since := "2024-09-05")] abbrev map_eq_cons' := @map_eq_cons_iff'

theorem map_eq_map_iff : map f l = map g l ↔ ∀ a ∈ l, f a = g a := by
  induction l <;> simp

theorem map_eq_iff : map f l = l' ↔ ∀ i : Nat, l'[i]? = l[i]?.map f := by
  constructor
  · rintro rfl i
    simp
  · intro h
    ext1 i
    simp_all

theorem map_eq_foldr (f : α → β) (l : List α) : map f l = foldr (fun a bs => f a :: bs) [] l := by
  induction l <;> simp [*]

@[simp] theorem map_set {f : α → β} {l : List α} {i : Nat} {a : α} :
    (l.set i a).map f = (l.map f).set i (f a) := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih => cases i <;> simp_all

@[deprecated "Use the reverse direction of `map_set`." (since := "2024-09-20")]
theorem set_map {f : α → β} {l : List α} {n : Nat} {a : α} :
    (map f l).set n (f a) = map f (l.set n a) := by
  simp

@[simp] theorem head_map (f : α → β) (l : List α) (w) :
    (map f l).head w = f (l.head (by simpa using w)) := by
  cases l
  · simp at w
  · simp_all

@[simp] theorem head?_map (f : α → β) (l : List α) : (map f l).head? = l.head?.map f := by
  cases l <;> rfl

@[simp] theorem map_tail? (f : α → β) (l : List α) : (tail? l).map (map f) = tail? (map f l) := by
  cases l <;> rfl

@[simp] theorem map_tail (f : α → β) (l : List α) :
    map f l.tail = (map f l).tail := by
  cases l <;> simp_all

theorem headD_map (f : α → β) (l : List α) (a : α) : headD (map f l) (f a) = f (headD l a) := by
  cases l <;> rfl

theorem tailD_map (f : α → β) (l : List α) (l' : List α) :
    tailD (map f l) (map f l') = map f (tailD l l') := by simp [← map_tail?]

@[simp] theorem getLast_map (f : α → β) (l : List α) (h) :
    getLast (map f l) h = f (getLast l (by simpa using h)) := by
  cases l
  · simp at h
  · simp only [← getElem_cons_length _ _ _ rfl]
    simp only [map_cons]
    simp only [← getElem_cons_length _ _ _ rfl]
    simp only [← map_cons, getElem_map]
    simp

@[simp] theorem getLast?_map (f : α → β) (l : List α) : getLast? (map f l) = (getLast? l).map f := by
  cases l
  · simp
  · rw [getLast?_eq_getLast, getLast?_eq_getLast, getLast_map] <;> simp

theorem getLastD_map (f : α → β) (l : List α) (a : α) : getLastD (map f l) (f a) = f (getLastD l a) := by
  simp

@[simp] theorem map_map (g : β → γ) (f : α → β) (l : List α) :
  map g (map f l) = map (g ∘ f) l := by induction l <;> simp_all

/-! ### filter -/

@[simp] theorem filter_cons_of_pos {p : α → Bool} {a : α} {l} (pa : p a) :
    filter p (a :: l) = a :: filter p l := by rw [filter, pa]

@[simp] theorem filter_cons_of_neg {p : α → Bool} {a : α} {l} (pa : ¬ p a) :
    filter p (a :: l) = filter p l := by rw [filter, eq_false_of_ne_true pa]

theorem filter_cons :
    (x :: xs : List α).filter p = if p x then x :: (xs.filter p) else xs.filter p := by
  split <;> simp [*]

theorem length_filter_le (p : α → Bool) (l : List α) :
    (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [filter_cons, length_cons, succ_eq_add_one]
    split
    · simp only [length_cons, succ_eq_add_one]
      exact Nat.succ_le_succ ih
    · exact Nat.le_trans ih (Nat.le_add_right _ _)

@[simp]
theorem filter_eq_self {l} : filter p l = l ↔ ∀ a ∈ l, p a := by
  induction l with simp
  | cons a l ih =>
    cases h : p a <;> simp [*]
    intro h; exact Nat.lt_irrefl _ (h ▸ length_filter_le p l)

@[simp]
theorem filter_length_eq_length {l} : (filter p l).length = l.length ↔ ∀ a ∈ l, p a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [filter_cons, length_cons, succ_eq_add_one, mem_cons, forall_eq_or_imp]
    split <;> rename_i h
    · simp_all [Nat.add_one_inj] -- Why does the simproc not fire here?
    · have := Nat.ne_of_lt (Nat.lt_succ.mpr (length_filter_le p l))
      simp_all

@[simp] theorem mem_filter : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  induction as with
  | nil => simp [filter]
  | cons a as ih =>
    by_cases h : p a
    · simp_all [or_and_left]
    · simp_all [or_and_right]

@[simp] theorem filter_eq_nil_iff {l} : filter p l = [] ↔ ∀ a, a ∈ l → ¬p a := by
  simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

@[deprecated filter_eq_nil_iff (since := "2024-09-05")] abbrev filter_eq_nil := @filter_eq_nil_iff

theorem forall_mem_filter {l : List α} {p : α → Bool} {P : α → Prop} :
    (∀ (i) (_ : i ∈ l.filter p), P i) ↔ ∀ (j) (_ : j ∈ l), p j → P j := by
  simp

@[deprecated forall_mem_filter (since := "2024-07-25")] abbrev forall_mem_filter_iff := @forall_mem_filter

@[simp] theorem filter_filter (q) : ∀ l, filter p (filter q l) = filter (fun a => p a && q a) l
  | [] => rfl
  | a :: l => by by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq, filter_filter _ l]

theorem foldl_filter (p : α → Bool) (f : β → α → β) (l : List α) (init : β) :
    (l.filter p).foldl f init = l.foldl (fun x y => if p y then f x y else x) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filter_cons, foldl_cons]
    split <;> simp [ih]

theorem foldr_filter (p : α → Bool) (f : α → β → β) (l : List α) (init : β) :
    (l.filter p).foldr f init = l.foldr (fun x y => if p x then f x y else y) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filter_cons, foldr_cons]
    split <;> simp [ih]

theorem filter_map (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  induction l with
  | nil => rfl
  | cons a l IH => by_cases h : p (f a) <;> simp [*]

@[deprecated filter_map (since := "2024-06-15")] abbrev map_filter := @filter_map

theorem map_filter_eq_foldr (f : α → β) (p : α → Bool) (as : List α) :
    map f (filter p as) = foldr (fun a bs => bif p a then f a :: bs else bs) [] as := by
  induction as with
  | nil => rfl
  | cons head _ ih =>
    simp only [foldr]
    cases hp : p head <;> simp [filter, *]

@[simp] theorem filter_append {p : α → Bool} :
    ∀ (l₁ l₂ : List α), filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂
  | [], _ => rfl
  | a :: l₁, l₂ => by simp [filter]; split <;> simp [filter_append l₁]

theorem filter_eq_cons_iff {l} {a} {as} :
    filter p l = a :: as ↔
      ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ (∀ x, x ∈ l₁ → ¬p x) ∧ p a ∧ filter p l₂ = as := by
  constructor
  · induction l with
    | nil => simp
    | cons x l ih =>
      intro h
      simp only [filter_cons] at h
      split at h <;> rename_i w
      · simp only [cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], l, ?_⟩
        simp [w]
      · specialize ih h
        obtain ⟨l₁, l₂, rfl, w₁, w₂, w₃⟩ := ih
        refine ⟨x :: l₁, l₂, ?_⟩
        simp_all
  · rintro ⟨l₁, l₂, rfl, h₁, h, h₂⟩
    simp [h₂, filter_cons, filter_eq_nil_iff.mpr h₁, h]

@[deprecated filter_eq_cons_iff (since := "2024-09-05")] abbrev filter_eq_cons := @filter_eq_cons_iff

theorem filter_congr {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → filter p l = filter q l
  | [], _ => rfl
  | a :: l, h => by
    rw [forall_mem_cons] at h; by_cases pa : p a
    · simp [pa, h.1 ▸ pa, filter_congr h.2]
    · simp [pa, h.1 ▸ pa, filter_congr h.2]

@[deprecated filter_congr (since := "2024-06-20")] abbrev filter_congr' := @filter_congr

theorem head_filter_of_pos {p : α → Bool} {l : List α} (w : l ≠ []) (h : p (l.head w)) :
    (filter p l).head ((ne_nil_of_mem (mem_filter.2 ⟨head_mem w, h⟩))) = l.head w := by
  cases l with
  | nil => simp
  | cons =>
    simp only [head_cons] at h
    simp [filter_cons, h]

@[simp] theorem filter_sublist {p : α → Bool} : ∀ (l : List α), filter p l <+ l
  | [] => .slnil
  | a :: l => by rw [filter]; split <;> simp [Sublist.cons, Sublist.cons₂, filter_sublist l]

/-! ### filterMap -/

@[simp] theorem filterMap_cons_none {f : α → Option β} {a : α} {l : List α} (h : f a = none) :
    filterMap f (a :: l) = filterMap f l := by simp only [filterMap, h]

@[simp] theorem filterMap_cons_some {f : α → Option β} {a : α} {l : List α} {b : β} (h : f a = some b) :
    filterMap f (a :: l) = b :: filterMap f l := by simp only [filterMap, h]

@[simp]
theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f := by
  funext l; induction l <;> simp [*, filterMap_cons]

@[simp] theorem filterMap_some_fun : filterMap (some : α → Option α) = id := by
  funext l
  erw [filterMap_eq_map]
  simp

theorem filterMap_some (l : List α) : filterMap some l = l := by
  rw [filterMap_some_fun, id]

theorem map_filterMap_some_eq_filter_map_isSome (f : α → Option β) (l : List α) :
    (l.filterMap f).map some = (l.map f).filter fun b => b.isSome := by
  induction l <;> simp [filterMap_cons]; split <;> simp [*]

theorem length_filterMap_le (f : α → Option β) (l : List α) :
    (filterMap f l).length ≤ l.length := by
  rw [← length_map _ some, map_filterMap_some_eq_filter_map_isSome, ← length_map _ f]
  apply length_filter_le

@[simp]
theorem filterMap_length_eq_length {l} :
    (filterMap f l).length = l.length ↔ ∀ a ∈ l, (f a).isSome := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [filterMap_cons, length_cons, succ_eq_add_one, mem_cons, forall_eq_or_imp]
    split <;> rename_i h
    · have := Nat.ne_of_lt (Nat.lt_succ.mpr (length_filterMap_le f l))
      simp_all
    · simp_all [Nat.add_one_inj] -- Why does the simproc not fire here?

@[simp]
theorem filterMap_eq_filter (p : α → Bool) :
    filterMap (Option.guard (p ·)) = filter p := by
  funext l
  induction l with
  | nil => rfl
  | cons a l IH => by_cases pa : p a <;> simp [filterMap_cons, Option.guard, pa, ← IH]

theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (l : List α) :
    filterMap g (filterMap f l) = filterMap (fun x => (f x).bind g) l := by
  induction l with
  | nil => rfl
  | cons a l IH => cases h : f a <;> simp [filterMap_cons, *]

theorem map_filterMap (f : α → Option β) (g : β → γ) (l : List α) :
    map g (filterMap f l) = filterMap (fun x => (f x).map g) l := by
  simp only [← filterMap_eq_map, filterMap_filterMap, Option.map_eq_bind]

@[simp]
theorem filterMap_map (f : α → β) (g : β → Option γ) (l : List α) :
    filterMap g (map f l) = filterMap (g ∘ f) l := by
  rw [← filterMap_eq_map, filterMap_filterMap]; rfl

theorem filter_filterMap (f : α → Option β) (p : β → Bool) (l : List α) :
    filter p (filterMap f l) = filterMap (fun x => (f x).filter p) l := by
  rw [← filterMap_eq_filter, filterMap_filterMap]
  congr; funext x; cases f x <;> simp [Option.filter, Option.guard]

theorem filterMap_filter (p : α → Bool) (f : α → Option β) (l : List α) :
    filterMap f (filter p l) = filterMap (fun x => if p x then f x else none) l := by
  rw [← filterMap_eq_filter, filterMap_filterMap]
  congr; funext x; by_cases h : p x <;> simp [Option.guard, h]

@[simp] theorem mem_filterMap {f : α → Option β} {l : List α} {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b := by
  induction l <;> simp [filterMap_cons]; split <;> simp [*, eq_comm]

theorem forall_mem_filterMap {f : α → Option β} {l : List α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ filterMap f l), P i) ↔ ∀ (j) (_ : j ∈ l) (b), f j = some b → P b := by
  simp only [mem_filterMap, forall_exists_index, and_imp]
  rw [forall_comm]
  apply forall_congr'
  intro a
  rw [forall_comm]

@[deprecated forall_mem_filterMap (since := "2024-07-25")] abbrev forall_mem_filterMap_iff := @forall_mem_filterMap

@[simp] theorem filterMap_append {α β : Type _} (l l' : List α) (f : α → Option β) :
    filterMap f (l ++ l') = filterMap f l ++ filterMap f l' := by
  induction l <;> simp [filterMap_cons]; split <;> simp [*]

theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (l : List α) : map g (filterMap f l) = l := by simp only [map_filterMap, H, filterMap_some, id]

theorem head_filterMap_of_eq_some {f : α → Option β} {l : List α} (w : l ≠ []) {b : β} (h : f (l.head w) = some b) :
    (filterMap f l).head ((ne_nil_of_mem (mem_filterMap.2 ⟨_, head_mem w, h⟩))) =
      b := by
  cases l with
  | nil => simp at w
  | cons a l =>
    simp only [head_cons] at h
    simp [filterMap_cons, h]

theorem forall_none_of_filterMap_eq_nil (h : filterMap f xs = []) : ∀ x ∈ xs, f x = none := by
  intro x hx
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    simp only [filterMap_cons] at h
    split at h
    · cases hx with
      | head => assumption
      | tail _ hmem => exact ih h hmem
    · contradiction

@[simp] theorem filterMap_eq_nil_iff {l} : filterMap f l = [] ↔ ∀ a ∈ l, f a = none := by
  constructor
  · exact forall_none_of_filterMap_eq_nil
  · intro h
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [filterMap_cons]
      split
      · apply ih
        simp_all
      · simp_all

@[deprecated filterMap_eq_nil_iff (since := "2024-09-05")] abbrev filterMap_eq_nil := @filterMap_eq_nil_iff

theorem filterMap_eq_cons_iff {l} {b} {bs} :
    filterMap f l = b :: bs ↔
      ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ (∀ x, x ∈ l₁ → f x = none) ∧ f a = some b ∧
        filterMap f l₂ = bs := by
  constructor
  · induction l with
    | nil => simp
    | cons a l ih =>
      cases h : f a with
      | none =>
        simp only [filterMap_cons_none h]
        intro w
        specialize ih w
        obtain ⟨l₁, a', l₂, rfl, w₁, w₂, w₃⟩ := ih
        exact ⟨a :: l₁, a', l₂, by simp_all⟩
      | some b =>
        simp only [filterMap_cons_some h, cons.injEq, and_imp]
        rintro rfl rfl
        refine ⟨[], a, l, by simp [h]⟩
  · rintro ⟨l₁, a, l₂, rfl, h₁, h₂, h₃⟩
    simp_all [filterMap_eq_nil_iff.mpr h₁, filterMap_cons_some h₂]

@[deprecated filterMap_eq_cons_iff (since := "2024-09-05")] abbrev filterMap_eq_cons := @filterMap_eq_cons_iff

/-! ### append -/

@[simp] theorem nil_append_fun : (([] : List α) ++ ·) = id := rfl

@[simp] theorem cons_append_fun (a : α) (as : List α) :
    (fun bs => ((a :: as) ++ bs)) = fun bs => a :: (as ++ bs) := rfl

theorem getElem_append {l₁ l₂ : List α} (n : Nat) (h) :
    (l₁ ++ l₂)[n] = if h' : n < l₁.length then l₁[n] else l₂[n - l₁.length]'(by simp at h h'; exact Nat.sub_lt_left_of_lt_add h' h) := by
  split <;> rename_i h'
  · rw [getElem_append_left h']
  · rw [getElem_append_right (by simpa using h')]

theorem getElem?_append_left {l₁ l₂ : List α} {n : Nat} (hn : n < l₁.length) :
    (l₁ ++ l₂)[n]? = l₁[n]? := by
  have hn' : n < (l₁ ++ l₂).length := Nat.lt_of_lt_of_le hn <|
    length_append .. ▸ Nat.le_add_right ..
  simp_all [getElem?_eq_getElem, getElem_append]

theorem getElem?_append_right : ∀ {l₁ l₂ : List α} {n : Nat}, l₁.length ≤ n →
  (l₁ ++ l₂)[n]? = l₂[n - l₁.length]?
| [], _, _, _ => rfl
| a :: l, _, n+1, h₁ => by
  rw [cons_append]
  simp [Nat.succ_sub_succ_eq_sub, getElem?_append_right (Nat.lt_succ.1 h₁)]

theorem getElem?_append {l₁ l₂ : List α} {n : Nat} :
    (l₁ ++ l₂)[n]? = if n < l₁.length then l₁[n]? else l₂[n - l₁.length]? := by
  split <;> rename_i h
  · exact getElem?_append_left h
  · exact getElem?_append_right (by simpa using h)

@[deprecated getElem?_append_right (since := "2024-06-12")]
theorem get?_append_right {l₁ l₂ : List α} {n : Nat} (h : l₁.length ≤ n) :
    (l₁ ++ l₂).get? n = l₂.get? (n - l₁.length) := by
  simp [getElem?_append_right, h]

/-- Variant of `getElem_append_left` useful for rewriting from the small list to the big list. -/
theorem getElem_append_left' (l₂ : List α) {l₁ : List α} {n : Nat} (hn : n < l₁.length) :
    l₁[n] = (l₁ ++ l₂)[n]'(by simpa using Nat.lt_add_right l₂.length hn) := by
  rw [getElem_append_left] <;> simp

/-- Variant of `getElem_append_right` useful for rewriting from the small list to the big list. -/
theorem getElem_append_right' (l₁ : List α) {l₂ : List α} {n : Nat} (hn : n < l₂.length) :
    l₂[n] = (l₁ ++ l₂)[n + l₁.length]'(by simpa [Nat.add_comm] using Nat.add_lt_add_left hn _) := by
  rw [getElem_append_right] <;> simp [*, le_add_left]

@[deprecated (since := "2024-06-12")]
theorem get_append_right_aux {l₁ l₂ : List α} {n : Nat}
  (h₁ : l₁.length ≤ n) (h₂ : n < (l₁ ++ l₂).length) : n - l₁.length < l₂.length := by
  rw [length_append] at h₂
  exact Nat.sub_lt_left_of_lt_add h₁ h₂

set_option linter.deprecated false in
@[deprecated getElem_append_right (since := "2024-06-12")]
theorem get_append_right' {l₁ l₂ : List α} {n : Nat} (h₁ : l₁.length ≤ n) (h₂) :
    (l₁ ++ l₂).get ⟨n, h₂⟩ = l₂.get ⟨n - l₁.length, get_append_right_aux h₁ h₂⟩ :=
  Option.some.inj <| by rw [← get?_eq_get, ← get?_eq_get, get?_append_right h₁]

theorem getElem_of_append {l : List α} (eq : l = l₁ ++ a :: l₂) (h : l₁.length = n) :
    l[n]'(eq ▸ h ▸ by simp_arith) = a := Option.some.inj <| by
  rw [← getElem?_eq_getElem, eq, getElem?_append_right (h ▸ Nat.le_refl _), h]
  simp

@[deprecated (since := "2024-06-12")]
theorem get_of_append_proof {l : List α}
    (eq : l = l₁ ++ a :: l₂) (h : l₁.length = n) : n < length l := eq ▸ h ▸ by simp_arith

set_option linter.deprecated false in
@[deprecated getElem_of_append (since := "2024-06-12")]
theorem get_of_append {l : List α} (eq : l = l₁ ++ a :: l₂) (h : l₁.length = n) :
    l.get ⟨n, get_of_append_proof eq h⟩ = a := Option.some.inj <| by
  rw [← get?_eq_get, eq, get?_append_right (h ▸ Nat.le_refl _), h, Nat.sub_self]; rfl

/--
See also `eq_append_cons_of_mem`, which proves a stronger version
in which the initial list must not contain the element.
-/
theorem append_of_mem {a : α} {l : List α} : a ∈ l → ∃ s t : List α, l = s ++ a :: t
  | .head l => ⟨[], l, rfl⟩
  | .tail b h => let ⟨s, t, h'⟩ := append_of_mem h; ⟨b::s, t, by rw [h', cons_append]⟩

@[simp 1100] theorem singleton_append : [x] ++ l = x :: l := rfl

theorem append_inj :
    ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
  | [], [], _, _, h, _ => ⟨rfl, h⟩
  | _ :: _, _ :: _, _, _, h, hl => by
    simp [append_inj (cons.inj h).2 (Nat.succ.inj hl)] at h ⊢; exact h

theorem append_inj_right (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : t₁ = t₂ :=
  (append_inj h hl).right

theorem append_inj_left (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : s₁ = s₂ :=
  (append_inj h hl).left

/-- Variant of `append_inj` instead requiring equality of the lengths of the second lists. -/
theorem append_inj' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h <| @Nat.add_right_cancel _ (length t₁) _ <| by
  let hap := congrArg length h; simp only [length_append, ← hl] at hap; exact hap

/-- Variant of `append_inj_right` instead requiring equality of the lengths of the second lists. -/
theorem append_inj_right' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : t₁ = t₂ :=
  (append_inj' h hl).right

/-- Variant of `append_inj_left` instead requiring equality of the lengths of the second lists. -/
theorem append_inj_left' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ :=
  (append_inj' h hl).left

theorem append_right_inj {t₁ t₂ : List α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  ⟨fun h => append_inj_right h rfl, congrArg _⟩

theorem append_left_inj {s₁ s₂ : List α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  ⟨fun h => append_inj_left' h rfl, congrArg (· ++ _)⟩

@[simp] theorem append_left_eq_self {x y : List α} : x ++ y = y ↔ x = [] := by
  rw [← append_left_inj (s₁ := x), nil_append]

@[simp] theorem self_eq_append_left {x y : List α} : y = x ++ y ↔ x = [] := by
  rw [eq_comm, append_left_eq_self]

@[simp] theorem append_right_eq_self {x y : List α} : x ++ y = x ↔ y = [] := by
  rw [← append_right_inj (t₁ := y), append_nil]

@[simp] theorem self_eq_append_right {x y : List α} : x = x ++ y ↔ y = [] := by
  rw [eq_comm, append_right_eq_self]

@[simp] theorem append_eq_nil : p ++ q = [] ↔ p = [] ∧ q = [] := by
  cases p <;> simp

theorem getLast_concat {a : α} : ∀ (l : List α), getLast (l ++ [a]) (by simp) = a
  | [] => rfl
  | a::t => by
    simp [getLast_cons _, getLast_concat t]

@[deprecated getElem_append (since := "2024-06-12")]
theorem get_append {l₁ l₂ : List α} (n : Nat) (h : n < l₁.length) :
    (l₁ ++ l₂).get ⟨n, length_append .. ▸ Nat.lt_add_right _ h⟩ = l₁.get ⟨n, h⟩ := by
  simp [getElem_append, h]

@[deprecated getElem_append_left (since := "2024-06-12")]
theorem get_append_left (as bs : List α) (h : i < as.length) {h'} :
    (as ++ bs).get ⟨i, h'⟩ = as.get ⟨i, h⟩ := by
  simp [getElem_append_left, h, h']

@[deprecated getElem_append_right (since := "2024-06-12")]
theorem get_append_right (as bs : List α) (h : as.length ≤ i) {h' h''} :
    (as ++ bs).get ⟨i, h'⟩ = bs.get ⟨i - as.length, h''⟩ := by
  simp [getElem_append_right, h, h', h'']

@[deprecated getElem?_append_left (since := "2024-06-12")]
theorem get?_append {l₁ l₂ : List α} {n : Nat} (hn : n < l₁.length) :
    (l₁ ++ l₂).get? n = l₁.get? n := by
  simp [getElem?_append_left hn]

@[simp] theorem head_append_of_ne_nil {l : List α} {w₁} (w₂) :
    head (l ++ l') w₁ = head l w₂ := by
  match l, w₂ with
  | a :: l, _ => rfl

theorem head_append {l₁ l₂ : List α} (w : l₁ ++ l₂ ≠ []) :
    head (l₁ ++ l₂) w =
      if h : l₁.isEmpty then
        head l₂ (by simp_all [isEmpty_iff])
      else
        head l₁ (by simp_all [isEmpty_iff]) := by
  split <;> rename_i h
  · simp [isEmpty_iff] at h
    subst h
    simp
  · simp [isEmpty_iff] at h
    simp [h]

theorem head_append_left {l₁ l₂ : List α} (h : l₁ ≠ []) :
    head (l₁ ++ l₂) (fun h => by simp_all) = head l₁ h := by
  rw [head_append, dif_neg (by simp_all)]

theorem head_append_right {l₁ l₂ : List α} (w : l₁ ++ l₂ ≠ []) (h : l₁ = []) :
    head (l₁ ++ l₂) w = head l₂ (by simp_all) := by
  rw [head_append, dif_pos (by simp_all)]

@[simp] theorem head?_append {l : List α} : (l ++ l').head? = l.head?.or l'.head? := by
  cases l <;> rfl

-- Note:
-- `getLast_append_of_ne_nil`, `getLast_append` and `getLast?_append`
-- are stated and proved later in the `reverse` section.

theorem tail?_append {l l' : List α} : (l ++ l').tail? = (l.tail?.map (· ++ l')).or l'.tail? := by
  cases l <;> simp

theorem tail?_append_of_ne_nil {l l' : List α} (_ : l ≠ []) : (l ++ l').tail? = some (l.tail ++ l') :=
  match l with
  | _ :: _ => by simp

theorem tail_append {l l' : List α} : (l ++ l').tail = if l.isEmpty then l'.tail else l.tail ++ l' := by
  cases l <;> simp

@[simp] theorem tail_append_of_ne_nil {xs ys : List α} (h : xs ≠ []) :
    (xs ++ ys).tail = xs.tail ++ ys := by
  simp_all [tail_append]

@[deprecated tail_append_of_ne_nil (since := "2024-07-24")] abbrev tail_append_left := @tail_append_of_ne_nil

theorem nil_eq_append_iff : [] = a ++ b ↔ a = [] ∧ b = [] := by
  rw [eq_comm, append_eq_nil]

@[deprecated nil_eq_append_iff (since := "2024-07-24")] abbrev nil_eq_append := @nil_eq_append_iff

theorem append_ne_nil_of_left_ne_nil {s : List α} (h : s ≠ []) (t : List α) : s ++ t ≠ [] := by simp_all
theorem append_ne_nil_of_right_ne_nil (s : List α) : t ≠ [] → s ++ t ≠ [] := by simp_all

@[deprecated append_ne_nil_of_left_ne_nil (since := "2024-07-24")]
theorem append_ne_nil_of_ne_nil_left {s : List α} (h : s ≠ []) (t : List α) : s ++ t ≠ [] := by simp_all
@[deprecated append_ne_nil_of_right_ne_nil (since := "2024-07-24")]
theorem append_ne_nil_of_ne_nil_right (s : List α) : t ≠ [] → s ++ t ≠ [] := by simp_all

theorem append_eq_cons_iff :
    a ++ b = x :: c ↔ (a = [] ∧ b = x :: c) ∨ (∃ a', a = x :: a' ∧ c = a' ++ b) := by
  cases a with simp | cons a as => ?_
  exact ⟨fun h => ⟨as, by simp [h]⟩, fun ⟨a', ⟨aeq, aseq⟩, h⟩ => ⟨aeq, by rw [aseq, h]⟩⟩

@[deprecated append_eq_cons_iff (since := "2024-07-24")] abbrev append_eq_cons := @append_eq_cons_iff

theorem cons_eq_append_iff :
    x :: c = a ++ b ↔ (a = [] ∧ b = x :: c) ∨ (∃ a', a = x :: a' ∧ c = a' ++ b) := by
  rw [eq_comm, append_eq_cons_iff]

@[deprecated cons_eq_append_iff (since := "2024-07-24")] abbrev cons_eq_append := @cons_eq_append_iff

theorem append_eq_append_iff {a b c d : List α} :
    a ++ b = c ++ d ↔ (∃ a', c = a ++ a' ∧ b = a' ++ d) ∨ ∃ c', a = c ++ c' ∧ d = c' ++ b := by
  induction a generalizing c with
  | nil => simp_all
  | cons a as ih => cases c <;> simp [eq_comm, and_assoc, ih, and_or_left]

@[deprecated append_inj (since := "2024-07-24")] abbrev append_inj_of_length_left := @append_inj
@[deprecated append_inj' (since := "2024-07-24")] abbrev append_inj_of_length_right := @append_inj'

@[simp] theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp_all [or_assoc]

theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
  mt mem_append.1 $ not_or.mpr ⟨h₁, h₂⟩

theorem mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_append

theorem mem_append_left {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inr h)

theorem mem_iff_append {a : α} {l : List α} : a ∈ l ↔ ∃ s t : List α, l = s ++ a :: t :=
  ⟨append_of_mem, fun ⟨s, t, e⟩ => e ▸ by simp⟩

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
    (∀ (x) (_ : x ∈ l₁ ++ l₂), p x) ↔ (∀ (x) (_ : x ∈ l₁), p x) ∧ (∀ (x) (_ : x ∈ l₂), p x) := by
  simp only [mem_append, or_imp, forall_and]

theorem set_append {s t : List α} :
    (s ++ t).set i x = if i < s.length then s.set i x ++ t else s ++ t.set (i - s.length) x := by
  induction s generalizing i with
  | nil => simp
  | cons a as ih => cases i with
    | zero => simp
    | succ i =>
      simp [Nat.add_one_lt_add_one_iff, ih]
      split
      · rfl
      · congr 3; rw [Nat.add_sub_add_right]

@[simp] theorem set_append_left {s t : List α} (i : Nat) (x : α) (h : i < s.length) :
    (s ++ t).set i x = s.set i x ++ t := by
  simp [set_append, h]

@[simp] theorem set_append_right {s t : List α} (i : Nat) (x : α) (h : s.length ≤ i) :
    (s ++ t).set i x = s ++ t.set (i - s.length) x := by
  rw [set_append, if_neg (by simp_all)]

@[simp] theorem foldrM_append [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (l l' : List α) :
    (l ++ l').foldrM f b = l'.foldrM f b >>= l.foldrM f := by
  induction l <;> simp [*]

@[simp] theorem foldl_append {β : Type _} (f : β → α → β) (b) (l l' : List α) :
    (l ++ l').foldl f b = l'.foldl f (l.foldl f b) := by simp [foldl_eq_foldlM]

@[simp] theorem foldr_append (f : α → β → β) (b) (l l' : List α) :
    (l ++ l').foldr f b = l.foldr f (l'.foldr f b) := by simp [foldr_eq_foldrM]

theorem filterMap_eq_append_iff {f : α → Option β} :
    filterMap f l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filterMap f l₁ = L₁ ∧ filterMap f l₂ = L₂ := by
  constructor
  · induction l generalizing L₁ with
    | nil =>
      simp only [filterMap_nil, nil_eq_append_iff, and_imp]
      rintro rfl rfl
      exact ⟨[], [], by simp⟩
    | cons x l ih =>
      simp only [filterMap_cons]
      split
      · intro h
        obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ := ih h
        refine ⟨x :: l₁, l₂, ?_⟩
        simp_all
      · rename_i b w
        intro h
        rcases cons_eq_append_iff.mp h with (⟨rfl, rfl⟩ | ⟨L₁, ⟨rfl, h⟩⟩)
        · refine ⟨[], x :: l, ?_⟩
          simp [filterMap_cons, w]
        · obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ := ih ‹_›
          refine ⟨x :: l₁, l₂, ?_⟩
          simp [filterMap_cons, w]
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    simp

@[deprecated filterMap_eq_append_iff (since := "2024-09-05")] abbrev filterMap_eq_append := @filterMap_eq_append_iff

theorem append_eq_filterMap_iff {f : α → Option β} :
    L₁ ++ L₂ = filterMap f l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filterMap f l₁ = L₁ ∧ filterMap f l₂ = L₂ := by
  rw [eq_comm, filterMap_eq_append_iff]

@[deprecated append_eq_filterMap (since := "2024-09-05")] abbrev append_eq_filterMap := @append_eq_filterMap_iff

theorem filter_eq_append_iff {p : α → Bool} :
    filter p l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filter p l₁ = L₁ ∧ filter p l₂ = L₂ := by
  rw [← filterMap_eq_filter, filterMap_eq_append_iff]

theorem append_eq_filter_iff {p : α → Bool} :
    L₁ ++ L₂ = filter p l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filter p l₁ = L₁ ∧ filter p l₂ = L₂ := by
  rw [eq_comm, filter_eq_append_iff]

@[deprecated append_eq_filter_iff (since := "2024-09-05")] abbrev append_eq_filter := @append_eq_filter_iff

@[simp] theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁; induction l₁ <;> intros <;> simp_all

theorem map_eq_append_iff {f : α → β} :
    map f l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = L₁ ∧ map f l₂ = L₂ := by
  rw [← filterMap_eq_map, filterMap_eq_append_iff]

theorem append_eq_map_iff {f : α → β} :
    L₁ ++ L₂ = map f l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = L₁ ∧ map f l₂ = L₂ := by
  rw [eq_comm, map_eq_append_iff]

@[deprecated map_eq_append_iff (since := "2024-09-05")] abbrev map_eq_append := @map_eq_append_iff
@[deprecated append_eq_map_iff (since := "2024-09-05")] abbrev append_eq_map := @append_eq_map_iff

/-! ### concat

Note that `concat_eq_append` is a `@[simp]` lemma, so `concat` should usually not appear in goals.
As such there's no need for a thorough set of lemmas describing `concat`.
-/

-- As `List.concat` is defined in `Init.Prelude`, we write the basic simplification lemmas here.
theorem concat_nil (a : α) : concat [] a = [a] :=
  rfl
theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b :=
  rfl

theorem init_eq_of_concat_eq {a b : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ b → l₁ = l₂ := by
  simp only [concat_eq_append]
  intro h
  apply append_inj_left' h (by simp)

theorem last_eq_of_concat_eq {a b : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ b → a = b := by
  simp only [concat_eq_append]
  intro h
  simpa using append_inj_right' h (by simp)

theorem concat_inj {a b : α} {l l' : List α} : concat l a = concat l' b ↔ l = l' ∧ a = b :=
  ⟨fun h => ⟨init_eq_of_concat_eq h, last_eq_of_concat_eq h⟩, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem concat_inj_left {l l' : List α} (a : α) : concat l a = concat l' a ↔ l = l' :=
  ⟨init_eq_of_concat_eq, by simp⟩

theorem concat_inj_right {l : List α} {a a' : α} : concat l a = concat l a' ↔ a = a' :=
  ⟨last_eq_of_concat_eq, by simp⟩

@[deprecated concat_inj (since := "2024-09-05")] abbrev concat_eq_concat := @concat_inj

theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] := by cases l <;> simp

theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by simp

theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by simp

theorem map_concat (f : α → β) (a : α) (l : List α) : map f (concat l a) = concat (map f l) (f a) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem eq_nil_or_concat : ∀ l : List α, l = [] ∨ ∃ L b, l = concat L b
  | [] => .inl rfl
  | a::l => match l, eq_nil_or_concat l with
    | _, .inl rfl => .inr ⟨[], a, rfl⟩
    | _, .inr ⟨L, b, rfl⟩ => .inr ⟨a::L, b, rfl⟩

/-! ### flatten -/

@[simp] theorem length_flatten (L : List (List α)) : (flatten L).length = (L.map length).sum := by
  induction L with
  | nil => rfl
  | cons =>
    simp [flatten, length_append, *]

theorem flatten_singleton (l : List α) : [l].flatten = l := by simp

@[simp] theorem mem_flatten : ∀ {L : List (List α)}, a ∈ L.flatten ↔ ∃ l, l ∈ L ∧ a ∈ l
  | [] => by simp
  | b :: l => by simp [mem_flatten, or_and_right, exists_or]

@[simp] theorem flatten_eq_nil_iff {L : List (List α)} : L.flatten = [] ↔ ∀ l ∈ L, l = [] := by
  induction L <;> simp_all

theorem flatten_ne_nil_iff {xs : List (List α)} : xs.flatten ≠ [] ↔ ∃ x, x ∈ xs ∧ x ≠ [] := by
  simp

theorem exists_of_mem_flatten : a ∈ flatten L → ∃ l, l ∈ L ∧ a ∈ l := mem_flatten.1

theorem mem_flatten_of_mem (lL : l ∈ L) (al : a ∈ l) : a ∈ flatten L := mem_flatten.2 ⟨l, lL, al⟩

theorem forall_mem_flatten {p : α → Prop} {L : List (List α)} :
    (∀ (x) (_ : x ∈ flatten L), p x) ↔ ∀ (l) (_ : l ∈ L) (x) (_ : x ∈ l), p x := by
  simp only [mem_flatten, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

theorem flatten_eq_flatMap {L : List (List α)} : flatten L = L.flatMap id := by
  induction L <;> simp [List.flatMap]

theorem head?_flatten {L : List (List α)} : (flatten L).head? = L.findSome? fun l => l.head? := by
  induction L with
  | nil => rfl
  | cons =>
    simp only [findSome?_cons]
    split <;> simp_all

-- `getLast?_flatten` is proved later, after the `reverse` section.
-- `head_flatten` and `getLast_flatten` are proved in `Init.Data.List.Find`.

theorem foldl_flatten (f : β → α → β) (b : β) (L : List (List α)) :
    (flatten L).foldl f b = L.foldl (fun b l => l.foldl f b) b := by
  induction L generalizing b <;> simp_all

theorem foldr_flatten (f : α → β → β) (b : β) (L : List (List α)) :
    (flatten L).foldr f b = L.foldr (fun l b => l.foldr f b) b := by
  induction L <;> simp_all

@[simp] theorem map_flatten (f : α → β) (L : List (List α)) : map f (flatten L) = flatten (map (map f) L) := by
  induction L <;> simp_all

@[simp] theorem filterMap_flatten (f : α → Option β) (L : List (List α)) :
    filterMap f (flatten L) = flatten (map (filterMap f) L) := by
  induction L <;> simp [*, filterMap_append]

@[simp] theorem filter_flatten (p : α → Bool) (L : List (List α)) :
    filter p (flatten L) = flatten (map (filter p) L) := by
  induction L <;> simp [*, filter_append]

theorem flatten_filter_not_isEmpty  :
    ∀ {L : List (List α)}, flatten (L.filter fun l => !l.isEmpty) = L.flatten
  | [] => rfl
  | [] :: L
  | (a :: l) :: L => by
      simp [flatten_filter_not_isEmpty (L := L)]

theorem flatten_filter_ne_nil [DecidablePred fun l : List α => l ≠ []] {L : List (List α)} :
    flatten (L.filter fun l => l ≠ []) = L.flatten := by
  simp only [ne_eq, ← isEmpty_iff, Bool.not_eq_true, Bool.decide_eq_false,
    flatten_filter_not_isEmpty]

@[simp] theorem flatten_append (L₁ L₂ : List (List α)) : flatten (L₁ ++ L₂) = flatten L₁ ++ flatten L₂ := by
  induction L₁ <;> simp_all

theorem flatten_concat (L : List (List α)) (l : List α) : flatten (L ++ [l]) = flatten L ++ l := by
  simp

theorem flatten_flatten {L : List (List (List α))} : flatten (flatten L) = flatten (map flatten L) := by
  induction L <;> simp_all

theorem flatten_eq_cons_iff {xs : List (List α)} {y : α} {ys : List α} :
    xs.flatten = y :: ys ↔
      ∃ as bs cs, xs = as ++ (y :: bs) :: cs ∧ (∀ l, l ∈ as → l = []) ∧ ys = bs ++ cs.flatten := by
  constructor
  · induction xs with
    | nil => simp
    | cons x xs ih =>
      intro h
      simp only [flatten_cons] at h
      replace h := h.symm
      rw [cons_eq_append_iff] at h
      obtain (⟨rfl, h⟩ | ⟨z⟩) := h
      · obtain ⟨as, bs, cs, rfl, _, rfl⟩ := ih h
        refine ⟨[] :: as, bs, cs, ?_⟩
        simpa
      · obtain ⟨a', rfl, rfl⟩ := z
        refine ⟨[], a', xs, ?_⟩
        simp
  · rintro ⟨as, bs, cs, rfl, h₁, rfl⟩
    simp [flatten_eq_nil_iff.mpr h₁]

theorem flatten_eq_append_iff {xs : List (List α)} {ys zs : List α} :
    xs.flatten = ys ++ zs ↔
      (∃ as bs, xs = as ++ bs ∧ ys = as.flatten ∧ zs = bs.flatten) ∨
        ∃ as bs c cs ds, xs = as ++ (bs ++ c :: cs) :: ds ∧ ys = as.flatten ++ bs ∧
          zs = c :: cs ++ ds.flatten := by
  constructor
  · induction xs generalizing ys with
    | nil =>
      simp only [flatten_nil, nil_eq, append_eq_nil, and_false, cons_append, false_and, exists_const,
        exists_false, or_false, and_imp, List.cons_ne_nil]
      rintro rfl rfl
      exact ⟨[], [], by simp⟩
    | cons x xs ih =>
      intro h
      simp only [flatten_cons] at h
      rw [append_eq_append_iff] at h
      obtain (⟨ys, rfl, h⟩ | ⟨c', rfl, h⟩) := h
      · obtain (⟨as, bs, rfl, rfl, rfl⟩ | ⟨as, bs, c, cs, ds, rfl, rfl, rfl⟩) := ih h
        · exact .inl ⟨x :: as, bs, by simp⟩
        · exact .inr ⟨x :: as, bs, c, cs, ds, by simp⟩
      · simp only [h]
        cases c' with
        | nil => exact .inl ⟨[ys], xs, by simp⟩
        | cons x c' => exact .inr ⟨[], ys, x, c', xs, by simp⟩
  · rintro (⟨as, bs, rfl, rfl, rfl⟩ | ⟨as, bs, c, cs, ds, rfl, rfl, rfl⟩)
    · simp
    · simp

/-- Two lists of sublists are equal iff their flattens coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_flatten_eq : ∀ {L L' : List (List α)},
    L = L' ↔ L.flatten = L'.flatten ∧ map length L = map length L'
  | _, [] => by simp_all
  | [], x' :: L' => by simp_all
  | x :: L, x' :: L' => by
    simp
    rw [eq_iff_flatten_eq]
    constructor
    · rintro ⟨rfl, h₁, h₂⟩
      simp_all
    · rintro ⟨h₁, h₂, h₃⟩
      obtain ⟨rfl, h⟩ := append_inj h₁ h₂
      exact ⟨rfl, h, h₃⟩

/-! ### flatMap -/

theorem flatMap_def (l : List α) (f : α → List β) : l.flatMap f = flatten (map f l) := by rfl

@[simp] theorem flatMap_id (l : List (List α)) : List.flatMap l id = l.flatten := by simp [flatMap_def]

@[simp] theorem mem_flatMap {f : α → List β} {b} {l : List α} : b ∈ l.flatMap f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [flatMap_def, mem_flatten]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_flatMap {b : β} {l : List α} {f : α → List β} :
    b ∈ l.flatMap f → ∃ a, a ∈ l ∧ b ∈ f a := mem_flatMap.1

theorem mem_flatMap_of_mem {b : β} {l : List α} {f : α → List β} {a} (al : a ∈ l) (h : b ∈ f a) :
    b ∈ l.flatMap f := mem_flatMap.2 ⟨a, al, h⟩

@[simp]
theorem flatMap_eq_nil_iff {l : List α} {f : α → List β} : List.flatMap l f = [] ↔ ∀ x ∈ l, f x = [] :=
  flatten_eq_nil_iff.trans <| by
    simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

@[deprecated flatMap_eq_nil_iff (since := "2024-09-05")] abbrev bind_eq_nil := @flatMap_eq_nil_iff

theorem forall_mem_flatMap {p : β → Prop} {l : List α} {f : α → List β} :
    (∀ (x) (_ : x ∈ l.flatMap f), p x) ↔ ∀ (a) (_ : a ∈ l) (b) (_ : b ∈ f a), p b := by
  simp only [mem_flatMap, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

theorem flatMap_singleton (f : α → List β) (x : α) : [x].flatMap f = f x :=
  append_nil (f x)

@[simp] theorem flatMap_singleton' (l : List α) : (l.flatMap fun x => [x]) = l := by
  induction l <;> simp [*]

theorem head?_flatMap {l : List α} {f : α → List β} :
    (l.flatMap f).head? = l.findSome? fun a => (f a).head? := by
  induction l with
  | nil => rfl
  | cons =>
    simp only [findSome?_cons]
    split <;> simp_all

@[simp] theorem flatMap_append (xs ys : List α) (f : α → List β) :
    (xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap f := by
  induction xs; {rfl}; simp_all [flatMap_cons, append_assoc]

@[deprecated flatMap_append (since := "2024-07-24")] abbrev append_bind := @flatMap_append

theorem flatMap_assoc {α β} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.flatMap f).flatMap g = l.flatMap fun x => (f x).flatMap g := by
  induction l <;> simp [*]

theorem map_flatMap (f : β → γ) (g : α → List β) :
    ∀ l : List α, (l.flatMap g).map f = l.flatMap fun a => (g a).map f
  | [] => rfl
  | a::l => by simp only [flatMap_cons, map_append, map_flatMap _ _ l]

theorem flatMap_map (f : α → β) (g : β → List γ) (l : List α) :
    (map f l).flatMap g = l.flatMap (fun a => g (f a)) := by
  induction l <;> simp [flatMap_cons, *]

theorem map_eq_flatMap {α β} (f : α → β) (l : List α) : map f l = l.flatMap fun x => [f x] := by
  simp only [← map_singleton]
  rw [← flatMap_singleton' l, map_flatMap, flatMap_singleton']

theorem filterMap_flatMap {β γ} (l : List α) (g : α → List β) (f : β → Option γ) :
    (l.flatMap g).filterMap f = l.flatMap fun a => (g a).filterMap f := by
  induction l <;> simp [*]

theorem filter_flatMap (l : List α) (g : α → List β) (f : β → Bool) :
    (l.flatMap g).filter f = l.flatMap fun a => (g a).filter f := by
  induction l <;> simp [*]

theorem flatMap_eq_foldl (f : α → List β) (l : List α) :
    l.flatMap f = l.foldl (fun acc a => acc ++ f a) [] := by
  suffices ∀ l', l' ++ l.flatMap f = l.foldl (fun acc a => acc ++ f a) l' by simpa using this []
  intro l'
  induction l generalizing l'
  · simp
  · next ih => rw [flatMap_cons, ← append_assoc, ih, foldl_cons]

/-! ### replicate -/

@[simp] theorem replicate_one : replicate 1 a = [a] := rfl

@[simp] theorem mem_replicate {a b : α} : ∀ {n}, b ∈ replicate n a ↔ n ≠ 0 ∧ b = a
  | 0 => by simp
  | n+1 => by simp [replicate_succ, mem_replicate, Nat.succ_ne_zero]

@[simp, deprecated mem_replicate (since := "2024-09-05")]
theorem contains_replicate [BEq α] {n : Nat} {a b : α} :
    (replicate n b).contains a = (a == b && !n == 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, elem_cons]
    split <;> simp_all

@[simp, deprecated mem_replicate (since := "2024-09-05")]
theorem decide_mem_replicate [BEq α] [LawfulBEq α] {a b : α} :
    ∀ {n}, decide (b ∈ replicate n a) = ((¬ n == 0) && b == a)
  | 0 => by simp
  | n+1 => by simp [replicate_succ, decide_mem_replicate, Nat.succ_ne_zero]

theorem eq_of_mem_replicate {a b : α} {n} (h : b ∈ replicate n a) : b = a := (mem_replicate.1 h).2

theorem forall_mem_replicate {p : α → Prop} {a : α} {n} :
    (∀ b, b ∈ replicate n a → p b) ↔ n = 0 ∨ p a := by
  cases n <;> simp [mem_replicate]

@[simp] theorem replicate_succ_ne_nil (n : Nat) (a : α) : replicate (n+1) a ≠ [] := by
  simp [replicate_succ]

@[simp] theorem replicate_eq_nil_iff {n : Nat} (a : α) : replicate n a = [] ↔ n = 0 := by
  cases n <;> simp

@[deprecated replicate_eq_nil_iff (since := "2024-09-05")] abbrev replicate_eq_nil := @replicate_eq_nil_iff

@[simp] theorem getElem_replicate (a : α) {n : Nat} {m} (h : m < (replicate n a).length) :
    (replicate n a)[m] = a :=
  eq_of_mem_replicate (get_mem _ _ _)

@[deprecated getElem_replicate (since := "2024-06-12")]
theorem get_replicate (a : α) {n : Nat} (m : Fin _) : (replicate n a).get m = a := by
  simp

theorem getElem?_replicate : (replicate n a)[m]? = if m < n then some a else none := by
  by_cases h : m < n
  · rw [getElem?_eq_getElem (by simpa), getElem_replicate, if_pos h]
  · rw [getElem?_eq_none (by simpa using h), if_neg h]

@[simp] theorem getElem?_replicate_of_lt {n : Nat} {m : Nat} (h : m < n) : (replicate n a)[m]? = some a := by
  simp [getElem?_replicate, h]

theorem head?_replicate (a : α) (n : Nat) : (replicate n a).head? = if n = 0 then none else some a := by
  cases n <;> simp [replicate_succ]

@[simp] theorem head_replicate (w : replicate n a ≠ []) : (replicate n a).head w = a := by
  cases n
  · simp at w
  · simp_all [replicate_succ]

-- `getLast?_replicate` and `getLast_replicate` appear below,
-- after more `reverse` lemmas are available.

@[simp] theorem tail_replicate (n : Nat) (a : α) : (replicate n a).tail = replicate (n - 1) a := by
  cases n <;> simp [replicate_succ]

@[simp] theorem replicate_inj : replicate n a = replicate m b ↔ n = m ∧ (n = 0 ∨ a = b) :=
  ⟨fun h => have eq : n = m := by simpa using congrArg length h
    ⟨eq, by
    subst eq
    by_cases w : n = 0
    · simp_all
    · right
      have p := congrArg (·[0]?) h
      replace w : 0 < n := by exact zero_lt_of_ne_zero w
      simp only [getElem?_replicate, if_pos w] at p
      simp_all⟩,
    by rintro ⟨rfl, rfl | rfl⟩ <;> rfl⟩

theorem eq_replicate_of_mem {a : α} :
    ∀ {l : List α}, (∀ (b) (_ : b ∈ l), b = a) → l = replicate l.length a
  | [], _ => rfl
  | b :: l, H => by
    let ⟨rfl, H₂⟩ := forall_mem_cons (l := l).1 H
    rw [length_cons, replicate, ← eq_replicate_of_mem H₂]

theorem eq_replicate_iff {a : α} {n} {l : List α} :
    l = replicate n a ↔ length l = n ∧ ∀ (b) (_ : b ∈ l), b = a :=
  ⟨fun h => h ▸ ⟨length_replicate .., fun _ => eq_of_mem_replicate⟩,
   fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

@[deprecated eq_replicate_iff (since := "2024-09-05")] abbrev eq_replicate := @eq_replicate_iff

theorem map_eq_replicate_iff {l : List α} {f : α → β} {b : β} :
    l.map f = replicate l.length b ↔ ∀ x ∈ l, f x = b := by
  simp [eq_replicate_iff]

@[simp] theorem map_const (l : List α) (b : β) : map (Function.const α b) l = replicate l.length b :=
  map_eq_replicate_iff.mpr fun _ _ => rfl

@[simp] theorem map_const_fun (x : β) : map (Function.const α x) = (replicate ·.length x) := by
  funext l
  simp

/-- Variant of `map_const` using a lambda rather than `Function.const`. -/
-- This can not be a `@[simp]` lemma because it would fire on every `List.map`.
theorem map_const' (l : List α) (b : β) : map (fun _ => b) l = replicate l.length b :=
  map_const l b

@[simp] theorem set_replicate_self : (replicate n a).set i a = replicate n a := by
  apply ext_getElem
  · simp
  · intro i h₁ h₂
    simp [getElem_set]

@[simp] theorem append_replicate_replicate : replicate n a ++ replicate m a = replicate (n + m) a := by
  rw [eq_replicate_iff]
  constructor
  · simp
  · intro b
    simp only [mem_append, mem_replicate, ne_eq]
    rintro (⟨-, rfl⟩ | ⟨_, rfl⟩) <;> rfl

theorem append_eq_replicate_iff {l₁ l₂ : List α} {a : α} :
    l₁ ++ l₂ = replicate n a ↔
      l₁.length + l₂.length = n ∧ l₁ = replicate l₁.length a ∧ l₂ = replicate l₂.length a := by
  simp only [eq_replicate_iff, length_append, mem_append, true_and, and_congr_right_iff]
  exact fun _ =>
    { mp := fun h => ⟨fun b m => h b (Or.inl m), fun b m => h b (Or.inr m)⟩,
      mpr := fun h b x => Or.casesOn x (fun m => h.left b m) fun m => h.right b m }

@[deprecated append_eq_replicate_iff (since := "2024-09-05")] abbrev append_eq_replicate := @append_eq_replicate_iff

@[simp] theorem map_replicate : (replicate n a).map f = replicate n (f a) := by
  ext1 n
  simp only [getElem?_map, getElem?_replicate]
  split <;> simp

theorem filter_replicate : (replicate n a).filter p = if p a then replicate n a else [] := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [replicate_succ, filter_cons]
    split <;> simp_all

@[simp] theorem filter_replicate_of_pos (h : p a) : (replicate n a).filter p = replicate n a := by
  simp [filter_replicate, h]

@[simp] theorem filter_replicate_of_neg (h : ¬ p a) : (replicate n a).filter p = [] := by
  simp [filter_replicate, h]

theorem filterMap_replicate {f : α → Option β} :
    (replicate n a).filterMap f = match f a with | none => [] | .some b => replicate n b := by
  induction n with
  | zero => split <;> simp
  | succ n ih =>
    simp only [replicate_succ, filterMap_cons]
    split <;> simp_all

-- This is not a useful `simp` lemma because `b` is unknown.
theorem filterMap_replicate_of_some {f : α → Option β} (h : f a = some b) :
    (replicate n a).filterMap f = replicate n b := by
  simp [filterMap_replicate, h]

@[simp] theorem filterMap_replicate_of_isSome {f : α → Option β} (h : (f a).isSome) :
    (replicate n a).filterMap f = replicate n (Option.get _ h) := by
  rw [Option.isSome_iff_exists] at h
  obtain ⟨b, h⟩ := h
  simp [filterMap_replicate, h]

@[simp] theorem filterMap_replicate_of_none {f : α → Option β} (h : f a = none) :
    (replicate n a).filterMap f = [] := by
  simp [filterMap_replicate, h]

@[simp] theorem flatten_replicate_nil : (replicate n ([] : List α)).flatten = [] := by
  induction n <;> simp_all [replicate_succ]

@[simp] theorem flatten_replicate_singleton : (replicate n [a]).flatten = replicate n a := by
  induction n <;> simp_all [replicate_succ]

@[simp] theorem flatten_replicate_replicate : (replicate n (replicate m a)).flatten = replicate (n * m) a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, flatten_cons, ih, append_replicate_replicate, replicate_inj, or_true,
      and_true, add_one_mul, Nat.add_comm]

theorem flatMap_replicate {β} (f : α → List β) : (replicate n a).flatMap f = (replicate n (f a)).flatten := by
  induction n with
  | zero => simp
  | succ n ih => simp only [replicate_succ, flatMap_cons, ih, flatten_cons]

@[simp] theorem isEmpty_replicate : (replicate n a).isEmpty = decide (n = 0) := by
  cases n <;> simp [replicate_succ]

/-- Every list is either empty, a non-empty `replicate`, or begins with a non-empty `replicate`
followed by a different element. -/
theorem eq_replicate_or_eq_replicate_append_cons {α : Type _} (l : List α) :
    (l = []) ∨ (∃ n a, l = replicate n a ∧ 0 < n) ∨
      (∃ n a b l', l = replicate n a ++ b :: l' ∧ 0 < n ∧ a ≠ b) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    right
    rcases ih with rfl | ⟨n, a, rfl, h⟩ | ⟨n, a, b, l', rfl, h⟩
    · left
      exact ⟨1, x, rfl, by decide⟩
    · by_cases h' : x = a
      · subst h'
        left
        exact ⟨n + 1, x, rfl, by simp⟩
      · right
        refine ⟨1, x, a, replicate (n - 1) a, ?_, by decide, h'⟩
        match n with | n + 1 => simp [replicate_succ]
    · right
      by_cases h' : x = a
      · subst h'
        refine ⟨n + 1, x, b, l', by simp [replicate_succ], by simp, h.2⟩
      · refine ⟨1, x, a, replicate (n - 1) a ++ b :: l', ?_, by decide, h'⟩
        match n with | n + 1 => simp [replicate_succ]

/-- An induction principle for lists based on contiguous runs of identical elements. -/
-- A `Sort _` valued version would require a different design. (And associated `@[simp]` lemmas.)
theorem replicateRecOn {α : Type _} {p : List α → Prop} (m : List α)
    (h0 : p []) (hr : ∀ a n, 0 < n → p (replicate n a))
    (hi : ∀ a b n l, a ≠ b → 0 < n → p (b :: l) → p (replicate n a ++ b :: l)) : p m := by
  rcases eq_replicate_or_eq_replicate_append_cons m with
    rfl | ⟨n, a, rfl, hn⟩ | ⟨n, a, b, l', w, hn, h⟩
  · exact h0
  · exact hr _ _ hn
  · have : (b :: l').length < m.length := by
      simpa [w] using Nat.lt_add_of_pos_left hn
    subst w
    exact hi _ _ _ _ h hn (replicateRecOn (b :: l') h0 hr hi)
termination_by m.length

/-! ### reverse -/

@[simp] theorem length_reverse (as : List α) : (as.reverse).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem mem_reverseAux {x : α} : ∀ {as bs}, x ∈ reverseAux as bs ↔ x ∈ as ∨ x ∈ bs
  | [], _ => ⟨.inr, fun | .inr h => h⟩
  | a :: _, _ => by rw [reverseAux, mem_cons, or_assoc, or_left_comm, mem_reverseAux, mem_cons]

@[simp] theorem mem_reverse {x : α} {as : List α} : x ∈ reverse as ↔ x ∈ as := by
  simp [reverse, mem_reverseAux]

@[simp] theorem reverse_eq_nil_iff {xs : List α} : xs.reverse = [] ↔ xs = [] := by
  match xs with
  | [] => simp
  | x :: xs => simp

theorem reverse_ne_nil_iff {xs : List α} : xs.reverse ≠ [] ↔ xs ≠ [] :=
  not_congr reverse_eq_nil_iff

/-- Variant of `getElem?_reverse` with a hypothesis giving the linear relation between the indices. -/
theorem getElem?_reverse' : ∀ {l : List α} (i j), i + j + 1 = length l →
    l.reverse[i]? = l[j]?
  | [], _, _, _ => rfl
  | a::l, i, 0, h => by simp [Nat.succ.injEq] at h; simp [h, getElem?_append_right, Nat.succ.injEq]
  | a::l, i, j+1, h => by
    have := Nat.succ.inj h; simp at this ⊢
    rw [getElem?_append_left, getElem?_reverse' _ _ this]
    rw [length_reverse, ← this]; apply Nat.lt_add_of_pos_right (Nat.succ_pos _)

@[deprecated getElem?_reverse' (since := "2024-06-12")]
theorem get?_reverse' {l : List α} (i j) (h : i + j + 1 = length l) : get? l.reverse i = get? l j := by
  simp [getElem?_reverse' _ _ h]

@[simp]
theorem getElem?_reverse {l : List α} {i} (h : i < length l) :
    l.reverse[i]? = l[l.length - 1 - i]? :=
  getElem?_reverse' _ _ <| by
    rw [Nat.add_sub_of_le (Nat.le_sub_one_of_lt h),
      Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) h)]

@[simp]
theorem getElem_reverse {l : List α} {i} (h : i < l.reverse.length) :
    l.reverse[i] = l[l.length - 1 - i]'(Nat.sub_one_sub_lt_of_lt (by simpa using h)) := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, ← getElem?_eq_getElem]
  rw [getElem?_reverse (by simpa using h)]

@[deprecated getElem?_reverse (since := "2024-06-12")]
theorem get?_reverse {l : List α} {i} (h : i < length l) :
    get? l.reverse i = get? l (l.length - 1 - i) := by
  simp [getElem?_reverse h]

theorem reverseAux_reverseAux_nil (as bs : List α) : reverseAux (reverseAux as bs) [] = reverseAux bs as := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => simp [reverseAux, ih]

@[simp] theorem reverse_reverse (as : List α) : as.reverse.reverse = as := by
  simp only [reverse]; rw [reverseAux_reverseAux_nil]; rfl

theorem reverse_eq_iff {as bs : List α} : as.reverse = bs ↔ as = bs.reverse := by
  constructor <;> (rintro rfl; simp)

@[simp] theorem reverse_inj {xs ys : List α} : xs.reverse = ys.reverse ↔ xs = ys := by
  simp [reverse_eq_iff]

@[simp] theorem reverse_eq_cons_iff {xs : List α} {a : α} {ys : List α} :
    xs.reverse = a :: ys ↔ xs = ys.reverse ++ [a] := by
  rw [reverse_eq_iff, reverse_cons]

@[deprecated reverse_eq_cons_iff (since := "2024-09-05")] abbrev reverse_eq_cons := @reverse_eq_cons_iff

@[simp] theorem getLast?_reverse (l : List α) : l.reverse.getLast? = l.head? := by
  cases l <;> simp [getLast?_concat]

@[simp] theorem head?_reverse (l : List α) : l.reverse.head? = l.getLast? := by
  rw [← getLast?_reverse, reverse_reverse]

theorem getLast?_eq_head?_reverse {xs : List α} : xs.getLast? = xs.reverse.head? := by
  simp

theorem head?_eq_getLast?_reverse {xs : List α} : xs.head? = xs.reverse.getLast? := by
  simp

theorem mem_of_mem_getLast? {l : List α} {a : α} (h : a ∈ getLast? l) : a ∈ l := by
  rw [getLast?_eq_head?_reverse] at h
  rw [← mem_reverse]
  exact mem_of_mem_head? h

@[simp] theorem map_reverse (f : α → β) (l : List α) : l.reverse.map f = (l.map f).reverse := by
  induction l <;> simp [*]

@[deprecated map_reverse (since := "2024-06-20")]
theorem reverse_map (f : α → β) (l : List α) : (l.map f).reverse = l.reverse.map f := by
  simp

@[simp] theorem filter_reverse (p : α → Bool) (l : List α) : (l.reverse.filter p) = (l.filter p).reverse := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [reverse_cons, filter_append, filter_cons, ih]
    split <;> simp_all

@[simp] theorem filterMap_reverse (f : α → Option β) (l : List α) : (l.reverse.filterMap f) = (l.filterMap f).reverse := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [reverse_cons, filterMap_append, filterMap_cons, ih]
    split <;> simp_all

@[simp] theorem reverse_append (as bs : List α) : (as ++ bs).reverse = bs.reverse ++ as.reverse := by
  induction as <;> simp_all

@[simp] theorem reverse_eq_append_iff {xs ys zs : List α} :
    xs.reverse = ys ++ zs ↔ xs = zs.reverse ++ ys.reverse := by
  rw [reverse_eq_iff, reverse_append]

@[deprecated reverse_eq_append_iff (since := "2024-09-05")] abbrev reverse_eq_append := @reverse_eq_append_iff

theorem reverse_concat (l : List α) (a : α) : (l ++ [a]).reverse = a :: l.reverse := by
  rw [reverse_append]; rfl

theorem reverse_eq_concat {xs ys : List α} {a : α} :
    xs.reverse = ys ++ [a] ↔ xs = a :: ys.reverse := by
  rw [reverse_eq_iff, reverse_concat]

/-- Reversing a flatten is the same as reversing the order of parts and reversing all parts. -/
theorem reverse_flatten (L : List (List α)) :
    L.flatten.reverse = (L.map reverse).reverse.flatten := by
  induction L <;> simp_all

/-- Flattening a reverse is the same as reversing all parts and reversing the flattened result. -/
theorem flatten_reverse (L : List (List α)) :
    L.reverse.flatten = (L.map reverse).flatten.reverse := by
  induction L <;> simp_all

theorem reverse_flatMap {β} (l : List α) (f : α → List β) : (l.flatMap f).reverse = l.reverse.flatMap (reverse ∘ f) := by
  induction l <;> simp_all

theorem flatMap_reverse {β} (l : List α) (f : α → List β) : (l.reverse.flatMap f) = (l.flatMap (reverse ∘ f)).reverse := by
  induction l <;> simp_all

@[simp] theorem reverseAux_eq (as bs : List α) : reverseAux as bs = reverse as ++ bs :=
  reverseAux_eq_append ..

@[simp] theorem foldrM_reverse [Monad m] (l : List α) (f : α → β → m β) (b) :
    l.reverse.foldrM f b = l.foldlM (fun x y => f y x) b :=
  (foldlM_reverse ..).symm.trans <| by simp

@[simp] theorem foldl_reverse (l : List α) (f : β → α → β) (b) :
    l.reverse.foldl f b = l.foldr (fun x y => f y x) b := by simp [foldl_eq_foldlM, foldr_eq_foldrM]

@[simp] theorem foldr_reverse (l : List α) (f : α → β → β) (b) :
    l.reverse.foldr f b = l.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by simp

theorem foldl_eq_foldr_reverse (l : List α) (f : β → α → β) (b) :
    l.foldl f b = l.reverse.foldr (fun x y => f y x) b := by simp

theorem foldr_eq_foldl_reverse (l : List α) (f : α → β → β) (b) :
    l.foldr f b = l.reverse.foldl (fun x y => f y x) b := by simp

@[simp] theorem reverse_replicate (n) (a : α) : reverse (replicate n a) = replicate n a :=
  eq_replicate_iff.2
    ⟨by rw [length_reverse, length_replicate],
     fun _ h => eq_of_mem_replicate (mem_reverse.1 h)⟩

/-! #### Further results about `getLast` and `getLast?` -/

@[simp] theorem head_reverse {l : List α} (h : l.reverse ≠ []) :
    l.reverse.head h = getLast l (by simp_all) := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    simp only [reverse_cons]
    by_cases h' : l = []
    · simp_all
    · simp only [head_eq_iff_head?_eq_some, head?_reverse] at ih
      simp [ih, h, h', getLast_cons, head_eq_iff_head?_eq_some]

theorem getLast_eq_head_reverse {l : List α} (h : l ≠ []) :
    l.getLast h = l.reverse.head (by simp_all) := by
  rw [← head_reverse]

theorem getLast_eq_iff_getLast_eq_some {xs : List α} (h) : xs.getLast h = a ↔ xs.getLast? = some a := by
  rw [getLast_eq_head_reverse, head_eq_iff_head?_eq_some]
  simp

@[simp] theorem getLast?_eq_none_iff {xs : List α} : xs.getLast? = none ↔ xs = [] := by
  rw [getLast?_eq_head?_reverse, head?_eq_none_iff, reverse_eq_nil_iff]

theorem getLast?_eq_some_iff {xs : List α} {a : α} : xs.getLast? = some a ↔ ∃ ys, xs = ys ++ [a] := by
  rw [getLast?_eq_head?_reverse, head?_eq_some_iff]
  simp only [reverse_eq_cons_iff]
  exact ⟨fun ⟨ys, h⟩ => ⟨ys.reverse, by simpa using h⟩, fun ⟨ys, h⟩ => ⟨ys.reverse, by simpa using h⟩⟩

@[simp] theorem getLast?_isSome : l.getLast?.isSome ↔ l ≠ [] := by
  rw [getLast?_eq_head?_reverse, head?_isSome]
  simp

theorem mem_of_getLast?_eq_some {xs : List α} {a : α} (h : xs.getLast? = some a) : a ∈ xs := by
  obtain ⟨ys, rfl⟩ := getLast?_eq_some_iff.1 h
  exact mem_concat_self ys a

@[simp] theorem getLast_reverse {l : List α} (h : l.reverse ≠ []) :
    l.reverse.getLast h = l.head (by simp_all) := by
  simp [getLast_eq_head_reverse]

theorem head_eq_getLast_reverse {l : List α} (h : l ≠ []) :
    l.head h = l.reverse.getLast (by simp_all) := by
  rw [← getLast_reverse]

@[simp] theorem getLast_append_of_ne_nil {l : List α} {h₁} (h₂ : l' ≠ []) :
    (l ++ l').getLast h₁ = l'.getLast h₂ := by
  simp only [getLast_eq_head_reverse, reverse_append]
  rw [head_append_of_ne_nil]

theorem getLast_append {l : List α} (h : l ++ l' ≠ []) :
    (l ++ l').getLast h =
      if h' : l'.isEmpty then
        l.getLast (by simp_all [isEmpty_iff])
      else
        l'.getLast (by simp_all [isEmpty_iff]) := by
  split <;> rename_i h'
  · simp only [isEmpty_iff] at h'
    subst h'
    simp
  · simp [isEmpty_iff] at h'
    simp [h']

theorem getLast_append_right {l : List α} (h : l' ≠ []) :
    (l ++ l').getLast (fun h => by simp_all) = l'.getLast h := by
  rw [getLast_append, dif_neg (by simp_all)]

theorem getLast_append_left {l : List α} (w : l ++ l' ≠ []) (h : l' = []) :
    (l ++ l').getLast w = l.getLast (by simp_all) := by
  rw [getLast_append, dif_pos (by simp_all)]

@[simp] theorem getLast?_append {l l' : List α} : (l ++ l').getLast? = l'.getLast?.or l.getLast? := by
  simp [← head?_reverse]

theorem getLast_filter_of_pos {p : α → Bool} {l : List α} (w : l ≠ []) (h : p (getLast l w) = true) :
    getLast (filter p l) (ne_nil_of_mem (mem_filter.2 ⟨getLast_mem w, h⟩)) = getLast l w := by
  simp only [getLast_eq_head_reverse, ← filter_reverse]
  rw [head_filter_of_pos]
  simp_all

theorem getLast_filterMap_of_eq_some {f : α → Option β} {l : List α} {w : l ≠ []} {b : β} (h : f (l.getLast w) = some b) :
    (filterMap f l).getLast (ne_nil_of_mem (mem_filterMap.2 ⟨_, getLast_mem w, h⟩)) = b := by
  simp only [getLast_eq_head_reverse, ← filterMap_reverse]
  rw [head_filterMap_of_eq_some (by simp_all)]
  simp_all

theorem getLast?_flatMap {L : List α} {f : α → List β} :
    (L.flatMap f).getLast? = L.reverse.findSome? fun a => (f a).getLast? := by
  simp only [← head?_reverse, reverse_flatMap]
  rw [head?_flatMap]
  rfl

theorem getLast?_flatten {L : List (List α)} :
    (flatten L).getLast? = L.reverse.findSome? fun l => l.getLast? := by
  simp [← flatMap_id, getLast?_flatMap]

theorem getLast?_replicate (a : α) (n : Nat) : (replicate n a).getLast? = if n = 0 then none else some a := by
  simp only [← head?_reverse, reverse_replicate, head?_replicate]

@[simp] theorem getLast_replicate (w : replicate n a ≠ []) : (replicate n a).getLast w = a := by
  simp [getLast_eq_head_reverse]

/-! ## Additional operations -/

/-! ### leftpad -/

-- We unfold `leftpad` and `rightpad` for verification purposes.
attribute [simp] leftpad rightpad

-- `length_leftpad` is in `Init.Data.List.Nat.Basic`.

theorem leftpad_prefix (n : Nat) (a : α) (l : List α) :
    replicate (n - length l) a <+: leftpad n a l := by
  simp only [IsPrefix, leftpad]
  exact Exists.intro l rfl

theorem leftpad_suffix (n : Nat) (a : α) (l : List α) : l <:+ (leftpad n a l) := by
  simp only [IsSuffix, leftpad]
  exact Exists.intro (replicate (n - length l) a) rfl

/-! ## List membership -/

/-! ### elem / contains -/

theorem elem_cons_self [BEq α] [LawfulBEq α] {a : α} : (a::as).elem a = true := by simp

@[simp] theorem contains_cons [BEq α] :
    (a :: as : List α).contains x = (x == a || as.contains x) := by
  simp only [contains, elem]
  split <;> simp_all

theorem contains_eq_any_beq [BEq α] (l : List α) (a : α) : l.contains a = l.any (a == ·) := by
  induction l with simp | cons b l => cases b == a <;> simp [*]

theorem contains_iff_exists_mem_beq [BEq α] {l : List α} {a : α} :
    l.contains a ↔ ∃ a' ∈ l, a == a' := by
  induction l <;> simp_all

theorem contains_iff_mem [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    l.contains a ↔ a ∈ l := by
  simp

/-! ## Sublists -/

/-! ### partition

Because we immediately simplify `partition` into two `filter`s for verification purposes,
we do not separately develop much theory about it.
-/

@[simp] theorem partition_eq_filter_filter (p : α → Bool) (l : List α) :
    partition p l = (filter p l, filter (not ∘ p) l) := by simp [partition, aux]
  where
    aux : ∀ l {as bs}, partition.loop p l (as, bs) =
        (as.reverse ++ filter p l, bs.reverse ++ filter (not ∘ p) l)
      | [] => by simp [partition.loop, filter]
      | a :: l => by cases pa : p a <;> simp [partition.loop, pa, aux, filter, append_assoc]

theorem mem_partition : a ∈ l ↔ a ∈ (partition p l).1 ∨ a ∈ (partition p l).2 := by
  by_cases p a <;> simp_all

/-! ### dropLast

`dropLast` is the specification for `Array.pop`, so theorems about `List.dropLast`
are often used for theorems about `Array.pop`.
-/

@[simp] theorem length_dropLast : ∀ (xs : List α), xs.dropLast.length = xs.length - 1
  | [] => rfl
  | x::xs => by simp

@[simp] theorem getElem_dropLast : ∀ (xs : List α) (i : Nat) (h : i < xs.dropLast.length),
    xs.dropLast[i] = xs[i]'(Nat.lt_of_lt_of_le h (length_dropLast .. ▸ Nat.pred_le _))
  | _::_::_, 0, _ => rfl
  | _::_::_, i+1, _ => getElem_dropLast _ i _

@[deprecated getElem_dropLast (since := "2024-06-12")]
theorem get_dropLast (xs : List α) (i : Fin xs.dropLast.length) :
    xs.dropLast.get i = xs.get ⟨i, Nat.lt_of_lt_of_le i.isLt (length_dropLast .. ▸ Nat.pred_le _)⟩ := by
  simp

theorem getElem?_dropLast (xs : List α) (i : Nat) :
    xs.dropLast[i]? = if i < xs.length - 1 then xs[i]? else none := by
  split
  · rw [getElem?_eq_getElem, getElem?_eq_getElem, getElem_dropLast]
    simpa
  · simp_all

theorem head_dropLast (xs : List α) (h) :
    xs.dropLast.head h = xs.head (by rintro rfl; simp at h) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => simp at h
    | cons y ys => rfl

theorem head?_dropLast (xs : List α) : xs.dropLast.head? = if 1 < xs.length then xs.head? else none := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys => simp [Nat.succ_lt_succ_iff]

theorem getLast_dropLast {xs : List α} (h) :
   xs.dropLast.getLast h =
     xs[xs.length - 2]'(match xs, h with | (_ :: _ :: _), _ => Nat.lt_trans (Nat.lt_add_one _) (Nat.lt_add_one _)) := by
  rw [getLast_eq_getElem, getElem_dropLast]
  congr 1
  simp; rfl

theorem getLast?_dropLast {xs : List α} :
    xs.dropLast.getLast? = if xs.length ≤ 1 then none else xs[xs.length - 2]? := by
  split <;> rename_i h
  · match xs, h with
    | [], _
    | [_], _ => simp
  · rw [getLast?_eq_getElem?, getElem?_dropLast, if_pos]
    · congr 1
      simp [← Nat.sub_add_eq]
    · simp only [Nat.not_le] at h
      match xs, h with
      | (_ :: _ :: _), _ => simp

theorem dropLast_cons_of_ne_nil {α : Type u} {x : α}
    {l : List α} (h : l ≠ []) : (x :: l).dropLast = x :: l.dropLast := by
  simp [dropLast, h]

theorem dropLast_concat_getLast : ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: b :: l, _ => by
    rw [dropLast_cons₂, cons_append, getLast_cons (cons_ne_nil _ _)]
    congr
    exact dropLast_concat_getLast (cons_ne_nil b l)

@[simp] theorem map_dropLast (f : α → β) (l : List α) : l.dropLast.map f = (l.map f).dropLast := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases xs <;> simp [ih]

@[simp] theorem dropLast_append_of_ne_nil {α : Type u} {l : List α} :
    ∀ (l' : List α) (_ : l ≠ []), (l' ++ l).dropLast = l' ++ l.dropLast
  | [], _ => by simp only [nil_append]
  | a :: l', h => by
    rw [cons_append, dropLast, dropLast_append_of_ne_nil l' h, cons_append]
    simp [h]

theorem dropLast_append {l₁ l₂ : List α} :
    (l₁ ++ l₂).dropLast = if l₂.isEmpty then l₁.dropLast else l₁ ++ l₂.dropLast := by
  split <;> simp_all

theorem dropLast_append_cons : dropLast (l₁ ++ b :: l₂) = l₁ ++ dropLast (b :: l₂) := by
  simp

@[simp 1100] theorem dropLast_concat : dropLast (l₁ ++ [b]) = l₁ := by simp

@[simp] theorem dropLast_replicate (n) (a : α) : dropLast (replicate n a) = replicate (n - 1) a := by
  match n with
  | 0 => simp
  | 1 => simp [replicate_succ]
  | n+2 =>
    rw [replicate_succ, dropLast_cons_of_ne_nil, dropLast_replicate]
    · simp [replicate_succ]
    · simp

@[simp] theorem dropLast_cons_self_replicate (n) (a : α) :
    dropLast (a :: replicate n a) = replicate n a := by
  rw [← replicate_succ, dropLast_replicate, Nat.add_sub_cancel]

@[simp] theorem tail_reverse (l : List α) : l.reverse.tail = l.dropLast.reverse := by
  apply ext_getElem
  · simp
  · intro i h₁ h₂
    simp [Nat.add_comm i, Nat.sub_add_eq]

/-!
### splitAt

We don't provide any API for `splitAt`, beyond the `@[simp]` lemma
`splitAt n l = (l.take n, l.drop n)`,
which is proved in `Init.Data.List.TakeDrop`.
-/

theorem splitAt_go (n : Nat) (l acc : List α) :
    splitAt.go l xs n acc =
      if n < xs.length then (acc.reverse ++ xs.take n, xs.drop n) else (l, []) := by
  induction xs generalizing n acc with
  | nil => simp [splitAt.go]
  | cons x xs ih =>
    cases n with
    | zero => simp [splitAt.go]
    | succ n =>
      rw [splitAt.go, take_succ_cons, drop_succ_cons, ih n (x :: acc),
        reverse_cons, append_assoc, singleton_append, length_cons]
      simp only [Nat.succ_lt_succ_iff]

/-! ## Manipulating elements -/

/-! ### replace -/
section replace
variable [BEq α]

@[simp] theorem replace_cons_self [LawfulBEq α] {a : α} : (a::as).replace a b = b::as := by
  simp [replace_cons]

@[simp] theorem replace_of_not_mem {l : List α} (h : !l.elem a) : l.replace a b = l := by
  induction l <;> simp_all [replace_cons]

@[simp] theorem length_replace {l : List α} : (l.replace a b).length = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [replace_cons]
    split <;> simp_all

theorem getElem?_replace [LawfulBEq α] {l : List α} {i : Nat} :
    (l.replace a b)[i]? = if l[i]? == some a then if a ∈ l.take i then some a else some b else l[i]? := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons x xs ih =>
    cases i <;>
    · simp only [replace_cons]
      split <;> split <;> simp_all

theorem getElem?_replace_of_ne [LawfulBEq α] {l : List α} {i : Nat} (h : l[i]? ≠ some a) :
    (l.replace a b)[i]? = l[i]? := by
  simp_all [getElem?_replace]

theorem getElem_replace [LawfulBEq α] {l : List α} {i : Nat} (h : i < l.length) :
    (l.replace a b)[i]'(by simpa) = if l[i] == a then if a ∈ l.take i then a else b else l[i] := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_replace]
  split <;> split <;> simp_all

theorem getElem_replace_of_ne [LawfulBEq α] {l : List α} {i : Nat} {h : i < l.length} (h' : l[i] ≠ a) :
    (l.replace a b)[i]'(by simpa) = l[i]'(h) := by
  rw [getElem_replace h]
  simp [h']

theorem head?_replace (l : List α) (a b : α) :
    (l.replace a b).head? = match l.head? with
      | none => none
      | some x => some (if a == x then b else x) := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp [replace_cons]
    split <;> simp_all

theorem head_replace (l : List α) (a b : α) (w) :
    (l.replace a b).head w =
      if a == l.head (by rintro rfl; simp_all) then
        b
      else
        l.head  (by rintro rfl; simp_all) := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_replace, head?_eq_head]

theorem replace_append [LawfulBEq α] {l₁ l₂ : List α} :
    (l₁ ++ l₂).replace a b = if a ∈ l₁ then l₁.replace a b ++ l₂ else l₁ ++ l₂.replace a b := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, replace_cons]
    split <;> split <;> simp_all

theorem replace_append_left [LawfulBEq α] {l₁ l₂ : List α} (h : a ∈ l₁) :
    (l₁ ++ l₂).replace a b = l₁.replace a b ++ l₂ := by
  simp [replace_append, h]

theorem replace_append_right [LawfulBEq α] {l₁ l₂ : List α} (h : ¬ a ∈ l₁) :
    (l₁ ++ l₂).replace a b = l₁ ++ l₂.replace a b := by
  simp [replace_append, h]

theorem replace_take {l : List α} {n : Nat} :
    (l.take n).replace a b = (l.replace a b).take n := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp [ih]
    | succ n =>
      simp only [replace_cons, take_succ_cons]
      split <;> simp_all

@[simp] theorem replace_replicate_self [LawfulBEq α] {a : α} (h : 0 < n) :
    (replicate n a).replace a b = b :: replicate (n - 1) a := by
  cases n <;> simp_all [replicate_succ, replace_cons]

@[simp] theorem replace_replicate_ne {a b c : α} (h : !b == a) :
    (replicate n a).replace b c = replicate n a := by
  rw [replace_of_not_mem]
  simp_all

end replace

/-! ### insert -/

section insert
variable [BEq α]

@[simp] theorem insert_nil (a : α) : [].insert a = [a] := rfl

variable [LawfulBEq α]

@[simp] theorem insert_of_mem {l : List α} (h : a ∈ l) : l.insert a = l := by
  simp [List.insert, h]

@[simp] theorem insert_of_not_mem {l : List α} (h : a ∉ l) : l.insert a = a :: l := by
  simp [List.insert, h]

@[simp] theorem mem_insert_iff {l : List α} : a ∈ l.insert b ↔ a = b ∨ a ∈ l := by
  if h : b ∈ l then
    rw [insert_of_mem h]
    constructor; {apply Or.inr}
    intro
    | Or.inl h' => rw [h']; exact h
    | Or.inr h' => exact h'
  else rw [insert_of_not_mem h, mem_cons]

@[simp 1100] theorem mem_insert_self (a : α) (l : List α) : a ∈ l.insert a :=
  mem_insert_iff.2 (Or.inl rfl)

theorem mem_insert_of_mem {l : List α} (h : a ∈ l) : a ∈ l.insert b :=
  mem_insert_iff.2 (Or.inr h)

theorem eq_or_mem_of_mem_insert {l : List α} (h : a ∈ l.insert b) : a = b ∨ a ∈ l :=
  mem_insert_iff.1 h

@[simp] theorem length_insert_of_mem {l : List α} (h : a ∈ l) :
    length (l.insert a) = length l := by rw [insert_of_mem h]

@[simp] theorem length_insert_of_not_mem {l : List α} (h : a ∉ l) :
    length (l.insert a) = length l + 1 := by rw [insert_of_not_mem h]; rfl

theorem length_le_length_insert {l : List α} {a : α} : l.length ≤ (l.insert a).length := by
  by_cases h : a ∈ l
  · rw [length_insert_of_mem h]
    exact Nat.le_refl _
  · rw [length_insert_of_not_mem h]
    exact Nat.le_succ _

theorem length_insert_pos {l : List α} {a : α} : 0 < (l.insert a).length := by
  by_cases h : a ∈ l
  · rw [length_insert_of_mem h]
    exact length_pos_of_mem h
  · rw [length_insert_of_not_mem h]
    exact Nat.zero_lt_succ _

theorem insert_eq {l : List α} {a : α} : l.insert a = if a ∈ l then l else a :: l := by
  simp [List.insert]

theorem getElem?_insert_zero (l : List α) (a : α) :
    (l.insert a)[0]? = if a ∈ l then l[0]? else some a := by
  simp only [insert_eq]
  split <;> simp

theorem getElem?_insert_succ (l : List α) (a : α) (i : Nat) :
    (l.insert a)[i+1]? = if a ∈ l then l[i+1]? else l[i]? := by
  simp only [insert_eq]
  split <;> simp

theorem getElem?_insert (l : List α) (a : α) (i : Nat) :
    (l.insert a)[i]? = if a ∈ l then l[i]? else if i = 0 then some a else l[i-1]? := by
  cases i
  · simp [getElem?_insert_zero]
  · simp [getElem?_insert_succ]

theorem getElem_insert (l : List α) (a : α) (i : Nat) (h : i < l.length) :
    (l.insert a)[i]'(Nat.lt_of_lt_of_le h length_le_length_insert) =
      if a ∈ l then l[i] else if i = 0 then a else l[i-1]'(Nat.lt_of_le_of_lt (Nat.pred_le _) h) := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_insert]
  split
  · simp [getElem?_eq_getElem, h]
  · split
    · rfl
    · have h' : i - 1 < l.length := Nat.lt_of_le_of_lt (Nat.pred_le _) h
      simp [getElem?_eq_getElem, h']

theorem head?_insert (l : List α) (a : α) :
    (l.insert a).head? = some (if h : a ∈ l then l.head (ne_nil_of_mem h) else a) := by
  simp only [insert_eq]
  split <;> rename_i h
  · simp [head?_eq_head (ne_nil_of_mem h)]
  · rfl

theorem head_insert (l : List α) (a : α) (w) :
    (l.insert a).head w = if h : a ∈ l then l.head (ne_nil_of_mem h) else a := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_insert]

theorem insert_append {l₁ l₂ : List α} {a : α} :
    (l₁ ++ l₂).insert a = if a ∈ l₂ then l₁ ++ l₂ else l₁.insert a ++ l₂ := by
  simp only [insert_eq, mem_append]
  (repeat split) <;> simp_all

theorem insert_append_of_mem_left {l₁ l₂ : List α} (h : a ∈ l₂) :
    (l₁ ++ l₂).insert a = l₁ ++ l₂ := by
  simp [insert_append, h]

theorem insert_append_of_not_mem_left {l₁ l₂ : List α} (h : ¬ a ∈ l₂) :
    (l₁ ++ l₂).insert a = l₁.insert a ++ l₂ := by
  simp [insert_append, h]

@[simp] theorem insert_replicate_self {a : α} (h : 0 < n) : (replicate n a).insert a = replicate n a := by
  cases n <;> simp_all

@[simp] theorem insert_replicate_ne {a b : α} (h : !b == a) :
    (replicate n a).insert b = b :: replicate n a := by
  rw [insert_of_not_mem]
  simp_all

end insert

/-! ## Logic -/

/-! ### any / all -/

theorem not_any_eq_all_not (l : List α) (p : α → Bool) : (!l.any p) = l.all fun a => !p a := by
  induction l with simp | cons _ _ ih => rw [ih]

theorem not_all_eq_any_not (l : List α) (p : α → Bool) : (!l.all p) = l.any fun a => !p a := by
  induction l with simp | cons _ _ ih => rw [ih]

theorem and_any_distrib_left (l : List α) (p : α → Bool) (q : Bool) :
    (q && l.any p) = l.any fun a => q && p a := by
  induction l with simp | cons _ _ ih => rw [Bool.and_or_distrib_left, ih]

theorem and_any_distrib_right (l : List α) (p : α → Bool) (q : Bool) :
    (l.any p && q) = l.any fun a => p a && q := by
  induction l with simp | cons _ _ ih => rw [Bool.and_or_distrib_right, ih]

theorem or_all_distrib_left (l : List α) (p : α → Bool) (q : Bool) :
    (q || l.all p) = l.all fun a => q || p a := by
  induction l with simp | cons _ _ ih => rw [Bool.or_and_distrib_left, ih]

theorem or_all_distrib_right (l : List α) (p : α → Bool) (q : Bool) :
    (l.all p || q) = l.all fun a => p a || q := by
  induction l with simp | cons _ _ ih => rw [Bool.or_and_distrib_right, ih]

theorem any_eq_not_all_not (l : List α) (p : α → Bool) : l.any p = !l.all (!p .) := by
  simp only [not_all_eq_any_not, Bool.not_not]

theorem all_eq_not_any_not (l : List α) (p : α → Bool) : l.all p = !l.any (!p .) := by
  simp only [not_any_eq_all_not, Bool.not_not]

@[simp] theorem any_map {l : List α} {p : α → Bool} : (l.map f).any p = l.any (p ∘ f) := by
  induction l with simp | cons _ _ ih => rw [ih]

@[simp] theorem all_map {l : List α} {p : α → Bool} : (l.map f).all p = l.all (p ∘ f) := by
  induction l with simp | cons _ _ ih => rw [ih]

@[simp] theorem any_filter {l : List α} {p q : α → Bool} :
    (filter p l).any q = l.any fun a => p a && q a := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [filter_cons]
    split <;> simp_all

@[simp] theorem all_filter {l : List α} {p q : α → Bool} :
    (filter p l).all q = l.all fun a => p a → q a := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [filter_cons]
    split <;> simp_all

@[simp] theorem any_filterMap {l : List α} {f : α → Option β} {p : β → Bool} :
    (filterMap f l).any p = l.any fun a => match f a with | some b => p b | none => false := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [filterMap_cons]
    split <;> simp_all

@[simp] theorem all_filterMap {l : List α} {f : α → Option β} {p : β → Bool} :
    (filterMap f l).all p = l.all fun a => match f a with | some b => p b | none => true := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [filterMap_cons]
    split <;> simp_all

@[simp] theorem any_append {x y : List α} : (x ++ y).any f = (x.any f || y.any f) := by
  induction x with
  | nil => rfl
  | cons h t ih => simp_all [Bool.or_assoc]

@[simp] theorem all_append {x y : List α} : (x ++ y).all f = (x.all f && y.all f) := by
  induction x with
  | nil => rfl
  | cons h t ih => simp_all [Bool.and_assoc]

@[simp] theorem any_flatten {l : List (List α)} : l.flatten.any f = l.any (any · f) := by
  induction l <;> simp_all

@[deprecated any_flatten (since := "2024-10-14")] abbrev any_join := @any_flatten

@[simp] theorem all_flatten {l : List (List α)} : l.flatten.all f = l.all (all · f) := by
  induction l <;> simp_all

@[deprecated all_flatten (since := "2024-10-14")] abbrev all_join := @all_flatten

@[simp] theorem any_flatMap {l : List α} {f : α → List β} :
    (l.flatMap f).any p = l.any fun a => (f a).any p := by
  induction l <;> simp_all

@[simp] theorem all_flatMap {l : List α} {f : α → List β} :
    (l.flatMap f).all p = l.all fun a => (f a).all p := by
  induction l <;> simp_all

@[simp] theorem any_reverse {l : List α} : l.reverse.any f = l.any f := by
  induction l <;> simp_all [Bool.or_comm]

@[simp] theorem all_reverse {l : List α} : l.reverse.all f = l.all f := by
  induction l <;> simp_all [Bool.and_comm]

@[simp] theorem any_replicate {n : Nat} {a : α} :
    (replicate n a).any f = if n = 0 then false else f a := by
  cases n <;> simp [replicate_succ]

@[simp] theorem all_replicate {n : Nat} {a : α} :
    (replicate n a).all f = if n = 0 then true else f a := by
  cases n <;> simp +contextual [replicate_succ]

@[simp] theorem any_insert [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    (l.insert a).any f = (f a || l.any f) := by
  simp [any_eq]

@[simp] theorem all_insert [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    (l.insert a).all f = (f a && l.all f) := by
  simp [all_eq]

/-! ### Deprecations -/


@[deprecated flatten_nil (since := "2024-10-14")] abbrev join_nil := @flatten_nil
@[deprecated flatten_cons (since := "2024-10-14")] abbrev join_cons := @flatten_cons
@[deprecated length_flatten (since := "2024-10-14")] abbrev length_join := @length_flatten
@[deprecated flatten_singleton (since := "2024-10-14")] abbrev join_singleton := @flatten_singleton
@[deprecated mem_flatten (since := "2024-10-14")] abbrev mem_join := @mem_flatten
@[deprecated flatten_eq_nil_iff (since := "2024-09-05")] abbrev join_eq_nil := @flatten_eq_nil_iff
@[deprecated flatten_eq_nil_iff (since := "2024-10-14")] abbrev join_eq_nil_iff := @flatten_eq_nil_iff
@[deprecated flatten_ne_nil_iff (since := "2024-09-05")] abbrev join_ne_nil := @flatten_ne_nil_iff
@[deprecated flatten_ne_nil_iff (since := "2024-10-14")] abbrev join_ne_nil_iff := @flatten_ne_nil_iff
@[deprecated exists_of_mem_flatten (since := "2024-10-14")] abbrev exists_of_mem_join := @exists_of_mem_flatten
@[deprecated mem_flatten_of_mem (since := "2024-10-14")] abbrev mem_join_of_mem := @mem_flatten_of_mem
@[deprecated forall_mem_flatten (since := "2024-10-14")] abbrev forall_mem_join := @forall_mem_flatten
@[deprecated flatten_eq_flatMap (since := "2024-10-14")] abbrev join_eq_bind := @flatten_eq_flatMap
@[deprecated head?_flatten (since := "2024-10-14")] abbrev head?_join := @head?_flatten
@[deprecated foldl_flatten (since := "2024-10-14")] abbrev foldl_join := @foldl_flatten
@[deprecated foldr_flatten (since := "2024-10-14")] abbrev foldr_join := @foldr_flatten
@[deprecated map_flatten (since := "2024-10-14")] abbrev map_join := @map_flatten
@[deprecated filterMap_flatten (since := "2024-10-14")] abbrev filterMap_join := @filterMap_flatten
@[deprecated filter_flatten (since := "2024-10-14")] abbrev filter_join := @filter_flatten
@[deprecated flatten_filter_not_isEmpty (since := "2024-10-14")] abbrev join_filter_not_isEmpty := @flatten_filter_not_isEmpty
@[deprecated flatten_filter_ne_nil (since := "2024-10-14")] abbrev join_filter_ne_nil := @flatten_filter_ne_nil
@[deprecated filter_flatten (since := "2024-08-26")]
theorem join_map_filter (p : α → Bool) (l : List (List α)) :
    (l.map (filter p)).flatten = (l.flatten).filter p := by
  rw [filter_flatten]
@[deprecated flatten_append (since := "2024-10-14")] abbrev join_append := @flatten_append
@[deprecated flatten_concat (since := "2024-10-14")] abbrev join_concat := @flatten_concat
@[deprecated flatten_flatten (since := "2024-10-14")] abbrev join_join := @flatten_flatten
@[deprecated flatten_eq_cons_iff (since := "2024-09-05")] abbrev join_eq_cons_iff := @flatten_eq_cons_iff
@[deprecated flatten_eq_cons_iff (since := "2024-09-05")] abbrev join_eq_cons := @flatten_eq_cons_iff
@[deprecated flatten_eq_append_iff (since := "2024-09-05")] abbrev join_eq_append := @flatten_eq_append_iff
@[deprecated flatten_eq_append_iff (since := "2024-10-14")] abbrev join_eq_append_iff := @flatten_eq_append_iff
@[deprecated eq_iff_flatten_eq (since := "2024-10-14")] abbrev eq_iff_join_eq := @eq_iff_flatten_eq
@[deprecated flatten_replicate_nil (since := "2024-10-14")] abbrev join_replicate_nil := @flatten_replicate_nil
@[deprecated flatten_replicate_singleton (since := "2024-10-14")] abbrev join_replicate_singleton := @flatten_replicate_singleton
@[deprecated flatten_replicate_replicate (since := "2024-10-14")] abbrev join_replicate_replicate := @flatten_replicate_replicate
@[deprecated reverse_flatten (since := "2024-10-14")] abbrev reverse_join := @reverse_flatten
@[deprecated flatten_reverse (since := "2024-10-14")] abbrev join_reverse := @flatten_reverse
@[deprecated getLast?_flatten (since := "2024-10-14")] abbrev getLast?_join := @getLast?_flatten
@[deprecated flatten_eq_flatMap (since := "2024-10-16")] abbrev flatten_eq_bind := @flatten_eq_flatMap
@[deprecated flatMap_def (since := "2024-10-16")] abbrev bind_def := @flatMap_def
@[deprecated flatMap_id (since := "2024-10-16")] abbrev bind_id := @flatMap_id
@[deprecated mem_flatMap (since := "2024-10-16")] abbrev mem_bind := @mem_flatMap
@[deprecated exists_of_mem_flatMap (since := "2024-10-16")] abbrev exists_of_mem_bind := @exists_of_mem_flatMap
@[deprecated mem_flatMap_of_mem (since := "2024-10-16")] abbrev mem_bind_of_mem := @mem_flatMap_of_mem
@[deprecated flatMap_eq_nil_iff (since := "2024-10-16")] abbrev bind_eq_nil_iff := @flatMap_eq_nil_iff
@[deprecated forall_mem_flatMap (since := "2024-10-16")] abbrev forall_mem_bind := @forall_mem_flatMap
@[deprecated flatMap_singleton (since := "2024-10-16")] abbrev bind_singleton := @flatMap_singleton
@[deprecated flatMap_singleton' (since := "2024-10-16")] abbrev bind_singleton' := @flatMap_singleton'
@[deprecated head?_flatMap (since := "2024-10-16")] abbrev head_bind := @head?_flatMap
@[deprecated flatMap_append (since := "2024-10-16")] abbrev bind_append := @flatMap_append
@[deprecated flatMap_assoc (since := "2024-10-16")] abbrev bind_assoc := @flatMap_assoc
@[deprecated map_flatMap (since := "2024-10-16")] abbrev map_bind := @map_flatMap
@[deprecated flatMap_map (since := "2024-10-16")] abbrev bind_map := @flatMap_map
@[deprecated map_eq_flatMap (since := "2024-10-16")] abbrev map_eq_bind := @map_eq_flatMap
@[deprecated filterMap_flatMap (since := "2024-10-16")] abbrev filterMap_bind := @filterMap_flatMap
@[deprecated filter_flatMap (since := "2024-10-16")] abbrev filter_bind := @filter_flatMap
@[deprecated flatMap_eq_foldl (since := "2024-10-16")] abbrev bind_eq_foldl := @flatMap_eq_foldl
@[deprecated flatMap_replicate (since := "2024-10-16")] abbrev bind_replicate := @flatMap_replicate
@[deprecated reverse_flatMap (since := "2024-10-16")] abbrev reverse_bind := @reverse_flatMap
@[deprecated flatMap_reverse (since := "2024-10-16")] abbrev bind_reverse := @flatMap_reverse
@[deprecated getLast?_flatMap (since := "2024-10-16")] abbrev getLast?_bind := @getLast?_flatMap
@[deprecated any_flatMap (since := "2024-10-16")] abbrev any_bind := @any_flatMap
@[deprecated all_flatMap (since := "2024-10-16")] abbrev all_bind := @all_flatMap

end List
