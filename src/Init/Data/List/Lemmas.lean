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
import Init.PropLemmas
import Init.Control.Lawful.Basic
import Init.Hints

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

-/
namespace List

open Nat

-- We may want to replace these `simp` attributes with explicit equational lemmas,
-- as we already have for all the non-monadic functions.
attribute [simp] mapA forA filterAuxM firstM anyM allM findM? findSomeM?

-- Previously `range.loop`, `mapM.loop`, `filterMapM.loop`, `forIn.loop`, `forIn'.loop`
-- had attribute `@[simp]`.
-- We don't currently provide simp lemmas,
-- as this is an internal implementation and they don't seem to be needed.

/-! ### cons -/

theorem cons_ne_nil (a : α) (l : List α) : a :: l ≠ [] := nofun

@[simp]
theorem cons_ne_self (a : α) (l : List α) : a :: l ≠ l := mt (congrArg length) (Nat.succ_ne_self _)

theorem head_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : h₁ = h₂ := (cons.inj H).1

theorem tail_eq_of_cons_eq (H : h₁ :: t₁ = h₂ :: t₂) : t₁ = t₂ := (cons.inj H).2

theorem cons_inj (a : α) {l l' : List α} : a :: l = a :: l' ↔ l = l' :=
  ⟨tail_eq_of_cons_eq, congrArg _⟩

theorem cons_eq_cons {a b : α} {l l' : List α} : a :: l = b :: l' ↔ a = b ∧ l = l' :=
  List.cons.injEq .. ▸ .rfl

theorem exists_cons_of_ne_nil : ∀ {l : List α}, l ≠ [] → ∃ b L, l = b :: L
  | c :: l', _ => ⟨c, l', rfl⟩

/-! ### length -/

theorem eq_nil_of_length_eq_zero (_ : length l = 0) : l = [] := match l with | [] => rfl

theorem ne_nil_of_length_eq_succ (_ : length l = succ n) : l ≠ [] := fun _ => nomatch l

@[simp] theorem length_eq_zero : length l = 0 ↔ l = [] :=
  ⟨eq_nil_of_length_eq_zero, fun h => h ▸ rfl⟩

theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
  | _::_, _ => Nat.zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
  | _::_, _ => ⟨_, .head ..⟩

theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
  ⟨exists_mem_of_length_pos, fun ⟨_, h⟩ => length_pos_of_mem h⟩

theorem exists_cons_of_length_pos : ∀ {l : List α}, 0 < l.length → ∃ h t, l = h :: t
  | _::_, _ => ⟨_, _, rfl⟩

theorem length_pos_iff_exists_cons :
    ∀ {l : List α}, 0 < l.length ↔ ∃ h t, l = h :: t :=
  ⟨exists_cons_of_length_pos, fun ⟨_, _, eq⟩ => eq ▸ Nat.succ_pos _⟩

theorem exists_cons_of_length_succ :
    ∀ {l : List α}, l.length = n + 1 → ∃ h t, l = h :: t
  | _::_, _ => ⟨_, _, rfl⟩

theorem length_pos {l : List α} : 0 < length l ↔ l ≠ [] :=
  Nat.pos_iff_ne_zero.trans (not_congr length_eq_zero)

theorem exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
  exists_mem_of_length_pos (length_pos.2 h)

theorem length_eq_one {l : List α} : length l = 1 ↔ ∃ a, l = [a] :=
  ⟨fun h => match l, h with | [_], _ => ⟨_, rfl⟩, fun ⟨_, h⟩ => by simp [h]⟩

/-! ### L[i] and L[i]? -/

@[simp] theorem get_cons_zero : get (a::l) (0 : Fin (l.length + 1)) = a := rfl

@[simp] theorem get_cons_succ {as : List α} {h : i + 1 < (a :: as).length} :
  (a :: as).get ⟨i+1, h⟩ = as.get ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

@[simp] theorem get_cons_succ' {as : List α} {i : Fin as.length} :
  (a :: as).get i.succ = as.get i := rfl

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
  fun ⟨h, e⟩ => e ▸ get?_eq_get _⟩

theorem get?_eq_none : l.get? n = none ↔ length l ≤ n :=
  ⟨fun e => Nat.ge_of_not_lt (fun h' => by cases e ▸ get?_eq_some.2 ⟨h', rfl⟩), get?_len_le⟩

@[simp] theorem get?_eq_getElem? (l : List α) (i : Nat) : l.get? i = l[i]? := by
  simp only [getElem?]; split
  · exact (get?_eq_get ‹_›)
  · exact (get?_eq_none.2 <| Nat.not_lt.1 ‹_›)

@[simp] theorem get_eq_getElem (l : List α) (i : Fin l.length) : l.get i = l[i.1]'i.2 := rfl

@[simp] theorem getElem?_nil {n : Nat} : ([] : List α)[n]? = none := rfl

@[simp] theorem getElem?_cons_zero {l : List α} : (a::l)[0]? = some a := by
  simp only [← get?_eq_getElem?]
  rfl

@[simp] theorem getElem?_cons_succ {l : List α} : (a::l)[n+1]? = l[n]? := by
  simp only [← get?_eq_getElem?]
  rfl

theorem getElem?_len_le : ∀ {l : List α} {n}, length l ≤ n → l[n]? = none
  | [], _, _ => rfl
  | _ :: l, _+1, h => by
    rw [getElem?_cons_succ, getElem?_len_le (l := l) <| Nat.le_of_succ_le_succ h]

theorem getElem?_eq_getElem {l : List α} {n} (h : n < l.length) : l[n]? = some l[n] := by
  simp only [← get?_eq_getElem?, get?_eq_get, h, get_eq_getElem]

theorem getElem?_eq_some {l : List α} : l[n]? = some a ↔ ∃ h : n < l.length, l[n] = a := by
  simp only [← get?_eq_getElem?, get?_eq_some, get_eq_getElem]

@[simp] theorem getElem?_eq_none : l[n]? = none ↔ length l ≤ n := by
  simp only [← get?_eq_getElem?, get?_eq_none]

@[simp] theorem getElem!_nil [Inhabited α] {n : Nat} : ([] : List α)[n]! = default := rfl

@[simp] theorem getElem!_cons_zero [Inhabited α] {l : List α} : (a::l)[0]! = a := by
  rw [getElem!_pos] <;> simp

@[simp] theorem getElem!_cons_succ [Inhabited α] {l : List α} : (a::l)[n+1]! = l[n]! := by
  by_cases h : n < l.length
  · rw [getElem!_pos, getElem!_pos] <;> simp_all [Nat.succ_lt_succ_iff]
  · rw [getElem!_neg, getElem!_neg] <;> simp_all [Nat.succ_lt_succ_iff]

@[simp] theorem get_cons_cons_one : (a₁ :: a₂ :: as).get (1 : Fin (as.length + 2)) = a₂ := rfl

theorem get!_len_le [Inhabited α] : ∀ {l : List α} {n}, length l ≤ n → l.get! n = (default : α)
  | [], _, _ => rfl
  | _ :: l, _+1, h => get!_len_le (l := l) <| Nat.le_of_succ_le_succ h

theorem get?_zero (l : List α) : l.get? 0 = l.head? := by cases l <;> rfl

/--
If one has `l[i]` in an expression and `h : l = l'`,
`rw [h]` will give a "motive it not type correct" error, as it cannot rewrite the
implicit `i < l.length` to `i < l'.length` directly. The theorem `getElem_of_eq` can be used to make
such a rewrite, with `rw [getElem_of_eq h]`.
-/
theorem getElem_of_eq {l l' : List α} (h : l = l') {i : Nat} (w : i < l.length) :
    l[i] = l'[i]'(h ▸ w) := by cases h; rfl

/--
If one has `l.get i` in an expression (with `i : Fin l.length`) and `h : l = l'`,
`rw [h]` will give a "motive it not type correct" error, as it cannot rewrite the
`i : Fin l.length` to `Fin l'.length` directly. The theorem `get_of_eq` can be used to make
such a rewrite, with `rw [get_of_eq h]`.
-/
theorem get_of_eq {l l' : List α} (h : l = l') (i : Fin l.length) :
    get l i = get l' ⟨i, h ▸ i.2⟩ := by cases h; rfl

@[simp] theorem getElem_singleton (a : α) (h : i < 1) : [a][i] = a :=
  match i, h with
  | 0, _ => rfl

@[deprecated getElem_singleton (since := "2024-06-12")]
theorem get_singleton (a : α) (n : Fin 1) : get [a] n = a := by simp

theorem getElem_zero {l : List α} (h : 0 < l.length) : l[0] = l.head (length_pos.mp h) :=
  match l, h with
  | _ :: _, _ => rfl

theorem get_mk_zero : ∀ {l : List α} (h : 0 < l.length), l.get ⟨0, h⟩ = l.head (length_pos.mp h)
  | _::_, _ => rfl

theorem getElem!_of_getElem? [Inhabited α] : ∀ {l : List α} {n : Nat}, l[n]? = some a → l[n]! = a
  | _a::_, 0, _ => by
    rw [getElem!_pos] <;> simp_all
  | _::l, _+1, e => by
    simp at e
    simp_all [getElem!_of_getElem? (l := l) e]

theorem get!_of_get? [Inhabited α] : ∀ {l : List α} {n}, get? l n = some a → get! l n = a
  | _a::_, 0, rfl => rfl
  | _::l, _+1, e => get!_of_get? (l := l) e

@[simp] theorem get!_eq_getD [Inhabited α] : ∀ (l : List α) n, l.get! n = l.getD n default
  | [], _      => rfl
  | _a::_, 0   => rfl
  | _a::l, n+1 => get!_eq_getD l n

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

@[simp] theorem getElem?_concat_length : ∀ (l : List α) (a : α), (l ++ [a])[l.length]? = some a
  | [], a => rfl
  | b :: l, a => by rw [cons_append, length_cons]; simp [getElem?_concat_length]

@[deprecated getElem?_concat_length (since := "2024-06-12")]
theorem get?_concat_length (l : List α) (a : α) : (l ++ [a]).get? l.length = some a := by simp

/-! ### concat -/

-- As `List.concat` is defined in `Init.Prelude`, we write the basic simplification lemmas here.
theorem concat_nil (a : α) : concat [] a = [a] :=
  rfl
theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b :=
  rfl

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ := by
  simp

theorem last_eq_of_concat_eq {a b : α} {l : List α} : concat l a = concat l b → a = b := by
  simp

theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] := by cases l <;> simp

theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by simp

theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by simp

theorem eq_nil_or_concat : ∀ l : List α, l = [] ∨ ∃ L b, l = L ++ [b]
  | [] => .inl rfl
  | a::l => match l, eq_nil_or_concat l with
    | _, .inl rfl => .inr ⟨[], a, rfl⟩
    | _, .inr ⟨L, b, rfl⟩ => .inr ⟨a::L, b, rfl⟩

/-! ### mem -/

@[simp] theorem not_mem_nil (a : α) : ¬ a ∈ [] := nofun

@[simp] theorem mem_cons : a ∈ (b :: l) ↔ a = b ∨ a ∈ l :=
  ⟨fun h => by cases h <;> simp [Membership.mem, *],
   fun | Or.inl rfl => by constructor | Or.inr h => by constructor; assumption⟩

theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l := .head ..

theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := .tail _

theorem eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  cases l <;> simp [-not_or]

theorem eq_of_mem_singleton : a ∈ [b] → a = b
  | .head .. => rfl

@[simp 1100] theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
  ⟨eq_of_mem_singleton, (by simp [·])⟩

theorem forall_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∀ x, x ∈ a :: l → p x) ↔ p a ∧ ∀ x, x ∈ l → p x :=
  ⟨fun H => ⟨H _ (.head ..), fun _ h => H _ (.tail _ h)⟩,
   fun ⟨H₁, H₂⟩ _ => fun | .head .. => H₁ | .tail _ h => H₂ _ h⟩

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

theorem elem_iff [BEq α] [LawfulBEq α] {a : α} {as : List α} :
    elem a as = true ↔ a ∈ as := ⟨mem_of_elem_eq_true, elem_eq_true_of_mem⟩

@[simp] theorem elem_eq_mem [BEq α] [LawfulBEq α] (a : α) (as : List α) :
    elem a as = decide (a ∈ as) := by rw [Bool.eq_iff_iff, elem_iff, decide_eq_true_iff]

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
  Or.elim (mem_cons.mp h₂) (absurd · h₁) (·)

theorem ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ≠ b := mt (· ▸ .head _)

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : a ∉ b::l → a ∉ l := mt (.tail _)

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y::l :=
  mt ∘ mem_of_ne_of_mem

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
  fun p => ⟨ne_of_not_mem_cons p, not_mem_of_not_mem_cons p⟩

theorem getElem_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ (n : Nat) (h : n < l.length), l[n]'h = a
  | _, _ :: _, .head .. => ⟨0, Nat.succ_pos _, rfl⟩
  | _, _ :: _, .tail _ m => let ⟨n, h, e⟩ := getElem_of_mem m; ⟨n+1, Nat.succ_lt_succ h, e⟩

theorem get_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n, get l n = a := by
  obtain ⟨n, h, e⟩ := getElem_of_mem h
  exact ⟨⟨n, h⟩, e⟩

theorem getElem_mem : ∀ (l : List α) n (h : n < l.length), l[n]'h ∈ l
  | _ :: _, 0, _ => .head ..
  | _ :: l, _+1, _ => .tail _ (getElem_mem l ..)

theorem get_mem : ∀ (l : List α) n h, get l ⟨n, h⟩ ∈ l
  | _ :: _, 0, _ => .head ..
  | _ :: l, _+1, _ => .tail _ (get_mem l ..)

theorem mem_iff_getElem {a} {l : List α} : a ∈ l ↔ ∃ (n : Nat) (h : n < l.length), l[n]'h = a :=
  ⟨getElem_of_mem, fun ⟨_, _, e⟩ => e ▸ getElem_mem ..⟩

theorem mem_iff_get {a} {l : List α} : a ∈ l ↔ ∃ n, get l n = a :=
  ⟨get_of_mem, fun ⟨_, e⟩ => e ▸ get_mem ..⟩

theorem getElem?_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n : Nat, l[n]? = some a :=
  let ⟨n, _, e⟩ := getElem_of_mem h; ⟨n, e ▸ getElem?_eq_getElem _⟩

theorem get?_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n, l.get? n = some a :=
  let ⟨⟨n, _⟩, e⟩ := get_of_mem h; ⟨n, e ▸ get?_eq_get _⟩

theorem getElem?_mem {l : List α} {n : Nat} {a : α} (e : l[n]? = some a) : a ∈ l :=
  let ⟨_, e⟩ := getElem?_eq_some.1 e; e ▸ getElem_mem ..

theorem get?_mem {l : List α} {n a} (e : l.get? n = some a) : a ∈ l :=
  let ⟨_, e⟩ := get?_eq_some.1 e; e ▸ get_mem ..

theorem mem_iff_getElem? {a} {l : List α} : a ∈ l ↔ ∃ n : Nat, l[n]? = some a := by
  simp [getElem?_eq_some, mem_iff_getElem]

theorem mem_iff_get? {a} {l : List α} : a ∈ l ↔ ∃ n, l.get? n = some a := by
  simp [getElem?_eq_some, Fin.exists_iff, mem_iff_get]

/-! ### set -/

@[simp] theorem set_nil (n : Nat) (a : α) : [].set n a = [] := rfl

@[simp] theorem set_zero (x : α) (xs : List α) (a : α) :
  (x :: xs).set 0 a = a :: xs := rfl

@[simp] theorem set_succ (x : α) (xs : List α) (n : Nat) (a : α) :
  (x :: xs).set (n + 1) a = x :: xs.set n a := rfl

@[simp] theorem getElem_set_eq (l : List α) (i : Nat) (a : α) (h : i < (l.set i a).length) :
    (l.set i a)[i] = a :=
  match l, i with
  | [], _ => by
    simp at h
    contradiction
  | _ :: _, 0 => by
    simp
  | _ :: l, i + 1 => by
    simp [getElem_set_eq l]

@[deprecated getElem_set_eq (since := "2024-06-12")]
theorem get_set_eq (l : List α) (i : Nat) (a : α) (h : i < (l.set i a).length) :
    (l.set i a).get ⟨i, h⟩ = a :=
  by simp

@[simp] theorem getElem_set_ne (l : List α) {i j : Nat} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a)[j] = l[j]'(by simp at hj; exact hj) :=
  match l, i, j with
  | [], _, _ => by
    simp
  | _ :: _, 0, 0 => by
    contradiction
  | _ :: _, 0, _ + 1 => by
    simp
  | _ :: _, _ + 1, 0 => by
    simp
  | _ :: l, i + 1, j + 1 => by
    have g : i ≠ j := h ∘ congrArg (· + 1)
    simp [getElem_set_ne l g]

@[deprecated getElem_set_ne (since := "2024-06-12")]
theorem get_set_ne (l : List α) {i j : Nat} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a).get ⟨j, hj⟩ = l.get ⟨j, by simp at hj; exact hj⟩ := by
  simp [h]

@[simp] theorem set_eq_nil (l : List α) (n : Nat) (a : α) : l.set n a = [] ↔ l = [] := by
  cases l <;> cases n <;> simp only [set]

theorem set_comm (a b : α) : ∀ {n m : Nat} (l : List α), n ≠ m →
    (l.set n a).set m b = (l.set m b).set n a
  | _, _, [], _ => by simp
  | n+1, 0, _ :: _, _ => by simp [set]
  | 0, m+1, _ :: _, _ => by simp [set]
  | n+1, m+1, x :: t, h =>
    congrArg _ <| set_comm a b t fun h' => h <| Nat.succ_inj'.mpr h'

@[simp]
theorem set_set (a b : α) : ∀ (l : List α) (n : Nat), (l.set n a).set n b = l.set n b
  | [], _ => by simp
  | _ :: _, 0 => by simp [set]
  | _ :: _, _+1 => by simp [set, set_set]

theorem getElem_set (a : α) {m n} (l : List α) (h) :
    (set l m a)[n]'h = if m = n then a else l[n]'(length_set .. ▸ h) := by
  if h : m = n then
    subst m; simp only [getElem_set_eq, ↓reduceIte]
  else
    simp [h]

@[deprecated getElem_set (since := "2024-06-12")]
theorem get_set (a : α) {m n} (l : List α) (h) :
    (set l m a).get ⟨n, h⟩ = if m = n then a else l.get ⟨n, length_set .. ▸ h⟩ := by
  simp [getElem_set]

theorem mem_or_eq_of_mem_set : ∀ {l : List α} {n : Nat} {a b : α}, a ∈ l.set n b → a ∈ l ∨ a = b
  | _ :: _, 0, _, _, h => ((mem_cons ..).1 h).symm.imp_left (.tail _)
  | _ :: _, _+1, _, _, .head .. => .inl (.head ..)
  | _ :: _, _+1, _, _, .tail _ h => (mem_or_eq_of_mem_set h).imp_left (.tail _)

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

@[simp] theorem foldrM_append [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (l l' : List α) :
    (l ++ l').foldrM f b = l'.foldrM f b >>= l.foldrM f := by
  induction l <;> simp [*]

@[simp] theorem foldl_append {β : Type _} (f : β → α → β) (b) (l l' : List α) :
    (l ++ l').foldl f b = l'.foldl f (l.foldl f b) := by simp [foldl_eq_foldlM]

@[simp] theorem foldr_append (f : α → β → β) (b) (l l' : List α) :
    (l ++ l').foldr f b = l.foldr f (l'.foldr f b) := by simp [foldr_eq_foldrM]

@[simp] theorem foldr_self_append (l : List α) : l.foldr cons l' = l ++ l' := by
  induction l <;> simp [*]

theorem foldr_self (l : List α) : l.foldr cons [] = l := by simp

theorem foldl_map (f : β₁ → β₂) (g : α → β₂ → α) (l : List β₁) (init : α) :
    (l.map f).foldl g init = l.foldl (fun x y => g x (f y)) init := by
  induction l generalizing init <;> simp [*]

theorem foldr_map (f : α₁ → α₂) (g : α₂ → β → β) (l : List α₁) (init : β) :
    (l.map f).foldr g init = l.foldr (fun x y => g (f x) y) init := by
  induction l generalizing init <;> simp [*]

/-! ### lt -/

theorem lt_irrefl' [LT α] (lt_irrefl : ∀ x : α, ¬x < x) (l : List α) : ¬l < l := by
  induction l with
  | nil => nofun
  | cons a l ih => intro
    | .head _ _ h => exact lt_irrefl _ h
    | .tail _ _ h => exact ih h

theorem lt_trans' [LT α] [DecidableRel (@LT.lt α _)]
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

theorem lt_antisymm' [LT α]
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


/-! ### getD -/

@[simp] theorem getD_eq_getElem? (l) (n) (a : α) : getD l n a = (l[n]?).getD a := by
  simp [getD]

@[deprecated getD_eq_getElem? (since := "2024-06-12")]
theorem getD_eq_get? : ∀ l n (a : α), getD l n a = (get? l n).getD a := by simp

/-! ### getLast -/

theorem getLast_eq_get : ∀ (l : List α) (h : l ≠ []),
    getLast l h = l.get ⟨l.length - 1, by
      match l with
      | [] => contradiction
      | a :: l => exact Nat.le_refl _⟩
  | [a], h => rfl
  | a :: b :: l, h => by
    simp [getLast, get, Nat.succ_sub_succ, getLast_eq_get]

theorem getLast_cons' {a : α} {l : List α} : ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil),
  getLast (a :: l) h₁ = getLast l h₂ := by
  induction l <;> intros; {contradiction}; rfl

theorem getLast_eq_getLastD (a l h) : @getLast α (a::l) h = getLastD l a := by
  cases l <;> rfl

theorem getLastD_eq_getLast? (a l) : @getLastD α l a = (getLast? l).getD a := by
  cases l <;> rfl

@[simp] theorem getLast_singleton (a h) : @getLast α [a] h = a := rfl

theorem getLast!_cons [Inhabited α] : @getLast! α _ (a::l) = getLastD l a := by
  simp [getLast!, getLast_eq_getLastD]

theorem getLast_mem : ∀ {l : List α} (h : l ≠ []), getLast l h ∈ l
  | [], h => absurd rfl h
  | [_], _ => .head ..
  | _::a::l, _ => .tail _ <| getLast_mem (cons_ne_nil a l)

theorem getLastD_mem_cons : ∀ (l : List α) (a : α), getLastD l a ∈ a::l
  | [], _ => .head ..
  | _::_, _ => .tail _ <| getLast_mem _

theorem getElem_cons_length (x : α) (xs : List α) (n : Nat) (h : n = xs.length) :
    (x :: xs)[n]'(by simp [h]) = (x :: xs).getLast (cons_ne_nil x xs) := by
  rw [getLast_eq_get]; cases h; rfl

@[deprecated getElem_cons_length (since := "2024-06-12")]
theorem get_cons_length (x : α) (xs : List α) (n : Nat) (h : n = xs.length) :
    (x :: xs).get ⟨n, by simp [h]⟩ = (x :: xs).getLast (cons_ne_nil x xs) := by
  simp [getElem_cons_length, h]

/-! ### getLast? -/

theorem getLast?_cons : @getLast? α (a::l) = getLastD l a := by
  simp [getLast?, getLast_eq_getLastD]

@[simp] theorem getLast?_singleton (a : α) : getLast? [a] = a := rfl

theorem getLast?_eq_getLast : ∀ l h, @getLast? α l = some (getLast l h)
  | [], h => nomatch h rfl
  | _::_, _ => rfl

theorem getLast?_eq_get? : ∀ (l : List α), getLast? l = l.get? (l.length - 1)
  | [] => rfl
  | a::l => by rw [getLast?_eq_getLast (a::l) nofun, getLast_eq_get, get?_eq_get]

@[simp] theorem getLast?_concat (l : List α) : getLast? (l ++ [a]) = some a := by
  simp [getLast?_eq_get?, Nat.succ_sub_succ]

@[simp] theorem getLastD_concat (a b l) : @getLastD α (l ++ [b]) a = b := by
  rw [getLastD_eq_getLast?, getLast?_concat]; rfl

/-! ### head -/

theorem head!_of_head? [Inhabited α] : ∀ {l : List α}, head? l = some a → head! l = a
  | _a::_l, rfl => rfl

theorem head?_eq_head : ∀ l h, @head? α l = some (head l h)
  | _::_, _ => rfl

/-! ### tail -/

@[simp] theorem tailD_eq_tail? (l l' : List α) : tailD l l' = (tail? l).getD l' := by
  cases l <;> rfl

/-! ### map -/

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

@[simp] theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁; induction l₁ <;> intros <;> simp_all

@[simp] theorem map_id (l : List α) : map id l = l := by induction l <;> simp_all

@[simp] theorem map_id' (l : List α) : map (fun a => a) l = l := by induction l <;> simp_all

@[simp] theorem mem_map {f : α → β} : ∀ {l : List α}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b
  | [] => by simp
  | _ :: l => by simp [mem_map (l := l), eq_comm (a := b)]

theorem mem_map_of_mem (f : α → β) (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

@[simp] theorem map_map (g : β → γ) (f : α → β) (l : List α) :
  map g (map f l) = map (g ∘ f) l := by induction l <;> simp_all

theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] := rfl

theorem exists_of_mem_map (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b := mem_map.1 h

theorem forall_mem_map_iff {f : α → β} {l : List α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ l.map f), P i) ↔ ∀ (j) (_ : j ∈ l), P (f j) := by
  simp

@[simp] theorem map_eq_nil {f : α → β} {l : List α} : map f l = [] ↔ l = [] := by
  constructor <;> exact fun _ => match l with | [] => rfl

/-! ### filter -/

@[simp] theorem filter_cons_of_pos {p : α → Bool} {a : α} (l) (pa : p a) :
    filter p (a :: l) = a :: filter p l := by rw [filter, pa]

@[simp] theorem filter_cons_of_neg {p : α → Bool} {a : α} (l) (pa : ¬ p a) :
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

theorem mem_filter : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  induction as with
  | nil => simp [filter]
  | cons a as ih =>
    by_cases h : p a
    · simp_all [or_and_left]
    · simp_all [or_and_right]

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a, a ∈ l → ¬p a := by
  simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

@[simp] theorem filter_filter (q) : ∀ l, filter p (filter q l) = filter (fun a => p a ∧ q a) l
  | [] => rfl
  | a :: l => by by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq, filter_filter _ l]

theorem filter_map (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  induction l with
  | nil => rfl
  | cons a l IH => by_cases h : p (f a) <;> simp [*]

@[deprecated filter_map (since := "2024-06-15")] abbrev map_filter := @filter_map

@[simp] theorem filter_append {p : α → Bool} :
    ∀ (l₁ l₂ : List α), filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by simp [filter]; split <;> simp [filter_append l₁]

theorem filter_congr' {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x ↔ q x) → filter p l = filter q l
  | [], _ => rfl
  | a :: l, h => by
    rw [forall_mem_cons] at h; by_cases pa : p a
    · simp [pa, h.1.1 pa, filter_congr' h.2]
    · simp [pa, mt h.1.2 pa, filter_congr' h.2]

/-! ### filterMap -/

theorem filterMap_cons_none {f : α → Option β} (a : α) (l : List α) (h : f a = none) :
    filterMap f (a :: l) = filterMap f l := by simp only [filterMap, h]

theorem filterMap_cons_some (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) :
    filterMap f (a :: l) = b :: filterMap f l := by simp only [filterMap, h]

@[simp]
theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f := by
  funext l; induction l <;> simp [*]

@[simp] theorem filterMap_some (l : List α) : filterMap some l = l := by
  erw [filterMap_eq_map, map_id]

theorem map_filterMap_some_eq_filter_map_is_some (f : α → Option β) (l : List α) :
    (l.filterMap f).map some = (l.map f).filter fun b => b.isSome := by
  induction l <;> simp; split <;> simp [*]

theorem length_filterMap_le (f : α → Option β) (l : List α) :
    (filterMap f l).length ≤ l.length := by
  rw [← length_map _ some, map_filterMap_some_eq_filter_map_is_some, ← length_map _ f]
  apply length_filter_le

@[simp]
theorem filterMap_eq_filter (p : α → Bool) :
    filterMap (Option.guard (p ·)) = filter p := by
  funext l
  induction l with
  | nil => rfl
  | cons a l IH => by_cases pa : p a <;> simp [Option.guard, pa, ← IH]

theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (l : List α) :
    filterMap g (filterMap f l) = filterMap (fun x => (f x).bind g) l := by
  induction l with
  | nil => rfl
  | cons a l IH => cases h : f a <;> simp [*]

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

@[simp] theorem mem_filterMap (f : α → Option β) (l : List α) {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b := by
  induction l <;> simp; split <;> simp [*, eq_comm]

theorem filterMap_append {α β : Type _} (l l' : List α) (f : α → Option β) :
    filterMap f (l ++ l') = filterMap f l ++ filterMap f l' := by
  induction l <;> simp; split <;> simp [*]

@[simp] theorem filterMap_join (f : α → Option β) (L : List (List α)) :
    filterMap f (join L) = join (map (filterMap f) L) := by
  induction L <;> simp [*, filterMap_append]

theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (l : List α) : map g (filterMap f l) = l := by simp only [map_filterMap, H, filterMap_some]

/-! ### append -/

theorem getElem?_append_right : ∀ {l₁ l₂ : List α} {n : Nat}, l₁.length ≤ n →
  (l₁ ++ l₂)[n]? = l₂[n - l₁.length]?
| [], _, n, _ => rfl
| a :: l, _, n+1, h₁ => by
  rw [cons_append]
  simp [Nat.succ_sub_succ_eq_sub, getElem?_append_right (Nat.lt_succ.1 h₁)]

@[deprecated getElem?_append_right (since := "2024-06-12")]
theorem get?_append_right {l₁ l₂ : List α} {n : Nat} (h : l₁.length ≤ n) :
    (l₁ ++ l₂).get? n = l₂.get? (n - l₁.length) := by
  simp [getElem?_append_right, h]

theorem getElem_append_right' {l₁ l₂ : List α} {n : Nat} (h₁ : l₁.length ≤ n) (h₂) :
    (l₁ ++ l₂)[n]'h₂ =
      l₂[n - l₁.length]'(by rw [length_append] at h₂; exact Nat.sub_lt_left_of_lt_add h₁ h₂) :=
  Option.some.inj <| by rw [← getElem?_eq_getElem, ← getElem?_eq_getElem, getElem?_append_right h₁]

@[deprecated (since := "2024-06-12")]
theorem get_append_right_aux {l₁ l₂ : List α} {n : Nat}
  (h₁ : l₁.length ≤ n) (h₂ : n < (l₁ ++ l₂).length) : n - l₁.length < l₂.length := by
  rw [length_append] at h₂
  exact Nat.sub_lt_left_of_lt_add h₁ h₂

set_option linter.deprecated false in
@[deprecated getElem_append_right' (since := "2024-06-12")]
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

theorem append_of_mem {a : α} {l : List α} : a ∈ l → ∃ s t : List α, l = s ++ a :: t
  | .head l => ⟨[], l, rfl⟩
  | .tail b h => let ⟨s, t, h'⟩ := append_of_mem h; ⟨b::s, t, by rw [h', cons_append]⟩

@[simp 1100] theorem singleton_append : [x] ++ l = x :: l := rfl

theorem append_inj :
    ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
  | [], [], t₁, t₂, h, _ => ⟨rfl, h⟩
  | a :: s₁, b :: s₂, t₁, t₂, h, hl => by
    simp [append_inj (cons.inj h).2 (Nat.succ.inj hl)] at h ⊢; exact h

theorem append_inj_right (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : t₁ = t₂ :=
  (append_inj h hl).right

theorem append_inj_left (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : s₁ = s₂ :=
  (append_inj h hl).left

theorem append_inj' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h <| @Nat.add_right_cancel _ (length t₁) _ <| by
  let hap := congrArg length h; simp only [length_append, ← hl] at hap; exact hap

theorem append_inj_right' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : t₁ = t₂ :=
  (append_inj' h hl).right

theorem append_inj_left' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ :=
  (append_inj' h hl).left

theorem append_right_inj {t₁ t₂ : List α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  ⟨fun h => append_inj_right h rfl, congrArg _⟩

theorem append_left_inj {s₁ s₂ : List α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  ⟨fun h => append_inj_left' h rfl, congrArg (· ++ _)⟩

@[simp] theorem append_eq_nil : p ++ q = [] ↔ p = [] ∧ q = [] := by
  cases p <;> simp

@[simp] theorem getLast_append {a : α} : ∀ (l : List α) h, getLast (l ++ [a]) h = a
  | [], _ => rfl
  | a::t, h => by
    simp [getLast_cons' _ fun H => cons_ne_nil _ _ (append_eq_nil.1 H).2, getLast_append t]

theorem getLast_concat : getLast (concat l a) h = a := by
  simp [concat_eq_append, getLast_append]

theorem getElem_append : ∀ {l₁ l₂ : List α} (n : Nat) (h : n < l₁.length),
    (l₁ ++ l₂)[n]'(length_append .. ▸ Nat.lt_add_right _ h) = l₁[n]
| a :: l, _, 0, h => rfl
| a :: l, _, n+1, h => by simp only [get, cons_append]; apply getElem_append

@[deprecated getElem_append (since := "2024-06-12")]
theorem get_append {l₁ l₂ : List α} (n : Nat) (h : n < l₁.length) :
    (l₁ ++ l₂).get ⟨n, length_append .. ▸ Nat.lt_add_right _ h⟩ = l₁.get ⟨n, h⟩ := by
  simp [getElem_append, h]

@[deprecated getElem_append_left (since := "2024-06-12")]
theorem get_append_left (as bs : List α) (h : i < as.length) {h'} : (as ++ bs).get ⟨i, h'⟩ = as.get ⟨i, h⟩ := by
  simp [getElem_append_left, h, h']

@[deprecated getElem_append_right (since := "2024-06-12")]
theorem get_append_right (as bs : List α) (h : ¬ i < as.length) {h' h''} : (as ++ bs).get ⟨i, h'⟩ = bs.get ⟨i - as.length, h''⟩ := by
  simp [getElem_append_right, h, h', h'']

theorem getElem?_append {l₁ l₂ : List α} {n : Nat} (hn : n < l₁.length) :
    (l₁ ++ l₂)[n]? = l₁[n]? := by
  have hn' : n < (l₁ ++ l₂).length := Nat.lt_of_lt_of_le hn <|
    length_append .. ▸ Nat.le_add_right ..
  simp_all [getElem?_eq_getElem, getElem_append]

@[deprecated (since := "2024-06-12")]
theorem get?_append {l₁ l₂ : List α} {n : Nat} (hn : n < l₁.length) :
    (l₁ ++ l₂).get? n = l₁.get? n := by
  simp [getElem?_append hn]

theorem append_eq_append : List.append l₁ l₂ = l₁ ++ l₂ := rfl

theorem append_ne_nil_of_ne_nil_left (s t : List α) : s ≠ [] → s ++ t ≠ [] := by simp_all

theorem append_ne_nil_of_ne_nil_right (s t : List α) : t ≠ [] → s ++ t ≠ [] := by simp_all

@[simp] theorem nil_eq_append : [] = a ++ b ↔ a = [] ∧ b = [] := by
  rw [eq_comm, append_eq_nil]

theorem append_ne_nil_of_left_ne_nil (a b : List α) (h0 : a ≠ []) : a ++ b ≠ [] := by simp [*]

theorem append_eq_cons :
    a ++ b = x :: c ↔ (a = [] ∧ b = x :: c) ∨ (∃ a', a = x :: a' ∧ c = a' ++ b) := by
  cases a with simp | cons a as => ?_
  exact ⟨fun h => ⟨as, by simp [h]⟩, fun ⟨a', ⟨aeq, aseq⟩, h⟩ => ⟨aeq, by rw [aseq, h]⟩⟩

theorem cons_eq_append :
    x :: c = a ++ b ↔ (a = [] ∧ b = x :: c) ∨ (∃ a', a = x :: a' ∧ c = a' ++ b) := by
  rw [eq_comm, append_eq_cons]

theorem append_eq_append_iff {a b c d : List α} :
    a ++ b = c ++ d ↔ (∃ a', c = a ++ a' ∧ b = a' ++ d) ∨ ∃ c', a = c ++ c' ∧ d = c' ++ b := by
  induction a generalizing c with
  | nil => simp_all
  | cons a as ih => cases c <;> simp [eq_comm, and_assoc, ih, and_or_left]

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

/-! ### join -/

theorem mem_join : ∀ {L : List (List α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l
  | [] => by simp
  | b :: l => by simp [mem_join, or_and_right, exists_or]

theorem exists_of_mem_join : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l := mem_join.1

theorem mem_join_of_mem (lL : l ∈ L) (al : a ∈ l) : a ∈ join L := mem_join.2 ⟨l, lL, al⟩

/-! ### bind -/

@[simp] theorem append_bind xs ys (f : α → List β) :
  List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs; {rfl}; simp_all [bind_cons, append_assoc]

@[simp] theorem bind_id (l : List (List α)) : List.bind l id = l.join := by simp [List.bind]

theorem mem_bind {f : α → List β} {b} {l : List α} : b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [List.bind, mem_join]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_bind {b : β} {l : List α} {f : α → List β} :
    b ∈ List.bind l f → ∃ a, a ∈ l ∧ b ∈ f a := mem_bind.1

theorem mem_bind_of_mem {b : β} {l : List α} {f : α → List β} {a} (al : a ∈ l) (h : b ∈ f a) :
    b ∈ List.bind l f := mem_bind.2 ⟨a, al, h⟩

theorem bind_map (f : β → γ) (g : α → List β) :
    ∀ l : List α, map f (l.bind g) = l.bind fun a => (g a).map f
  | [] => rfl
  | a::l => by simp only [bind_cons, map_append, bind_map _ _ l]

/-! ### replicate -/

theorem replicate_succ (a : α) (n) : replicate (n+1) a = a :: replicate n a := rfl

theorem mem_replicate {a b : α} : ∀ {n}, b ∈ replicate n a ↔ n ≠ 0 ∧ b = a
  | 0 => by simp
  | n+1 => by simp [mem_replicate, Nat.succ_ne_zero]

theorem eq_of_mem_replicate {a b : α} {n} (h : b ∈ replicate n a) : b = a := (mem_replicate.1 h).2

@[simp] theorem getElem_replicate (a : α) {n : Nat} {m} (h : m < (replicate n a).length) :
    (replicate n a)[m] = a :=
  eq_of_mem_replicate (get_mem _ _ _)

@[deprecated getElem_replicate (since := "2024-06-12")]
theorem get_replicate (a : α) {n : Nat} (m : Fin _) : (replicate n a).get m = a := by
  simp

theorem eq_replicate_of_mem {a : α} :
    ∀ {l : List α}, (∀ (b) (_ : b ∈ l), b = a) → l = replicate l.length a
  | [], _ => rfl
  | b :: l, H => by
    let ⟨rfl, H₂⟩ := forall_mem_cons (l := l).1 H
    rw [length_cons, replicate, ← eq_replicate_of_mem H₂]

theorem eq_replicate {a : α} {n} {l : List α} :
    l = replicate n a ↔ length l = n ∧ ∀ (b) (_ : b ∈ l), b = a :=
  ⟨fun h => h ▸ ⟨length_replicate .., fun _ => eq_of_mem_replicate⟩,
   fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

/-! ### reverse -/

@[simp] theorem length_reverse (as : List α) : (as.reverse).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem getElem?_reverse' : ∀ {l : List α} (i j), i + j + 1 = length l →
    l.reverse[i]? = l[j]?
  | [], _, _, _ => rfl
  | a::l, i, 0, h => by simp [Nat.succ.injEq] at h; simp [h, getElem?_append_right, Nat.succ.injEq]
  | a::l, i, j+1, h => by
    have := Nat.succ.inj h; simp at this ⊢
    rw [getElem?_append, getElem?_reverse' _ _ this]
    rw [length_reverse, ← this]; apply Nat.lt_add_of_pos_right (Nat.succ_pos _)

@[deprecated getElem?_reverse' (since := "2024-06-12")]
theorem get?_reverse' {l : List α} (i j) (h : i + j + 1 = length l) : get? l.reverse i = get? l j := by
  simp [getElem?_reverse' _ _ h]

theorem getElem?_reverse {l : List α} {i} (h : i < length l) :
    l.reverse[i]? = l[l.length - 1 - i]? :=
  getElem?_reverse' _ _ <| by
    rw [Nat.add_sub_of_le (Nat.le_sub_one_of_lt h),
      Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) h)]

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

@[simp] theorem getLast?_reverse (l : List α) : l.reverse.getLast? = l.head? := by cases l <;> simp

@[simp] theorem head?_reverse (l : List α) : l.reverse.head? = l.getLast? := by
  rw [← getLast?_reverse, reverse_reverse]

@[simp] theorem reverse_append (as bs : List α) : (as ++ bs).reverse = bs.reverse ++ as.reverse := by
  induction as <;> simp_all

theorem reverse_map (f : α → β) (l : List α) : (l.map f).reverse = l.reverse.map f := by
  induction l <;> simp [*]

@[simp] theorem reverse_eq_nil_iff {xs : List α} : xs.reverse = [] ↔ xs = [] := by
  match xs with
  | [] => simp
  | x :: xs => simp

@[simp] theorem mem_reverseAux {x : α} : ∀ {as bs}, x ∈ reverseAux as bs ↔ x ∈ as ∨ x ∈ bs
  | [], _ => ⟨.inr, fun | .inr h => h⟩
  | a :: _, _ => by rw [reverseAux, mem_cons, or_assoc, or_left_comm, mem_reverseAux, mem_cons]

@[simp] theorem mem_reverse {x : α} {as : List α} : x ∈ reverse as ↔ x ∈ as := by simp [reverse]

theorem reverseAux_eq (as bs : List α) : reverseAux as bs = reverse as ++ bs :=
  reverseAux_eq_append ..

@[simp] theorem foldrM_reverse [Monad m] (l : List α) (f : α → β → m β) (b) :
    l.reverse.foldrM f b = l.foldlM (fun x y => f y x) b :=
  (foldlM_reverse ..).symm.trans <| by simp

@[simp] theorem foldl_reverse (l : List α) (f : β → α → β) (b) :
    l.reverse.foldl f b = l.foldr (fun x y => f y x) b := by simp [foldl_eq_foldlM, foldr_eq_foldrM]

@[simp] theorem foldr_reverse (l : List α) (f : α → β → β) (b) :
    l.reverse.foldr f b = l.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by simp

/-! ### elem -/

@[simp] theorem elem_cons_self [BEq α] [LawfulBEq α] {a : α} : (a::as).elem a = true := by
  simp [elem_cons]

/-! ### contains -/

@[simp] theorem contains_cons [BEq α] :
    (a :: as : List α).contains x = (a == x || as.contains x) := by
  simp only [contains, elem]
  split <;> simp_all

theorem contains_eq_any_beq [BEq α] (l : List α) (a : α) : l.contains a = l.any (· == a) := by
  induction l with simp | cons b l => cases b == a <;> simp [*]

/-! ### take and drop

Further results on `List.take` and `List.drop`, which rely on stronger automation in `Nat`,
are given in `Init.Data.List.TakeDrop`.
-/

@[simp] theorem take_append_drop : ∀ (n : Nat) (l : List α), take n l ++ drop n l = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | n+1, x :: xs => congrArg (cons x) <| take_append_drop n xs

@[simp] theorem length_drop : ∀ (i : Nat) (l : List α), length (drop i l) = length l - i
  | 0, _ => rfl
  | succ i, [] => Eq.symm (Nat.zero_sub (succ i))
  | succ i, x :: l => calc
    length (drop (succ i) (x :: l)) = length l - i := length_drop i l
    _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm

theorem drop_length_le {l : List α} (h : l.length ≤ i) : drop i l = [] :=
  length_eq_zero.1 (length_drop .. ▸ Nat.sub_eq_zero_of_le h)

theorem take_length_le {l : List α} (h : l.length ≤ i) : take i l = l := by
  have := take_append_drop i l
  rw [drop_length_le h, append_nil] at this; exact this

@[simp] theorem drop_length (l : List α) : drop l.length l = [] := drop_length_le (Nat.le_refl _)

@[simp] theorem take_length (l : List α) : take l.length l = l := take_length_le (Nat.le_refl _)

theorem take_concat_get (l : List α) (i : Nat) (h : i < l.length) :
    (l.take i).concat l[i] = l.take (i+1) :=
  Eq.symm <| (append_left_inj _).1 <| (take_append_drop (i+1) l).trans <| by
    rw [concat_eq_append, append_assoc, singleton_append, get_drop_eq_drop, take_append_drop]

theorem reverse_concat (l : List α) (a : α) : (l.concat a).reverse = a :: l.reverse := by
  rw [concat_eq_append, reverse_append]; rfl

abbrev take_succ_cons := @take_cons_succ

theorem take_all_of_le {n} {l : List α} (h : length l ≤ n) : take n l = l :=
  take_length_le h

@[simp]
theorem take_left : ∀ l₁ l₂ : List α, take (length l₁) (l₁ ++ l₂) = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congrArg (cons a) (take_left l₁ l₂)

theorem take_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left

theorem map_take (f : α → β) :
    ∀ (L : List α) (i : Nat), (L.take i).map f = (L.map f).take i
  | [], i => by simp
  | _, 0 => by simp
  | h :: t, n + 1 => by dsimp; rw [map_take f t n]

theorem getElem?_take {l : List α} {n m : Nat} (h : m < n) : (l.take n)[m]? = l[m]? := by
  induction n generalizing l m with
  | zero =>
    exact absurd h (Nat.not_lt_of_le m.zero_le)
  | succ _ hn =>
    cases l with
    | nil => simp only [take_nil]
    | cons hd tl =>
      cases m
      · simp
      · simpa using hn (Nat.lt_of_succ_lt_succ h)

@[deprecated getElem?_take (since := "2024-06-12")]
theorem get?_take {l : List α} {n m : Nat} (h : m < n) : (l.take n).get? m = l.get? m := by
  simp [getElem?_take, h]

@[simp]
theorem get?_take_of_succ {l : List α} {n : Nat} : (l.take (n + 1))[n]? = l[n]? :=
  getElem?_take (Nat.lt_succ_self n)

theorem take_succ {l : List α} {n : Nat} : l.take (n + 1) = l.take n ++ l[n]?.toList := by
  induction l generalizing n with
  | nil =>
    simp only [take_nil, Option.toList, getElem?_nil, append_nil]
  | cons hd tl hl =>
    cases n
    · simp only [take, Option.toList, getElem?_cons_zero, nil_append]
    · simp only [take, hl, getElem?_cons_succ, cons_append]

@[simp]
theorem take_eq_nil_iff {l : List α} {k : Nat} : l.take k = [] ↔ l = [] ∨ k = 0 := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]

theorem take_eq_nil_of_eq_nil : ∀ {as : List α} {i}, as = [] → as.take i = []
  | _, _, rfl => take_nil

theorem ne_nil_of_take_ne_nil {as : List α} {i : Nat} (h: as.take i ≠ []) : as ≠ [] :=
  mt take_eq_nil_of_eq_nil h

theorem dropLast_eq_take (l : List α) : l.dropLast = l.take l.length.pred := by
  cases l with
  | nil => simp [dropLast]
  | cons x l =>
    induction l generalizing x with
    | nil => simp [dropLast]
    | cons hd tl hl => simp [dropLast, hl]

@[simp]
theorem drop_eq_nil_iff_le {l : List α} {k : Nat} : l.drop k = [] ↔ l.length ≤ k := by
  refine' ⟨fun h => _, drop_eq_nil_of_le⟩
  induction k generalizing l with
  | zero =>
    simp only [drop] at h
    simp [h]
  | succ k hk =>
    cases l
    · simp
    · simp only [drop] at h
      simpa [Nat.succ_le_succ_iff] using hk h

theorem drop_sizeOf_le [SizeOf α] (l : List α) (n : Nat) : sizeOf (l.drop n) ≤ sizeOf l := by
  induction l generalizing n with
  | nil => rw [drop_nil]; apply Nat.le_refl
  | cons _ _ lih =>
    induction n with
    | zero => apply Nat.le_refl
    | succ n =>
      exact Trans.trans (lih _) (Nat.le_add_left _ _)

@[simp] theorem drop_drop (n : Nat) : ∀ (m) (l : List α), drop n (drop m l) = drop (n + m) l
  | m, [] => by simp
  | 0, l => by simp
  | m + 1, a :: l =>
    calc
      drop n (drop (m + 1) (a :: l)) = drop n (drop m l) := rfl
      _ = drop (n + m) l := drop_drop n m l
      _ = drop (n + (m + 1)) (a :: l) := rfl

theorem take_drop : ∀ (m n : Nat) (l : List α), take n (drop m l) = drop m (take (m + n) l)
  | 0, _, _ => by simp
  | _, _, [] => by simp
  | _+1, _, _ :: _ => by simpa [Nat.succ_add, take_succ_cons, drop_succ_cons] using take_drop ..

theorem map_drop (f : α → β) :
    ∀ (L : List α) (i : Nat), (L.drop i).map f = (L.map f).drop i
  | [], i => by simp
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [map_drop f t]

@[simp]
theorem getElem_cons_drop : ∀ (l : List α) (i : Nat) (h : i < l.length),
    l[i] :: drop (i + 1) l = drop i l
  | _::_, 0, _ => rfl
  | _::_, i+1, _ => getElem_cons_drop _ i _

@[deprecated getElem_cons_drop (since := "2024-06-12")]
theorem get_cons_drop (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  simp

theorem drop_eq_getElem_cons {n} {l : List α} (h) : drop n l = l[n] :: drop (n + 1) l :=
  (getElem_cons_drop _ n h).symm

@[deprecated drop_eq_getElem_cons (since := "2024-06-12")]
theorem drop_eq_get_cons {n} {l : List α} (h) : drop n l = get l ⟨n, h⟩ :: drop (n + 1) l := by
  simp [drop_eq_getElem_cons]

theorem drop_eq_nil_of_eq_nil : ∀ {as : List α} {i}, as = [] → as.drop i = []
  | _, _, rfl => drop_nil

theorem ne_nil_of_drop_ne_nil {as : List α} {i : Nat} (h: as.drop i ≠ []) : as ≠ [] :=
  mt drop_eq_nil_of_eq_nil h

@[deprecated drop_drop (since := "2024-06-15")]
theorem drop_add (m n) (l : List α) : drop (m + n) l = drop m (drop n l) := by
  simp [drop_drop]

@[simp]
theorem drop_left : ∀ l₁ l₂ : List α, drop (length l₁) (l₁ ++ l₂) = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => drop_left l₁ l₂

theorem drop_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : drop n (l₁ ++ l₂) = l₂ := by
  rw [← h]; apply drop_left

/-! ### takeWhile and dropWhile -/

theorem dropWhile_cons :
    (x :: xs : List α).dropWhile p = if p x then xs.dropWhile p else x :: xs := by
  split <;> simp_all [dropWhile]

@[simp] theorem takeWhile_append_dropWhile (p : α → Bool) :
    ∀ (l : List α), takeWhile p l ++ dropWhile p l = l
  | [] => rfl
  | x :: xs => by simp [takeWhile, dropWhile]; cases p x <;> simp [takeWhile_append_dropWhile p xs]

theorem dropWhile_append {xs ys : List α} :
    (xs ++ ys).dropWhile p =
      if (xs.dropWhile p).isEmpty then ys.dropWhile p else xs.dropWhile p ++ ys := by
  induction xs with
  | nil => simp
  | cons h t ih =>
    simp only [cons_append, dropWhile_cons]
    split <;> simp_all

/-! ### partition -/

@[simp] theorem partition_eq_filter_filter (p : α → Bool) (l : List α) :
    partition p l = (filter p l, filter (not ∘ p) l) := by simp [partition, aux] where
  aux : ∀ l {as bs}, partition.loop p l (as, bs) =
    (as.reverse ++ filter p l, bs.reverse ++ filter (not ∘ p) l)
  | [] => by simp [partition.loop, filter]
  | a :: l => by cases pa : p a <;> simp [partition.loop, pa, aux, filter, append_assoc]

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

theorem dropLast_cons_of_ne_nil {α : Type u} {x : α}
    {l : List α} (h : l ≠ []) : (x :: l).dropLast = x :: l.dropLast := by
  simp [dropLast, h]

@[simp] theorem dropLast_append_of_ne_nil {α : Type u} {l : List α} :
    ∀ (l' : List α) (_ : l ≠ []), (l' ++ l).dropLast = l' ++ l.dropLast
  | [], _ => by simp only [nil_append]
  | a :: l', h => by
    rw [cons_append, dropLast, dropLast_append_of_ne_nil l' h, cons_append]
    simp [h]

theorem dropLast_append_cons : dropLast (l₁ ++ b::l₂) = l₁ ++ dropLast (b::l₂) := by
  simp only [ne_eq, not_false_eq_true, dropLast_append_of_ne_nil]

@[simp 1100] theorem dropLast_concat : dropLast (l₁ ++ [b]) = l₁ := by simp

/-! ### isPrefixOf -/

@[simp] theorem isPrefixOf_cons₂_self [BEq α] [LawfulBEq α] {a : α} :
    isPrefixOf (a::as) (a::bs) = isPrefixOf as bs := by simp [isPrefixOf_cons₂]

/-! ### replace -/

@[simp] theorem replace_cons_self [BEq α] [LawfulBEq α] {a : α} : (a::as).replace a b = b::as := by
  simp [replace_cons]

/-! ### insert -/

section insert
variable [BEq α] [LawfulBEq α]

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

end insert

/-! ### erase -/

section erase
variable [BEq α]

@[simp] theorem erase_cons_head [LawfulBEq α] (a : α) (l : List α) : (a :: l).erase a = l := by
  simp [erase_cons]

@[simp] theorem erase_cons_tail {a b : α} (l : List α) (h : ¬(b == a)) :
    (b :: l).erase a = b :: l.erase a := by simp only [erase_cons, if_neg h]

theorem erase_of_not_mem [LawfulBEq α] {a : α} : ∀ {l : List α}, a ∉ l → l.erase a = l
  | [], _ => rfl
  | b :: l, h => by
    rw [mem_cons, not_or] at h
    simp only [erase_cons, if_neg, erase_of_not_mem h.2, beq_iff_eq, Ne.symm h.1, not_false_eq_true]

end erase

/-! ### find? -/

theorem find?_cons_of_pos (l) (h : p a) : find? p (a :: l) = some a :=
  by simp [find?, h]

theorem find?_cons_of_neg (l) (h : ¬p a) : find? p (a :: l) = find? p l :=
  by simp [find?, h]

theorem find?_eq_none : find? p l = none ↔ ∀ x ∈ l, ¬ p x := by
  induction l <;> simp [find?_cons]; split <;> simp [*]

theorem find?_some : ∀ {l}, find? p l = some a → p a
  | b :: l, H => by
    by_cases h : p b <;> simp [find?, h] at H
    · exact H ▸ h
    · exact find?_some H

@[simp] theorem mem_of_find?_eq_some : ∀ {l}, find? p l = some a → a ∈ l
  | b :: l, H => by
    by_cases h : p b <;> simp [find?, h] at H
    · exact H ▸ .head _
    · exact .tail _ (mem_of_find?_eq_some H)

/-! ### findSome? -/

theorem exists_of_findSome?_eq_some {l : List α} {f : α → Option β} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => simp_all
  | cons h l ih =>
    simp_all only [findSome?_cons, mem_cons, exists_eq_or_imp]
    split at w <;> simp_all

/-! ### lookup -/

@[simp] theorem lookup_cons_self [BEq α] [LawfulBEq α] {k : α} : ((k,b)::es).lookup k = some b := by
  simp [lookup_cons]

/-! ### any / all -/

@[simp] theorem any_eq_true {l : List α} : l.any p ↔ ∃ x, x ∈ l ∧ p x := by induction l <;> simp [*]

@[simp] theorem all_eq_true {l : List α} : l.all p ↔ ∀ x, x ∈ l →  p x := by induction l <;> simp [*]

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

/-! ### zip -/

theorem zip_map (f : α → γ) (g : β → δ) :
    ∀ (l₁ : List α) (l₂ : List β), zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (Prod.map f g)
  | [], l₂ => rfl
  | l₁, [] => by simp only [map, zip_nil_right]
  | a :: l₁, b :: l₂ => by
    simp only [map, zip_cons_cons, zip_map, Prod.map]; constructor

theorem zip_map_left (f : α → γ) (l₁ : List α) (l₂ : List β) :
    zip (l₁.map f) l₂ = (zip l₁ l₂).map (Prod.map f id) := by rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (l₁ : List α) (l₂ : List β) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by rw [← zip_map, map_id]

theorem zip_append :
    ∀ {l₁ r₁ : List α} {l₂ r₂ : List β} (_h : length l₁ = length l₂),
      zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂
  | [], r₁, l₂, r₂, h => by simp only [eq_nil_of_length_eq_zero h.symm]; rfl
  | l₁, r₁, [], r₂, h => by simp only [eq_nil_of_length_eq_zero h]; rfl
  | a :: l₁, r₁, b :: l₂, r₂, h => by
    simp only [cons_append, zip_cons_cons, zip_append (Nat.succ.inj h)]

theorem zip_map' (f : α → β) (g : α → γ) :
    ∀ l : List α, zip (l.map f) (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by simp only [map, zip_cons_cons, zip_map']

theorem of_mem_zip {a b} : ∀ {l₁ : List α} {l₂ : List β}, (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
  | _ :: l₁, _ :: l₂, h => by
    cases h
    case head => simp
    case tail h =>
    · have := of_mem_zip h
      exact ⟨Mem.tail _ this.1, Mem.tail _ this.2⟩

theorem map_fst_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length ≤ l₂.length → map Prod.fst (zip l₁ l₂) = l₁
  | [], bs, _ => rfl
  | _ :: as, _ :: bs, h => by
    simp [Nat.succ_le_succ_iff] at h
    show _ :: map Prod.fst (zip as bs) = _ :: as
    rw [map_fst_zip as bs h]
  | a :: as, [], h => by simp at h

theorem map_snd_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₂.length ≤ l₁.length → map Prod.snd (zip l₁ l₂) = l₂
  | _, [], _ => by
    rw [zip_nil_right]
    rfl
  | [], b :: bs, h => by simp at h
  | a :: as, b :: bs, h => by
    simp [Nat.succ_le_succ_iff] at h
    show _ :: map Prod.snd (zip as bs) = _ :: bs
    rw [map_snd_zip as bs h]

/-! ### zipWith -/

theorem getElem?_zipWith {f : α → β → γ} {i : Nat} :
    (List.zipWith f as bs)[i]? = match as[i]?, bs[i]? with
      | some a, some b => some (f a b) | _, _ => none := by
  induction as generalizing bs i with
  | nil => cases bs with
    | nil => simp
    | cons b bs => simp
  | cons a as aih => cases bs with
    | nil => simp
    | cons b bs => cases i <;> simp_all

@[deprecated getElem?_zipWith (since := "2024-06-12")]
theorem get?_zipWith {f : α → β → γ} :
    (List.zipWith f as bs).get? i = match as.get? i, bs.get? i with
      | some a, some b => some (f a b) | _, _ => none := by
  simp [getElem?_zipWith]

set_option linter.deprecated false in
@[deprecated getElem?_zipWith (since := "2024-06-07")] abbrev zipWith_get? := @get?_zipWith

@[simp]
theorem zipWith_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (l₁ : List α) (l₂ : List β) :
    zipWith f (l₁.map g) (l₂.map h) = zipWith (fun a b => f (g a) (h b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_map_left (l₁ : List α) (l₂ : List β) (f : α → α') (g : α' → β → γ) :
    zipWith g (l₁.map f) l₂ = zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_map_right (l₁ : List α) (l₂ : List β) (f : β → β') (g : α → β' → γ) :
    zipWith g l₁ (l₂.map f) = zipWith (fun a b => g a (f b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_foldr_eq_zip_foldr {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldr g i = (zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_foldl_eq_zip_foldl {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldl g i = (zip l₁ l₂).foldl (fun r p => g r (f p.1 p.2)) i := by
  induction l₁ generalizing i l₂ <;> cases l₂ <;> simp_all

@[simp]
theorem zipWith_eq_nil_iff {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp

theorem map_zipWith {δ : Type _} (f : α → β) (g : γ → δ → α) (l : List γ) (l' : List δ) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' := by
  induction l generalizing l' with
  | nil => simp
  | cons hd tl hl =>
    · cases l'
      · simp
      · simp [hl]

theorem zipWith_distrib_take : (zipWith f l l').take n = zipWith f (l.take n) (l'.take n) := by
  induction l generalizing l' n with
  | nil => simp
  | cons hd tl hl =>
    cases l'
    · simp
    · cases n
      · simp
      · simp [hl]

theorem zipWith_distrib_drop : (zipWith f l l').drop n = zipWith f (l.drop n) (l'.drop n) := by
  induction l generalizing l' n with
  | nil => simp
  | cons hd tl hl =>
    · cases l'
      · simp
      · cases n
        · simp
        · simp [hl]

theorem zipWith_append (f : α → β → γ) (l la : List α) (l' lb : List β)
    (h : l.length = l'.length) :
    zipWith f (l ++ la) (l' ++ lb) = zipWith f l l' ++ zipWith f la lb := by
  induction l generalizing l' with
  | nil =>
    have : l' = [] := eq_nil_of_length_eq_zero (by simpa using h.symm)
    simp [this]
  | cons hl tl ih =>
    cases l' with
    | nil => simp at h
    | cons head tail =>
      simp only [length_cons, Nat.succ.injEq] at h
      simp [ih _ h]

/-! ### zipWithAll -/

theorem getElem?_zipWithAll {f : Option α → Option β → γ} {i : Nat } :
    (zipWithAll f as bs)[i]? = match as[i]?, bs[i]? with
      | none, none => .none | a?, b? => some (f a? b?) := by
  induction as generalizing bs i with
  | nil => induction bs generalizing i with
    | nil => simp
    | cons b bs bih => cases i <;> simp_all
  | cons a as aih => cases bs with
    | nil =>
      specialize @aih []
      cases i <;> simp_all
    | cons b bs => cases i <;> simp_all

@[deprecated getElem?_zipWithAll (since := "2024-06-12")]
theorem get?_zipWithAll {f : Option α → Option β → γ} :
    (zipWithAll f as bs).get? i = match as.get? i, bs.get? i with
      | none, none => .none | a?, b? => some (f a? b?) := by
  simp [getElem?_zipWithAll]

set_option linter.deprecated false in
@[deprecated getElem?_zipWithAll (since := "2024-06-07")] abbrev zipWithAll_get? := @get?_zipWithAll

/-! ### enumFrom -/

@[simp] theorem enumFrom_length : ∀ {n} {l : List α}, (enumFrom n l).length = l.length
  | _, [] => rfl
  | _, _ :: _ => congrArg Nat.succ enumFrom_length

/-! ### enum -/

@[simp] theorem enum_length : (enum l).length = l.length :=
  enumFrom_length

theorem enum_cons : (a::as).enum = (0, a) :: as.enumFrom 1 := rfl

/-! ### minimum? -/

@[simp] theorem minimum?_nil [Min α] : ([] : List α).minimum? = none := rfl

-- We don't put `@[simp]` on `minimum?_cons`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem minimum?_cons [Min α] {xs : List α} : (x :: xs).minimum? = foldl min x xs := rfl

@[simp] theorem minimum?_eq_none_iff {xs : List α} [Min α] : xs.minimum? = none ↔ xs = [] := by
  cases xs <;> simp [minimum?]

theorem minimum?_mem [Min α] (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) :
    {xs : List α} → xs.minimum? = some a → a ∈ xs := by
  intro xs
  match xs with
  | nil => simp
  | x :: xs =>
    simp only [minimum?_cons, Option.some.injEq, List.mem_cons]
    intro eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons y xs ind =>
      simp at eq
      have p := ind _ eq
      cases p with
      | inl p =>
        cases min_eq_or x y with | _ q => simp [p, q]
      | inr p => simp [p, mem_cons]

theorem le_minimum?_iff [Min α] [LE α]
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) :
    {xs : List α} → xs.minimum? = some a → ∀ x, x ≤ a ↔ ∀ b, b ∈ xs → x ≤ b
  | nil => by simp
  | cons x xs => by
    rw [minimum?]
    intro eq y
    simp only [Option.some.injEq] at eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons z xs ih =>
      simp at eq
      simp [ih _ eq, le_min_iff, and_assoc]

-- This could be refactored by designing appropriate typeclasses to replace `le_refl`, `min_eq_or`,
-- and `le_min_iff`.
theorem minimum?_eq_some_iff [Min α] [LE α] [anti : Antisymm ((· : α) ≤ ·)]
    (le_refl : ∀ a : α, a ≤ a)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b)
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) {xs : List α} :
    xs.minimum? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  refine ⟨fun h => ⟨minimum?_mem min_eq_or h, (le_minimum?_iff le_min_iff h _).1 (le_refl _)⟩, ?_⟩
  intro ⟨h₁, h₂⟩
  cases xs with
  | nil => simp at h₁
  | cons x xs =>
    exact congrArg some <| anti.1
      ((le_minimum?_iff le_min_iff (xs := x::xs) rfl _).1 (le_refl _) _ h₁)
      (h₂ _ (minimum?_mem min_eq_or (xs := x::xs) rfl))

/-! ### maximum? -/

@[simp] theorem maximum?_nil [Max α] : ([] : List α).maximum? = none := rfl

-- We don't put `@[simp]` on `maximum?_cons`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem maximum?_cons [Max α] {xs : List α} : (x :: xs).maximum? = foldl max x xs := rfl

@[simp] theorem maximum?_eq_none_iff {xs : List α} [Max α] : xs.maximum? = none ↔ xs = [] := by
  cases xs <;> simp [maximum?]

theorem maximum?_mem [Max α] (min_eq_or : ∀ a b : α, max a b = a ∨ max a b = b) :
    {xs : List α} → xs.maximum? = some a → a ∈ xs
  | nil => by simp
  | cons x xs => by
    rw [maximum?]; rintro ⟨⟩
    induction xs generalizing x with simp at *
    | cons y xs ih =>
      rcases ih (max x y) with h | h <;> simp [h]
      simp [← or_assoc, min_eq_or x y]

theorem maximum?_le_iff [Max α] [LE α]
    (max_le_iff : ∀ a b c : α, max b c ≤ a ↔ b ≤ a ∧ c ≤ a) :
    {xs : List α} → xs.maximum? = some a → ∀ x, a ≤ x ↔ ∀ b ∈ xs, b ≤ x
  | nil => by simp
  | cons x xs => by
    rw [maximum?]; rintro ⟨⟩ y
    induction xs generalizing x with
    | nil => simp
    | cons y xs ih => simp [ih, max_le_iff, and_assoc]

-- This could be refactored by designing appropriate typeclasses to replace `le_refl`, `max_eq_or`,
-- and `le_min_iff`.
theorem maximum?_eq_some_iff [Max α] [LE α] [anti : Antisymm ((· : α) ≤ ·)]
    (le_refl : ∀ a : α, a ≤ a)
    (max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b)
    (max_le_iff : ∀ a b c : α, max b c ≤ a ↔ b ≤ a ∧ c ≤ a) {xs : List α} :
    xs.maximum? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, b ≤ a := by
  refine ⟨fun h => ⟨maximum?_mem max_eq_or h, (maximum?_le_iff max_le_iff h _).1 (le_refl _)⟩, ?_⟩
  intro ⟨h₁, h₂⟩
  cases xs with
  | nil => simp at h₁
  | cons x xs =>
    exact congrArg some <| anti.1
      (h₂ _ (maximum?_mem max_eq_or (xs := x::xs) rfl))
      ((maximum?_le_iff max_le_iff (xs := x::xs) rfl _).1 (le_refl _) _ h₁)

/-! ### mapM -/

/-- Alternate (non-tail-recursive) form of mapM for proofs. -/
def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | a :: l => return (← f a) :: (← l.mapM' f)

@[simp] theorem mapM'_nil [Monad m] {f : α → m β} : mapM' f [] = pure [] := rfl
@[simp] theorem mapM'_cons [Monad m] {f : α → m β} :
    mapM' f (a :: l) = return ((← f a) :: (← l.mapM' f)) :=
  rfl

theorem mapM'_eq_mapM [Monad m] [LawfulMonad m] (f : α → m β) (l : List α) :
    mapM' f l = mapM f l := by simp [go, mapM] where
  go : ∀ l acc, mapM.loop f l acc = return acc.reverse ++ (← mapM' f l)
    | [], acc => by simp [mapM.loop, mapM']
    | a::l, acc => by simp [go l, mapM.loop, mapM']

@[simp] theorem mapM_nil [Monad m] (f : α → m β) : [].mapM f = pure [] := rfl

@[simp] theorem mapM_cons [Monad m] [LawfulMonad m] (f : α → m β) :
    (a :: l).mapM f = (return (← f a) :: (← l.mapM f)) := by simp [← mapM'_eq_mapM, mapM']

@[simp] theorem mapM_append [Monad m] [LawfulMonad m] (f : α → m β) {l₁ l₂ : List α} :
    (l₁ ++ l₂).mapM f = (return (← l₁.mapM f) ++ (← l₂.mapM f)) := by induction l₁ <;> simp [*]

/-! ### forM -/

-- We use `List.forM` as the simp normal form, rather that `ForM.forM`.
-- As such we need to replace `List.forM_nil` and `List.forM_cons`:

@[simp] theorem forM_nil' [Monad m] : ([] : List α).forM f = (pure .unit : m PUnit) := rfl

@[simp] theorem forM_cons' [Monad m] :
    (a::as).forM f = (f a >>= fun _ => as.forM f : m PUnit) :=
  List.forM_cons _ _ _

end List
