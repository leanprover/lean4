/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro, Markus Himmel
-/
module

prelude
public import Init.Data.List.SplitOn.Basic
import all Init.Data.List.SplitOn.Basic
import Init.Data.List.Nat.Modify
import Init.ByCases

public section

namespace List

variable {p : α → Bool} {xs : List α} {ls : List (List α)}

@[simp]
theorem splitOn_nil [BEq α] (a : α) : [].splitOn a = [[]] :=
  (rfl)

@[simp]
theorem splitOnP_nil : [].splitOnP p = [[]] :=
  (rfl)

@[simp]
theorem splitOnPPrepend_ne_nil (p : α → Bool) (xs acc : List α) : splitOnPPrepend p xs acc ≠ [] := by
  fun_induction splitOnPPrepend <;> simp_all

@[deprecated splitOnPPrepend_ne_nil (since := "2026-02-26")]
theorem splitOnP.go_ne_nil (p : α → Bool) (xs acc : List α) : splitOnPPrepend p xs acc ≠ [] :=
  splitOnPPrepend_ne_nil p xs acc

@[simp] theorem splitOnPPrepend_nil {acc : List α} : splitOnPPrepend p [] acc = [acc.reverse] := (rfl)
@[simp] theorem splitOnPPrepend_nil_right : splitOnPPrepend p xs [] = splitOnP p xs := (rfl)
theorem splitOnP_eq_splitOnPPrepend : splitOnP p xs = splitOnPPrepend p xs [] := (rfl)

theorem splitOnPPrepend_cons_eq_if {x : α} {xs acc : List α} :
    splitOnPPrepend p (x :: xs) acc =
      if p x then acc.reverse :: splitOnP p xs else splitOnPPrepend p xs (x :: acc) := by
  simp [splitOnPPrepend]

theorem splitOnPPrepend_cons_pos {p : α → Bool} {a : α} {l acc : List α} (h : p a) :
    splitOnPPrepend p (a :: l) acc = acc.reverse :: splitOnP p l := by
  simp [splitOnPPrepend, h]

theorem splitOnPPrepend_cons_neg {p : α → Bool} {a : α} {l acc : List α} (h : p a = false) :
    splitOnPPrepend p (a :: l) acc = splitOnPPrepend p l (a :: acc) := by
  simp [splitOnPPrepend, h]

theorem splitOnP_cons_eq_if_splitOnPPrepend {x : α} {xs : List α} :
    splitOnP p (x :: xs) = if p x then [] :: splitOnP p xs else splitOnPPrepend p xs [x] := by
  simp [splitOnPPrepend_cons_eq_if, ← splitOnPPrepend_nil_right]

theorem splitOnPPrepend_eq_modifyHead {xs acc : List α} :
    splitOnPPrepend p xs acc = modifyHead (acc.reverse ++ ·) (splitOnP p xs) := by
  induction xs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp [splitOnPPrepend_cons_eq_if, splitOnP_cons_eq_if_splitOnPPrepend, ih]
    split <;> simp <;> congr

@[deprecated splitOnPPrepend_eq_modifyHead (since := "2026-02-26")]
theorem splitOnP.go_acc {xs acc : List α} :
    splitOnPPrepend p xs acc = modifyHead (acc.reverse ++ ·) (splitOnP p xs) :=
  splitOnPPrepend_eq_modifyHead

@[simp]
theorem splitOnP_ne_nil (p : α → Bool) (xs : List α) : xs.splitOnP p ≠ [] :=
  splitOnPPrepend_ne_nil p xs []

theorem splitOnP_cons_eq_if_modifyHead (x : α) (xs : List α) :
    (x :: xs).splitOnP p =
      if p x then [] :: xs.splitOnP p else (xs.splitOnP p).modifyHead (cons x) := by
  simp [splitOnP_cons_eq_if_splitOnPPrepend, splitOnPPrepend_eq_modifyHead]

@[deprecated splitOnP_cons_eq_if_modifyHead (since := "2026-02-26")]
theorem splitOnP_cons (x : α) (xs : List α) :
    (x :: xs).splitOnP p =
      if p x then [] :: xs.splitOnP p else (xs.splitOnP p).modifyHead (cons x) :=
  splitOnP_cons_eq_if_modifyHead x xs

/-- The original list `L` can be recovered by flattening the lists produced by `splitOnP p L`,
interspersed with the elements `L.filter p`. -/
theorem splitOnP_spec (as : List α) :
    flatten (zipWith (· ++ ·) (splitOnP p as) (((as.filter p).map fun x => [x]) ++ [[]])) = as := by
  induction as with
  | nil => simp
  | cons a as' ih =>
    rw [splitOnP_cons_eq_if_modifyHead]
    split <;> simp [*, flatten_zipWith, splitOnP_ne_nil]
where
  flatten_zipWith {xs ys : List (List α)} {a : α} (hxs : xs ≠ []) (hys : ys ≠ []) :
      flatten (zipWith (fun x x_1 => x ++ x_1) (modifyHead (cons a) xs) ys) =
        a :: flatten (zipWith (fun x x_1 => x ++ x_1) xs ys) := by
    cases xs <;> cases ys <;> simp_all

/-- If no element satisfies `p` in the list `xs`, then `xs.splitOnP p = [xs]` -/
theorem splitOnP_eq_singleton (h : ∀ x ∈ xs, p x = false) : xs.splitOnP p = [xs] := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [mem_cons, forall_eq_or_imp] at h
    simp [splitOnP_cons_eq_if_modifyHead, h.1, ih h.2]

@[deprecated splitOnP_eq_singleton (since := "2026-02-26")]
theorem splitOnP_eq_single (h : ∀ x ∈ xs, p x = false) : xs.splitOnP p = [xs] :=
  splitOnP_eq_singleton h

/-- When a list of the form `[...xs, sep, ...as]` is split at the `sep` element satisfying `p`,
the result is the concatenation of `splitOnP` called on `xs` and `as` -/
theorem splitOnP_append_cons (xs as : List α) {sep : α} (hsep : p sep) :
    (xs ++ sep :: as).splitOnP p = List.splitOnP p xs ++ List.splitOnP p as := by
  induction xs with
  | nil => simp [splitOnP_cons_eq_if_modifyHead, hsep]
  | cons hd tl ih =>
    obtain ⟨hd1, tl1, h1'⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (p := p) (xs := tl))
    by_cases hPh : p hd <;> simp [splitOnP_cons_eq_if_modifyHead, *]

/-- When a list of the form `[...xs, sep, ...as]` is split on `p`, the first element is `xs`,
  assuming no element in `xs` satisfies `p` but `sep` does satisfy `p` -/
theorem splitOnP_append_cons_of_forall_mem (h : ∀ x ∈ xs, p x = false) (sep : α)
    (hsep : p sep = true) (as : List α) : (xs ++ sep :: as).splitOnP p = xs :: as.splitOnP p := by
  rw [splitOnP_append_cons xs as hsep, splitOnP_eq_singleton h, singleton_append]

@[deprecated splitOnP_append_cons_of_forall_mem (since := "2026-02-26")]
theorem splitOnP_first (h : ∀ x ∈ xs, p x = false) (sep : α)
    (hsep : p sep = true) (as : List α) : (xs ++ sep :: as).splitOnP p = xs :: as.splitOnP p :=
  splitOnP_append_cons_of_forall_mem h sep hsep as

theorem splitOn_eq_splitOnP [BEq α] {x : α} {xs : List α} : xs.splitOn x = xs.splitOnP (· == x) :=
  (rfl)

@[simp]
theorem splitOn_ne_nil [BEq α] (a : α) (xs : List α) : xs.splitOn a ≠ [] := by
  simp [splitOn_eq_splitOnP]

theorem splitOn_cons_eq_if_modifyHead [BEq α] {a : α} (x : α) (xs : List α) :
    (x :: xs).splitOn a =
      if x == a then [] :: xs.splitOn a else (xs.splitOn a).modifyHead (cons x) := by
  simpa [splitOn_eq_splitOnP] using splitOnP_cons_eq_if_modifyHead ..

/-- If no element satisfies `p` in the list `xs`, then `xs.splitOnP p = [xs]` -/
theorem splitOn_eq_singleton_of_beq_eq_false [BEq α] {a : α} (h : ∀ x ∈ xs, (x == a) = false) :
    xs.splitOn a = [xs] := by
  simpa [splitOn_eq_splitOnP] using splitOnP_eq_singleton h

theorem splitOn_eq_singleton [BEq α] [LawfulBEq α] {a : α} (h : a ∉ xs) :
    xs.splitOn a = [xs] :=
  splitOn_eq_singleton_of_beq_eq_false
    (fun _ hb => beq_eq_false_iff_ne.2 (fun hab => absurd hb (hab ▸ h)))

/-- When a list of the form `[...xs, sep, ...as]` is split at the `sep` element equal to `a`,
the result is the concatenation of `splitOnP` called on `xs` and `as` -/
theorem splitOn_append_cons_of_beq [BEq α] {a : α} (xs as : List α) {sep : α} (hsep : sep == a) :
    (xs ++ sep :: as).splitOn a = List.splitOn a xs ++ List.splitOn a as := by
  simpa [splitOn_eq_splitOnP] using splitOnP_append_cons (p := (· == a)) _ _ hsep

/-- When a list of the form `[...xs, sep, ...as]` is split at `a`,
the result is the concatenation of `splitOnP` called on `xs` and `as` -/
theorem splitOn_append_cons_self [BEq α] [ReflBEq α] {a : α} (xs as : List α) :
    (xs ++ a :: as).splitOn a = List.splitOn a xs ++ List.splitOn a as :=
  splitOn_append_cons_of_beq _ _ (BEq.refl _)

/-- When a list of the form `[...xs, sep, ...as]` is split at `a`, the first element is `xs`,
  assuming no element in `xs` is equal to `a` but `sep` is equal to `a`. -/
theorem splitOn_append_cons_of_forall_mem_beq_eq_false [BEq α] {a : α}
    (h : ∀ x ∈ xs, (x == a) = false) (sep : α)
    (hsep : sep == a) (as : List α) : (xs ++ sep :: as).splitOn a = xs :: as.splitOn a := by
  simpa [splitOn_eq_splitOnP] using splitOnP_append_cons_of_forall_mem h _ hsep _

/-- When a list of the form `[...xs, a, ...as]` is split at `a`, the first element is `xs`,
  assuming no element in `xs` is equal to `a`. -/
theorem splitOn_append_cons_self_of_not_mem [BEq α] [LawfulBEq α] {a : α}
    (h : a ∉ xs) (as : List α) : (xs ++ a :: as).splitOn a = xs :: as.splitOn a :=
  splitOn_append_cons_of_forall_mem_beq_eq_false
    (fun b hb => beq_eq_false_iff_ne.2 fun hab => absurd hb (hab ▸ h)) _ (by simp) _

/-- `intercalate [x]` is the left inverse of `splitOn x` -/
@[simp]
theorem intercalate_splitOn [BEq α] [LawfulBEq α] (x : α) : [x].intercalate (xs.splitOn x) = xs := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    simp only [splitOn_cons_eq_if_modifyHead, beq_iff_eq]
    split
    · simp_all [intercalate_cons_of_ne_nil, splitOn_ne_nil]
    · have hsp := splitOn_ne_nil x tl
      generalize splitOn x tl = ls at *
      cases ls <;> simp_all

/-- `splitOn x` is the left inverse of `intercalate [x]`, on the domain
consisting of each nonempty list of lists `ls` whose elements do not contain `x` -/
theorem splitOn_intercalate [BEq α] [LawfulBEq α] (x : α) (hx : ∀ l ∈ ls, x ∉ l) (hls : ls ≠ []) :
    ([x].intercalate ls).splitOn x = ls := by
  induction ls with
  | nil => simp at hls
  | cons hd tl ih =>
    simp only [mem_cons, forall_eq_or_imp] at ⊢ hx
    match tl with
    | [] => simpa using splitOn_eq_singleton hx.1
    | t::tl =>
      simp only [intercalate_cons_cons, append_assoc, cons_append, nil_append]
      rw [splitOn_append_cons_self_of_not_mem hx.1, ih hx.2 (by simp)]

end List
