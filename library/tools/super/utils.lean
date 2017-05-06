/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
open tactic expr list

meta def get_metas : expr → list expr
| (var _) := []
| (sort _) := []
| (const _ _) := []
| (mvar n t) := expr.mvar n t :: get_metas t
| (local_const _ _ _ t) := get_metas t
| (app a b) := get_metas a ++ get_metas b
| (lam _ _ d b) := get_metas d ++ get_metas b
| (pi _ _ d b) := get_metas d ++ get_metas b
| (elet _ t v b) := get_metas t ++ get_metas v ++ get_metas b
| (macro _ _) := []

meta def get_meta_type : expr → expr
| (mvar _ t) := t
| _ := mk_var 0

-- TODO(gabriel): think about how to handle the avalanche of implicit arguments
meta def expr_size : expr → nat
| (var _) := 1
| (sort _) := 1
| (const _ _) := 1
| (mvar n t) := 1
| (local_const _ _ _ _) := 1
| (app a b) := expr_size a + expr_size b
| (lam _ _ d b) := 1 + expr_size b
| (pi _ _ d b) := 1 + expr_size b
| (elet _ t v b) := 1 + expr_size v + expr_size b
| (macro _ _) := 1

namespace ordering

def is_lt {A} [has_ordering A] (x y : A) : bool :=
match has_ordering.cmp x y with ordering.lt := tt | _ := ff end

end ordering

namespace list

meta def nub {A} [has_ordering A] (l : list A) : list A :=
rb_map.keys (rb_map.set_of_list l)

meta def nub_on {A B} [has_ordering B] (f : A → B) (l : list A) : list A :=
rb_map.values (rb_map.of_list (map (λx, (f x, x)) l))

def nub_on' {A B} [decidable_eq B] (f : A → B) : list A → list A
| [] := []
| (x::xs) := x :: filter (λy, f x ≠ f y) (nub_on' xs)

def for_all {A} (l : list A) (p : A → Prop) [decidable_pred p] : bool :=
list.all l (λx, to_bool (p x))

def exists_ {A} (l : list A) (p : A → Prop) [decidable_pred p] : bool :=
list.any l (λx, to_bool (p x))

def subset_of {A} [decidable_eq A] (xs ys : list A) :=
xs.for_all (λx, x ∈ ys)

def filter_maximal {A} (gt : A → A → bool) (l : list A) : list A :=
filter (λx, l.for_all (λy, ¬gt y x)) l

private def zip_with_index' {A} : ℕ → list A → list (A × ℕ)
| _ nil := nil
| i (x::xs) := (x,i) :: zip_with_index' (i+1) xs

def zip_with_index {A} : list A → list (A × ℕ) :=
zip_with_index' 0

meta def merge_sorted {A} [has_ordering A] : list A → list A → list A
| [] ys := ys
| xs [] := xs
| (x::xs) (y::ys) :=
  if ordering.is_lt x y then
    x :: merge_sorted xs (y::ys)
  else
    y :: merge_sorted (x::xs) ys

meta def sort {A} [has_ordering A] : list A → list A
| (x::xs) :=
  let (smaller, greater_eq) := partition (λy, ordering.is_lt y x) xs in
  merge_sorted (sort smaller) (x :: sort greater_eq)
| [] := []

meta def sort_on {A B} (f : A → B) [has_ordering B] : list A → list A :=
@sort _ ⟨λx y, has_ordering.cmp (f x) (f y)⟩

end list

meta def name_of_funsym : expr → name
| (local_const uniq _ _ _) := uniq
| (const n _) := n
| _ := name.anonymous

private meta def contained_funsyms' : expr → rb_map name expr → rb_map name expr
| (var _) m := m
| (sort _) m := m
| (const n ls) m := rb_map.insert m n (const n ls)
| (mvar _ t) m := contained_funsyms' t m
| (local_const uniq pp bi t) m := rb_map.insert m uniq (local_const uniq pp bi t)
| (app a b) m := contained_funsyms' a (contained_funsyms' b m)
| (lam _ _ d b) m := contained_funsyms' d (contained_funsyms' b m)
| (pi _ _ d b) m := contained_funsyms' d (contained_funsyms' b m)
| (elet _ t v b) m := contained_funsyms' t (contained_funsyms' v (contained_funsyms' b m))
| (macro _ _) m := m

meta def contained_funsyms (e : expr) : rb_map name expr :=
contained_funsyms' e (rb_map.mk name expr)

private meta def contained_lconsts' : expr → rb_map name expr → rb_map name expr
| (var _) m := m
| (sort _) m := m
| (const _ _) m := m
| (mvar _ t) m := contained_lconsts' t m
| (local_const uniq pp bi t) m := contained_lconsts' t (rb_map.insert m uniq (local_const uniq pp bi t))
| (app a b) m := contained_lconsts' a (contained_lconsts' b m)
| (lam _ _ d b) m := contained_lconsts' d (contained_lconsts' b m)
| (pi _ _ d b) m := contained_lconsts' d (contained_lconsts' b m)
| (elet _ t v b) m := contained_lconsts' t (contained_lconsts' v (contained_lconsts' b m))
| (macro _ _) m := m

meta def contained_lconsts (e : expr) : rb_map name expr :=
contained_lconsts' e (rb_map.mk name expr)

meta def contained_lconsts_list (es : list expr) : rb_map name expr :=
es.foldl (λlcs e, contained_lconsts' e lcs) (rb_map.mk name expr)

namespace tactic

meta def infer_univ (type : expr) : tactic level :=
do sort_of_type ← infer_type type >>= whnf,
match sort_of_type with
| sort lvl := return lvl
| not_sort := do fmt ← pp not_sort,
                 fail $ to_fmt "cannot get universe level of sort: " ++ fmt
end

end tactic

namespace nat

def min (m n : ℕ) := if m < n then m else n
def max (m n : ℕ) := if m > n then m else n

end nat
