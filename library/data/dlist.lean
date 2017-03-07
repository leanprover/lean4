/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
universes u
/--
A difference list is a function that, given a list, returns the original
contents of the difference list prepended to the given list.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure dlist (α : Type u) :=
(apply : list α → list α)
(inv   : ∀ l, apply l = apply [] ++ l)

namespace dlist
open function
variables {α : Type u}

local notation `♯`:max := by abstract {intros, rsimp}

/-- Convert a list to a dlist -/
def of_list (l : list α) : dlist α :=
⟨append l, ♯⟩

/-- Convert a dlist to a list -/
def to_list : dlist α → list α
| ⟨xs, _⟩ := xs []

/--  Create a dlist containing no elements -/
def empty : dlist α :=
⟨id, ♯⟩

local notation a `::_`:max := list.cons a

/-- Create dlist with a single element -/
def singleton (x : α) : dlist α :=
⟨x::_, ♯⟩

local attribute [simp] function.comp

/-- `O(1)` Prepend a single element to a dlist -/
def cons (x : α) : dlist α →  dlist α
| ⟨xs, h⟩ := ⟨x::_ ∘ xs, ♯⟩

/-- `O(1)` Append a single element to a dlist -/
def concat (x : α) : dlist α → dlist α
| ⟨xs, h⟩ := ⟨xs ∘ x::_, ♯⟩

/-- `O(1)` Append dlists -/
protected def append : dlist α → dlist α → dlist α
| ⟨xs, h₁⟩ ⟨ys, h₂⟩ := ⟨xs ∘ ys, ♯⟩

instance : has_append (dlist α) :=
⟨dlist.append⟩

local attribute [simp] of_list to_list empty singleton cons concat dlist.append

lemma to_list_of_list (l : list α) : to_list (of_list l) = l :=
by cases l; simp

lemma of_list_to_list (l : dlist α) : of_list (to_list l) = l :=
begin
   cases l with xs,
   assert h : append (xs []) = xs,
   {intros, apply funext, intros x, simp [inv x]},
   simp [h]
end

lemma to_list_empty : to_list (@empty α) = [] :=
by simp

lemma to_list_singleton (x : α) : to_list (singleton x) = [x] :=
by simp

lemma to_list_append (l₁ l₂ : dlist α) : to_list (l₁ ++ l₂) = to_list l₁ ++ to_list l₂ :=
show to_list (dlist.append l₁ l₂) = to_list l₁ ++ to_list l₂, from
by cases l₁; cases l₂; simp; rsimp

lemma to_list_cons (x : α) (l : dlist α) : to_list (cons x l) = x :: to_list l :=
by cases l; rsimp

lemma to_list_concat (x : α) (l : dlist α) : to_list (concat x l) = to_list l ++ [x] :=
by cases l; simp; rsimp

end dlist
