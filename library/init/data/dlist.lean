/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic init.function
universes u
/--
A difference list is a function that, given a list, returns the original
contents of the difference list prepended to the given list.
This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure dlist (α : Type u) :=
(apply     : list α → list α)
(invariant : ∀ l, apply l = apply [] ++ l)

namespace dlist
variables {α : Type u}
open list

def of_list (l : list α) : dlist α :=
⟨append l, λ t, (append_nil l).symm ▸ rfl⟩

def empty : dlist α :=
⟨id, λ t, rfl⟩

def to_list : dlist α → list α
| ⟨f, h⟩ := f []

def singleton (a : α) : dlist α :=
⟨λ t, a :: t, λ t, rfl⟩

def cons : α → dlist α → dlist α
| a ⟨f, h⟩ := ⟨λ t, a :: f t, λ t,
               show a :: f t = a :: f [] ++ t, from
               have h₁ : a :: f t = a :: (f nil ++ t), from h t ▸ rfl,
               have h₂ : a :: (f nil ++ t) = a :: f nil ++ t, from (cons_append _ _ _).symm,
               eq.trans h₁ h₂⟩

def append : dlist α → dlist α → dlist α
| ⟨f, h₁⟩ ⟨g, h₂⟩ := ⟨f ∘ g, λ t,
                      show f (g t) = (f (g [])) ++ t, from
                      (h₁ (g [])).symm ▸ (append_assoc (f []) (g []) t).symm ▸ h₂ t ▸ h₁ (g t) ▸ rfl⟩

def push : dlist α → α → dlist α
| ⟨f, h⟩ a := ⟨λ t, f (a :: t), λ t, (h (a::t)).symm ▸ (h [a]).symm ▸ (append_assoc (f []) [a] t).symm ▸ rfl⟩

instance : has_append (dlist α) :=
⟨dlist.append⟩

end dlist
