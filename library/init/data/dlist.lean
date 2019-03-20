/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.List.basic init.Function
universes u
/--
A difference List is a Function that, given a List, returns the original
contents of the difference List prepended to the given List.
This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure Dlist (α : Type u) :=
(apply     : List α → List α)
(invariant : ∀ l, apply l = apply [] ++ l)

namespace Dlist
variables {α : Type u}
open List

def ofList (l : List α) : Dlist α :=
⟨append l, λ t, (appendNil l).symm ▸ rfl⟩

def Empty : Dlist α :=
⟨id, λ t, rfl⟩

def toList : Dlist α → List α
| ⟨f, h⟩ := f []

def singleton (a : α) : Dlist α :=
⟨λ t, a :: t, λ t, rfl⟩

def cons : α → Dlist α → Dlist α
| a ⟨f, h⟩ := ⟨λ t, a :: f t, λ t,
               show a :: f t = a :: f [] ++ t, from
               have h₁ : a :: f t = a :: (f nil ++ t), from h t ▸ rfl,
               have h₂ : a :: (f nil ++ t) = a :: f nil ++ t, from (consAppend _ _ _).symm,
               Eq.trans h₁ h₂⟩

def append : Dlist α → Dlist α → Dlist α
| ⟨f, h₁⟩ ⟨g, h₂⟩ := ⟨f ∘ g, λ t,
                      show f (g t) = (f (g [])) ++ t, from
                      (h₁ (g [])).symm ▸ (appendAssoc (f []) (g []) t).symm ▸ h₂ t ▸ h₁ (g t) ▸ rfl⟩

def push : Dlist α → α → Dlist α
| ⟨f, h⟩ a := ⟨λ t, f (a :: t), λ t, (h (a::t)).symm ▸ (h [a]).symm ▸ (appendAssoc (f []) [a] t).symm ▸ rfl⟩

instance : HasAppend (Dlist α) :=
⟨Dlist.append⟩

end Dlist
