/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.nat
open decidable list

universe variables u v

instance (A : Type u) : inhabited (list A) :=
⟨list.nil⟩

notation h :: t  := cons h t
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

namespace list
variables {A : Type u} {B : Type v}

def append : list A → list A → list A
| []       l := l
| (h :: s) t := h :: (append s t)

def length : list A → nat
| []       := 0
| (a :: l) := length l + 1

open option nat

def nth : list A → nat → option A
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

def head [inhabited A] : list A → A
| []       := default A
| (a :: l) := a

def tail : list A → list A
| []       := []
| (a :: l) := l

def concat : Π (x : A), list A → list A
| a []       := [a]
| a (b :: l) := b :: concat a l

def reverse : list A → list A
| []       := []
| (a :: l) := concat a (reverse l)

def map (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: map l

def for : list A → (A → B) → list B :=
flip map

def join : list (list A) → list A
| []        := []
| (l :: ls) := append l (join ls)

def filter (p : A → Prop) [h : decidable_pred p] : list A → list A
| []     := []
| (a::l) := if p a then a :: filter l else filter l

def dropn : ℕ → list A → list A
| 0 a := a
| (succ n) [] := []
| (succ n) (x::r) := dropn n r
end list

instance {A : Type u} : has_append (list A) :=
⟨list.append⟩
