/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.nat
open decidable list
set_option new_elaborator true

universe variables u v

attribute [instance]
protected definition list.is_inhabited (A : Type u) : inhabited (list A) :=
inhabited.mk list.nil

notation h :: t  := cons h t
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

namespace list
variable {A : Type u}

definition append : list A → list A → list A
| []       l := l
| (h :: s) t := h :: (append s t)

definition length : list A → nat
| []       := 0
| (a :: l) := length l + 1

open option nat

definition nth : list A → nat → option A
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

definition head [inhabited A] : list A → A
| []       := default A
| (a :: l) := a

definition tail : list A → list A
| []       := []
| (a :: l) := l

definition concat : Π (x : A), list A → list A
| a []       := [a]
| a (b :: l) := b :: concat a l

definition reverse : list A → list A
| []       := []
| (a :: l) := concat a (reverse l)

definition map {B : Type v} (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: map l

definition join : list (list A) → list A
| []        := []
| (l :: ls) := append l (join ls)

definition filter (p : A → Prop) [h : decidable_pred p] : list A → list A
| []     := []
| (a::l) := if p a then a :: filter l else filter l

definition dropn : ℕ → list A → list A
| 0 a := a
| (succ n) [] := []
| (succ n) (x::r) := dropn n r
end list

attribute [instance]
definition list_has_append {A : Type u} : has_append (list A) :=
has_append.mk list.append
