/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.pointed
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

open core is_trunc

structure pointed [class] (A : Type) :=
  (point : A)

namespace pointed
  variables {A B : Type}
  definition pt [H : pointed A] := point A

  -- Any contractible type is pointed
  definition pointed_of_is_contr [instance] (A : Type) [H : is_contr A] : pointed A :=
  pointed.mk !center

  -- A pi type with a pointed target is pointed
  definition pointed_pi [instance] (P : A → Type) [H : Πx, pointed (P x)]
      : pointed (Πx, P x) :=
  pointed.mk (λx, pt)

  -- A sigma type of pointed components is pointed
  definition pointed_sigma [instance] (P : A → Type) [G : pointed A]
      [H : pointed (P pt)] : pointed (Σx, P x) :=
  pointed.mk ⟨pt,pt⟩

  definition pointed_prod [instance] (A B : Type) [H1 : pointed A] [H2 : pointed B]
      : pointed (A × B) :=
  pointed.mk (pt,pt)

  definition pointed_loop [instance] (a : A) : pointed (a = a) :=
  pointed.mk idp

  definition pointed_fun_closed (f : A → B) [H : pointed A] : pointed B :=
  pointed.mk (f pt)

end pointed

structure Pointed :=
  {carrier : Type}
  (Point   : carrier)

open pointed Pointed

namespace Pointed
  attribute carrier [coercion]
  protected definition mk' (A : Type) [H : pointed A] : Pointed := Pointed.mk (point A)
  definition pointed_carrier [instance] (A : Pointed) : pointed (carrier A) :=
  pointed.mk (Point A)

  definition Loop_space [reducible] (A : Pointed) : Pointed :=
  Pointed.mk' (point A = point A)

  definition Iterated_loop_space (A : Pointed) (n : ℕ) : Pointed :=
  nat.rec_on n A (λn X, Loop_space X)

  prefix `Ω`:95 := Loop_space
  notation `Ω[`:95 n:0 `]`:0 A:95 := Iterated_loop_space A n

end Pointed

namespace pointed
  export Pointed (hiding cases_on destruct mk)
  abbreviation Cases_on := @Pointed.cases_on
  abbreviation Destruct := @Pointed.destruct
  abbreviation Mk := @Pointed.mk

  definition iterated_loop_space (A : Type) [H : pointed A] (n : ℕ) : Type :=
  carrier (Iterated_loop_space (Pointed.mk' A) n)

end pointed
