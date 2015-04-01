/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
prelude
import init.relation

structure setoid [class] (A : Type) :=
(r : A → A → Prop) (iseqv : equivalence r)

namespace setoid
  infix `≈` := setoid.r

  variable {A : Type}
  variable [s : setoid A]
  include s

  theorem refl (a : A) : a ≈ a :=
  and.elim_left (@setoid.iseqv A s) a

  theorem symm {a b : A} : a ≈ b → b ≈ a :=
  λ H, and.elim_left (and.elim_right (@setoid.iseqv A s)) a b H

  theorem trans {a b c : A} : a ≈ b → b ≈ c → a ≈ c :=
  λ H₁ H₂, and.elim_right (and.elim_right (@setoid.iseqv A s)) a b c H₁ H₂
end setoid
