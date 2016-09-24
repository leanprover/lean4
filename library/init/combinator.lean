/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
/- Combinator calculus -/
namespace combinator
universe variables u₁ u₂ u₃
def I {A : Type u₁} (a : A) := a
def K {A : Type u₁} {B : Type u₂} (a : A) (b : B) := a
def S {A : Type u₁} {B : Type u₂} {C : Type u₃} (x : A → B → C) (y : A → B) (z : A) := x z (y z)
end combinator
