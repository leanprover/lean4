/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
set_option new_elaborator true
/- Combinator calculus -/
namespace combinator
definition I {A : Type} (a : A) := a
definition K {A B : Type} (a : A) (b : B) := a
definition S {A B C : Type} (x : A → B → C) (y : A → B) (z : A) := x z (y z)
end combinator
