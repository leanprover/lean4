-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
definition pair {A : (Type U)} {B : (Type U)} (a : A) (b : B) := tuple a, b
theorem    pair_inj1 {A : (Type U)} {B : A → (Type U)} {a b : sig x, B x} (H : a = b) : proj1 a = proj1 b
:= subst (refl (proj1 a)) H
theorem    pair_inj2 {A B : (Type U)} {a b : A # B} (H : a = b) : proj2 a = proj2 b
:= subst (refl (proj2 a)) H
theorem    pairext_proj {A B : (Type U)} {p : A # B} {a : A} {b : B} (H1 : proj1 p = a) (H2 : proj2 p = b) : p = (pair a b)
:= @pairext A (λ x, B) p (pair a b) H1 (to_heq H2)
