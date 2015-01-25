-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic
open eq
definition refl := @eq.refl

definition transport {A : Type} {a b : A} {P : A → Type} (p : a = b) (H : P a) : P b
:= eq.rec H p

theorem transport_refl {A : Type} {a : A} {P : A → Type} (H : P a) : transport (refl a) H = H
:= refl H

attribute transport [irreducible]
theorem transport_proof_irrel {A : Type} {a b : A} {P : A → Type} (p1 p2 : a = b) (H : P a) : transport p1 H = transport p2 H
:= refl (transport p1 H)

theorem transport_eq {A : Type} {a : A} {P : A → Type} (p : a = a) (H : P a) : transport p H = H
:= calc transport p H = transport (refl a) H : transport_proof_irrel p (refl a) H
                 ...  = H                    : transport_refl H

theorem dcongr {A : Type} {B : A → Type} {a b : A} (f : Π x, B x) (p : a = b) : transport p (f a) = f b
:= have H1 : ∀ p1 : a = a, transport p1 (f a) = f a, from
     assume p1 : a = a, transport_eq p1 (f a),
   eq.rec H1 p p

theorem transport_trans {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p, calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                          ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq.rec H1 p2 p2
