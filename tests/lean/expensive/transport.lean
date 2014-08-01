-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

namespace N1
definition transport {A : Type} {a b : A} {P : A → Type} (p : a = b) (H : P a) : P b
:= eq_rec H p

theorem transport_refl {A : Type} {a : A} {P : A → Type} (H : P a) : transport (refl a) H = H
:= refl H

opaque_hint (hiding transport)
theorem transport_proof_irrel {A : Type} {a b : A} {P : A → Type} (p1 p2 : a = b) (H : P a) : transport p1 H = transport p2 H
:= refl (transport p1 H)

theorem transport_eq {A : Type} {a : A} {P : A → Type} (p : a = a) (H : P a) : transport p H = H
:= calc transport p H = transport (refl a) H : transport_proof_irrel p (refl a) H
                 ...  = H                    : transport_refl H

theorem dcongr {A : Type} {B : A → Type} {a b : A} (f : Π x, B x) (p : a = b) : transport p (f a) = f b
:= have H1 : ∀ p1 : a = a, transport p1 (f a) = f a, from
     assume p1 : a = a, transport_eq p1 (f a),
   eq_rec H1 p p

theorem transport_trans {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p, calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                          ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans1 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans2 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans3 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans4 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans5 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans6 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans7 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans8 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans9 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans10 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans11 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans12 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans13 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans14 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans15 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans16 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans17 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans18 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans19 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans20 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans21 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans22 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans23 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans24 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans25 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans26 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans27 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans28 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans29 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p, calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                          ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans30 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans31 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans32 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans33 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans34 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans35 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans36 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans37 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans38 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans39 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans40 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans41 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans42 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans43 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans44 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans45 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans46 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans47 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans48 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans49 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans50 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans51 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans52 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans53 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans54 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans55 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans56 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans57 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans58 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2
end

namespace N2
definition transport {A : Type} {a b : A} {P : A → Type} (p : a = b) (H : P a) : P b
:= eq_rec H p

theorem transport_refl {A : Type} {a : A} {P : A → Type} (H : P a) : transport (refl a) H = H
:= refl H

opaque_hint (hiding transport)
theorem transport_proof_irrel {A : Type} {a b : A} {P : A → Type} (p1 p2 : a = b) (H : P a) : transport p1 H = transport p2 H
:= refl (transport p1 H)

theorem transport_eq {A : Type} {a : A} {P : A → Type} (p : a = a) (H : P a) : transport p H = H
:= calc transport p H = transport (refl a) H : transport_proof_irrel p (refl a) H
                 ...  = H                    : transport_refl H

theorem dcongr {A : Type} {B : A → Type} {a b : A} (f : Π x, B x) (p : a = b) : transport p (f a) = f b
:= have H1 : ∀ p1 : a = a, transport p1 (f a) = f a, from
     assume p1 : a = a, transport_eq p1 (f a),
   eq_rec H1 p p

theorem transport_trans {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p, calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                          ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans1 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans2 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans3 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans4 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans5 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans6 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans7 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans8 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans9 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans10 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans11 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans12 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans13 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans14 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans15 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans16 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans17 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans18 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans19 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans20 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans21 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans22 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans23 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans24 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans25 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans26 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans27 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans28 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans29 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p, calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                          ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans30 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans31 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans32 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans33 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans34 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans35 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans36 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans37 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans38 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans39 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans40 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans41 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans42 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans43 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans44 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans45 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans46 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans47 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans48 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans49 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans50 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans51 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans52 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans53 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans54 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans55 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans56 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans57 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2

theorem transport_trans58 {A : Type} {a b c : A} {P : A → Type} (p1 : a = b) (p2 : b = c) (H : P a) :
                       transport p1 (transport p2 H) = transport (trans p1 p2) H
:= have H1 : ∀ p : b = b, transport p1 (transport p H) = transport (trans p1 p) H, from
     take p : b = b,
       calc transport p1 (transport p H) = transport p1 H           : {transport_eq p H}
                                    ...  = transport (trans p1 p) H : refl (transport p1 H),
   eq_rec H1 p2 p2
end