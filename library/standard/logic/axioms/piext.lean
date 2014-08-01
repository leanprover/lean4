----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.classes.inhabited logic.connectives.cast

-- Pi extensionality
axiom piext {A : Type} {B B' : A → Type} {H : inhabited (Π x, B x)} :
  (Π x, B x) = (Π x, B' x) → B = B'

theorem cast_app {A : Type} {B B' : A → Type} (H : (Π x, B x) = (Π x, B' x)) (f : Π x, B x)
  (a : A) : cast H f a == f a :=
have Hi [fact] : inhabited (Π x, B x), from inhabited_intro f,
have Hb : B = B', from piext H,
cast_app' Hb f a

theorem hcongr1 {A : Type} {B B' : A → Type} {f : Π x, B x} {f' : Π x, B' x} (a : A)
  (H : f == f') : f a == f' a :=
have Hi [fact] : inhabited (Π x, B x), from inhabited_intro f,
have Hb : B = B', from piext (type_eq H),
hcongr1' a H Hb

theorem hcongr {A A' : Type} {B : A → Type} {B' : A' → Type}
    {f : Π x, B x} {f' : Π x, B' x} {a : A} {a' : A'}
    (Hff' : f == f') (Haa' : a == a') : f a == f' a' :=
have H1 : ∀ (B B' : A → Type) (f : Π x, B x) (f' : Π x, B' x), f == f' → f a == f' a, from
  take B B' f f' e, hcongr1 a e,
have H2 : ∀ (B : A → Type) (B' : A' → Type) (f : Π x, B x) (f' : Π x, B' x),
    f == f' → f a == f' a', from hsubst Haa' H1,
H2 B B' f f' Hff'
