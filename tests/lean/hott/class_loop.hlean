constant (A : Type₁)
constant (hom : A → A → Type₁)
constant (id' : Πa, hom a a)

structure is_iso [class] {a b : A} (f : hom a b) :=
(inverse : hom b a)
open is_iso

set_option pp.metavar_args true
set_option pp.purify_metavars false

definition inverse_id [instance] {a : A} : is_iso (id' a) :=
is_iso.mk (id' a) (id' a)

definition inverse_is_iso [instance] {a b : A} (f : hom a b) (H : is_iso f) : is_iso (@inverse a b f H) :=
is_iso.mk (inverse f) f

constant a : A

set_option trace.class_instances true

definition foo := inverse (id' a)

set_option pp.implicit true

print definition foo
