set_option pp.notation false

inductive [class] C (A : Type*)
| mk : A → C

definition val {A : Type*} (c : C A) : A :=
C.rec (λa, a) c

constant magic (A : Type*) : A
attribute [instance, priority std.priority.max]
noncomputable definition C_magic (A : Type*) : C A :=
C.mk (magic A)

attribute [instance]
definition C_prop : C Prop :=
C.mk true

attribute [instance]
definition C_prod {A B : Type*} (Ha : C A) (Hb : C B) : C (prod A B) :=
C.mk (prod.mk (val Ha) (val Hb))

-- C_magic will be used because it has max priority
noncomputable definition test : C (prod Prop Prop) :=
by tactic.apply_instance

#reduce test
