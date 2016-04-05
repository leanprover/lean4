structure S1 [class] (A : Type) :=
(a : A)

structure S2 [class] (A : Type) extends S1 A :=
(b : A)

structure S3 [class] (A : Type) extends S1 A :=
(c : A)

structure S4 [class] (A : Type) extends S2 A, S3 A :=
(d : A)

constant s : S4 nat
attribute s [instance]

set_option pp.all true
-- set_option pp.purify_metavars false
-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true
-- set_option trace.class_instances true

definition f (A : Type) (s : S2 A) : S1 A :=
@S2.to_S1 A s

#unify @S3.to_S1 _ (@S4.to_S3 _ s), (f nat _ : S1 nat)

#unify @S3.to_S1 _ (@S4.to_S3 _ s), (@S2.to_S1 nat _ : S1 nat)
