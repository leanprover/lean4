open tactic

inductive vector (A : Type) : nat → Type
  | nil {} : vector 0
  | cons : Π {n}, A -> vector n -> vector (nat.succ n)

definition vmap {A B : Type} (f : A -> B) : Π {n}, vector A n -> vector B n
| vmap vector.nil := vector.nil
| vmap (vector.cons x xs) := vector.cons (f x) (vmap xs)

definition vappend {A} : Π {n m}, vector A n -> vector A m -> vector A (m + n)
| vappend vector.nil vector.nil := vector.nil
| vappend vector.nil (vector.cons x xs) := vector.cons x xs
| vappend (vector.cons x xs) vector.nil := vector.cons x (vappend xs vector.nil)
| vappend (vector.cons x xs) (vector.cons y ys) := vector.cons x (vappend xs (vector.cons y ys))

axiom Sorry : ∀ A, A

theorem vappend_assoc :
  Π {A : Type} {n m k : nat} (v1 : vector A n) (v2 : vector A m) (v3 : vector A k),
  vappend (vappend v1 v2) v3 == vappend v1 (vappend v2 v3) :=
by do
     intros,
     v <- get_local `v1,
     induction_core semireducible v (`vector.rec_on) [],
     v2 ← get_local `v2,
     cases_using v2 [`m, `h2, `t2],
     trace_state, trace "------",
     -- unfold only the first occurrence (i.e., the one of the form (vappend nil nil)
     unfold_occs_of [1] `vappend,
     trace_state, trace "------",
     mk_const `Sorry >>= apply,
     -- unfold only the first occurrence (i.e., the one of the form (vappend nil (cons ...))
     unfold_occs_of [1] `vappend,
     trace_state, trace "------",
     repeat $ mk_const `Sorry >>= apply
