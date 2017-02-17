open tactic

-- TODO(Leo): remove the following command.
-- It has been added to avoid a crash in the code generator
noncomputable theory

inductive vector (A : Type) : nat → Type
  | nil {} : vector 0
  | cons : Π {n}, A -> vector n -> vector (nat.succ n)

definition vmap {A B : Type} (f : A -> B) : Π {n}, vector A n -> vector B n
| 0     vector.nil := vector.nil
| (n+1) (vector.cons x xs) := vector.cons (f x) (vmap xs)

noncomputable definition vappend {A} : Π {n m}, vector A n → vector A m → vector A (m + n)
| 0     0     vector.nil         vector.nil         := vector.nil
| 0     (m+1) vector.nil         (vector.cons x xs) := vector.cons x xs
| (n+1) 0     (vector.cons x xs) vector.nil         := vector.cons x (vappend xs vector.nil)
| (n+1) (m+1) (vector.cons x xs) (vector.cons y ys) := vector.cons x (vappend xs (vector.cons y ys))

axiom Sorry : ∀ A, A

theorem vappend_assoc :
  Π {A : Type} {n m k : nat} (v1 : vector A n) (v2 : vector A m) (v3 : vector A k),
  vappend (vappend v1 v2) v3 == vappend v1 (vappend v2 v3) :=
by do
     intros,
     v <- get_local `v1,
     induction v,
     v2 ← get_local `v2,
     cases v2 [`m, `h2, `t2],
     trace_state, trace "------",
     -- unfold only the first occurrence (i.e., the one of the form (vappend nil nil)
     dunfold_occs_of [1] `vappend,
     trace_state, trace "------",
     mk_const `Sorry >>= apply,
     -- unfold only the first occurrence (i.e., the one of the form (vappend nil (cons ...))
     dunfold_occs_of [1] `vappend,
     trace_state, trace "------",
     repeat $ mk_const `Sorry >>= apply
