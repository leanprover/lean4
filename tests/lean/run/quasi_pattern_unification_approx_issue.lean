variables {δ σ : Type}

def foo1 : state_t δ (state_t σ id) σ :=
monad_lift (get : state_t σ id σ)
/-
In Lean3, we used to use the quasi-pattern approximation during elaboration.
The example above demonstrates why it produces counterintuitive behavior.
We have the `monad-lift` application:

@monad_lift ?m ?n ?c ?α (get : state_t σ id σ) : ?n ?α

It produces the following unification problem when we process the expected type:

?n ?α =?= state_t δ (state_t σ id) σ
==> (approximate using first-order unification)
?n := state_t δ (state_t σ id)
?α := σ

Then, we need to solve:

?m ?α =?= state_t σ id σ
==> instantiate metavars
?m σ =?= state_t σ id σ
==> (approximate since it is a quasi-pattern unification constraint)
?m := λ σ, state_t σ id σ

Remark: the constraint is not a Milner pattern because σ is in
the local context of `?m`. We are ignoring the other possible solutions:
?m := λ σ', state_t σ id σ
?m := λ σ', state_t σ' id σ
?m := λ σ', state_t σ id σ'

We need the quasi-pattern approximation for elaborating recursors.
One option is to enable this kind of approximation only when
elaborating recursors and executing induction-like tactics.

If we had use first-order unification, then we would have produced
the right answer: `?m := state_t σ id`

Haskell would work on this example since it always uses
first-order unification.
-/

def foo2 : state_t δ (state_t σ id) σ :=
do s : σ  ← monad_lift (get : state_t σ id σ),
   pure s
