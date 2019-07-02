variables {δ σ : Type}

def foo1 : StateT δ (StateT σ Id) σ :=
monadLift (get : StateT σ Id σ)
/-
In Lean3, we used to use the quasi-pattern approximation during elaboration.
The example above demonstrates why it produces counterintuitive behavior.
We have the `Monad-lift` application:

@monadLift ?m ?n ?c ?α (get : StateT σ id σ) : ?n ?α

It produces the following unification problem when we process the expected Type:

?n ?α =?= StateT δ (StateT σ id) σ
==> (approximate using first-order unification)
?n := StateT δ (StateT σ id)
?α := σ

Then, we need to solve:

?m ?α =?= StateT σ id σ
==> instantiate metavars
?m σ =?= StateT σ id σ
==> (approximate since it is a quasi-pattern unification constraint)
?m := fun σ => StateT σ id σ

Remark: the constraint is not a Milner pattern because σ is in
the local context of `?m`. We are ignoring the other possible solutions:
?m := fun σ' => StateT σ id σ
?m := fun σ' => StateT σ' id σ
?m := fun σ' => StateT σ id σ'

We need the quasi-pattern approximation for elaborating recursors.
One Option is to enable this kind of approximation only when
elaborating recursors and executing induction-like tactics.

If we had use first-order unification, then we would have produced
the right answer: `?m := StateT σ id`

Haskell would work on this example since it always uses
first-order unification.
-/

def foo2 : StateT δ (StateT σ Id) σ :=
do s : σ  ← monadLift (get : StateT σ Id σ);
   pure s
