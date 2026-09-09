import Lean
/-!
# Stress tests for `letToHave` verdicts

Families that are sensitive to the design of the `sym =>` mode `let_to_have`
(see `sym_let_to_have_perf.md`): dependence discovered only through a
whnf-to-sort obligation, dependence through instance defeq, and clean closures
that must not create dependence. The verdicts documented here must be
reproduced by `Sym.letToHave`.
-/

set_option pp.letVarTypes true

open Lean Elab Command in
/--
`#let_to_have t` elaborates `t` then applies let-to-have. It typechecks `t` before and after.
-/
elab "#let_to_have " t:term : command => runTermElabM fun _ => do
  let e ← Term.elabTermAndSynthesize t none
  Meta.check e
  let e' ← Meta.letToHave e
  Meta.check e'
  unless ← Meta.isDefEq e e' do
    throwError "result is not definitionally equal"
  if e == e' then
    logInfo m!"no change"
  else
    logInfo m!"{e'}"

set_option linter.unusedVariables false

/-!
Dependence discovered only through a whnf-to-sort obligation: the domain `G x` has type
`H x`, which is a sort only after zeta-unfolding `x`. The `let` must be kept.
-/
def H : Bool → Type 1 := fun b => match b with | true => Type | false => Type
axiom G : (b : Bool) → H b

/-- info: no change -/
#guard_msgs in #let_to_have let x := true; fun (y : G x) => True

/-!
Dependence through instance defeq: elaborating `(1 : α)` uses `instOfNatNat`, which
requires `α ≡ Nat` by zeta-unfolding. The `let` must be kept.
-/
/-- info: no change -/
#guard_msgs in #let_to_have let α := Nat; ((1, 2) : α × α).1

/-!
A clean closure under the `let`: the lambda's binder type does not involve `x`, so the
closure body cannot create a dependence. Must become a `have`.
-/
/--
info: have x : Nat := 10;
List.foldl (fun a b => a + b) x [1, 2]
-/
#guard_msgs in #let_to_have let x := 10; List.foldl (fun a b => a + b) x [1, 2]

/-!
Projection whose structure type is closed: no dependence. Must become a `have`.
-/
/--
info: have x : Nat × Nat := (1, 2);
x.fst
-/
#guard_msgs in #let_to_have let x := (1, 2); x.1

/-!
Note for the future `Sym.letToHave` test: add the pointer-sharing family — the same
shared open `.letE` under two enclosing binders of different types, where the verdicts
differ per context (e.g. `let w := b; (rfl : w = b)` is nondependent for `b : Unit`
via eta, dependent for `b : Nat`). Not expressible here: elaborated terms are not
hash-consed.
-/
