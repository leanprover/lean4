import Lean
/-!
# Tests of the `Sym.letToHave` transformation

Port of `tests/elab/letToHave.lean` (the `Meta.letToHave` test suite) to the `sym`
implementation. Differences from the original suite:
- the `let_to_have at h`/`at *` tactic tests are not ported: in `sym =>` mode hypotheses
  are never modified (tactic tests are in `sym_let_to_have_tactic.lean`);
- there is no trace class, so the cache-reporting test only checks the output term;
- a dependent `let` whose subtree contains a metavariable is conservatively kept, like
  `Meta.letToHave`, but without its context-sensitive analysis (fvar identity is lost
  in bound-variable form): the "metavariable in the value" cases stay `let`s here even
  though `Meta.letToHave` converts them.
-/

set_option pp.letVarTypes true
set_option pp.mvars.anonymous false

open Lean Elab Command Meta Sym in
/--
`#sym_let_to_have t` elaborates `t`, hash-conses it, and applies `Sym.letToHave`.
It typechecks the result and checks it is defeq to the input.
-/
elab "#sym_let_to_have " t:term : command => runTermElabM fun _ => do
  let e ← Term.elabTermAndSynthesize t none
  Meta.check e
  SymM.run do
    let e ← shareCommon e
    let e' ← Sym.letToHave e
    Meta.check e'
    unless ← Meta.isDefEq e e' do
      throwError "result is not definitionally equal"
    if Sym.isSameExpr e e' then
      logInfo m!"no change"
    else
      logInfo m!"{e'}"

set_option linter.unusedVariables false

/-!
Very basic tests where there are no lets.
-/
/-- info: no change -/
#guard_msgs in #sym_let_to_have true
/-- info: no change -/
#guard_msgs in #sym_let_to_have fun (x : Nat) => x + 1
/-- info: no change -/
#guard_msgs in #sym_let_to_have ∀ (x : Nat), x = x
/-- info: no change -/
#guard_msgs in #sym_let_to_have have x := 1; x + 1

/-!
Basic tests of nondependent `let`s.
-/
/--
info: have x : Nat := 1;
true
-/
#guard_msgs in #sym_let_to_have let x := 1; true
/--
info: have x : Nat := 1;
x + 1
-/
#guard_msgs in #sym_let_to_have let x := 1; x + 1
/--
info: have x : Nat := 1;
have x' : Nat := x;
have x'' : Nat := x + x';
have x''' : Nat := x + x' + x'';
x + x' + x'' + x'''
-/
#guard_msgs in #sym_let_to_have
  let x : Nat := 1; let x' := x; let x'' := x + x'; let x''' := x + x' + x''; x + x' + x'' + x'''
/--
info: fun x =>
  have x' : Nat := x;
  have x'' : Nat := x + x';
  have x''' : Nat := x + x' + x'';
  x + x' + x'' + x'''
-/
#guard_msgs in #sym_let_to_have
  fun x : Nat => let x' := x; let x'' := x + x'; let x''' := x + x' + x''; x + x' + x'' + x'''
/--
info: (x : Nat) →
  have x' : Nat := x;
  have x'' : Nat := x + x';
  have x''' : Nat := x + x' + x'';
  Fin (x + x' + x'' + x''')
-/
#guard_msgs in #sym_let_to_have
  ∀ x : Nat, let x' := x; let x'' := x + x'; let x''' := x + x' + x''; Fin (x + x' + x'' + x''')

/-!
Hash-consing: the two occurrences are the same node and are converted together.
-/
/--
info: (have x : Nat := 1;
  x + 1) +
  have x : Nat := 1;
  x + 1
-/
#guard_msgs in
#sym_let_to_have (let x := 1; x + 1) + (let x := 1; x + 1)

/-!
Alpha-sharing ignores binder names, so the differently-named copies are also one node.
-/
/--
info: (have x : Nat := 1;
  x + 1) +
  have x : Nat := 1;
  x + 1
-/
#guard_msgs in
#sym_let_to_have (let x := 1; x + 1) + (let y := 1; y + 1)

/-!
A subterm that first occurs outside any `let`, then needs a type under the `let`.
-/
/--
info: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 +
  have y : Nat := 1;
  1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + y
-/
#guard_msgs in
#sym_let_to_have (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8) + (let y := 1; (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8) + y)

/-!
Dependence in a let value.
-/
/--
info: let x : Nat := 1;
have h : x = 1 := ⋯;
x
-/
#guard_msgs in #sym_let_to_have let x := 1; let h : x = 1 := rfl; x

/-!
Dependence in a let type.
-/
/--
info: let x : Nat := 1;
have h : 0 = 0 := ⋯;
x
-/
#guard_msgs in #sym_let_to_have let x := 1; let h : (0 : Fin x) = (0 : Fin x) := rfl; x

/-!
No dependence from the let type.
-/
/--
info: have x : Nat := 1;
have h : 0 = 0 := ⋯;
x
-/
#guard_msgs in #sym_let_to_have let x := 1; let h : (0 : Fin (x + 1)) = (0 : Fin (x + 1)) := rfl; x
/-!
Another dependence in the let type.
-/
/--
info: let x : Nat := 1;
have h : 0 = 0 := ⋯;
x
-/
#guard_msgs in #sym_let_to_have let x := 1; let h : (0 : Fin (x + 1)) = (0 : Fin (1 + 1)) := rfl; x

/-!
Dependence in a forall type
-/
/--
info: let U : Type 1 := Type;
have α : U := Nat;
∀ (n : α), n = n
-/
#guard_msgs in #sym_let_to_have let U := Type; let α : U := Nat; ∀ (n : α), n = n

/-!
Dependence in a forall body
-/
/--
info: let U : Type 1 := Type;
have α : U := Nat;
Bool → α
-/
#guard_msgs in #sym_let_to_have let U := Type; let α : U := Nat; Bool → α

/-!
Dependence in a lambda type
-/
/--
info: let U : Type 1 := Type;
have α : U := Nat;
fun n => n
-/
#guard_msgs in #sym_let_to_have let U := Type; let α : U := Nat; fun (n : α) => n

/-!
Metavariable under binder, might be dependent, doesn't change (same as `Meta.letToHave`).
-/
/-- info: no change -/
#guard_msgs in #sym_let_to_have let x := 1; ?m
/-!
`Meta.letToHave` converts here (the metavariable's context doesn't include `x`); the
`sym` version cannot see metavariable contexts and conservatively keeps the `let`.
-/
/-- info: no change -/
#guard_msgs in #sym_let_to_have let x := ?m; ?m
/-!
Same: `Meta.letToHave` keeps `x` but converts `y`; the `sym` version keeps both.
-/
/-- info: no change -/
#guard_msgs in #sym_let_to_have let x := 1; let y := ?m; ?m

/-!
Test with a deep let expression.
-/
syntax "deepLets% " num term:arg term:arg : term
macro_rules
  | `(deepLets% 0 $b $e) => `(if $b then $e else 0)
  | `(deepLets% $n $b $e) =>
    let n' : Lean.Syntax.NumLit := Lean.quote (n.getNat - 1)
    `(let b' : Bool := !$b; let x : Nat := 1*$e; deepLets% $n' b' x)
/--
info: fun a =>
  have b' : Bool := !true;
  have x : Nat := 1 * (0 + a);
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  if b' = true then x else 0
-/
#guard_msgs in #sym_let_to_have fun a => deepLets% 5 true (0 + a)

/--
info: fun a =>
  have b' : Bool := !true;
  have x : Nat := 1 * (0 + a);
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := ⋯;
  ⋯
-/
#guard_msgs in set_option pp.deepTerms.threshold 10 in #sym_let_to_have fun a => deepLets% 33 true (0 + a)
/--
info: fun a =>
  have b' : Bool := !true;
  have x : Nat := 1 * (0 + a);
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := 1 * x;
  have b' : Bool := !b';
  have x : Nat := ⋯;
  ⋯
-/
#guard_msgs in set_option pp.deepTerms.threshold 10 in #sym_let_to_have fun a => deepLets% 150 true (0 + a)
