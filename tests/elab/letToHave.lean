import Lean
/-!
# Tests of the `letToHave` transformation
-/

set_option pp.letVarTypes true
set_option pp.mvars.anonymous false

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
Very basic tests where there are no lets.
-/
/-- info: no change -/
#guard_msgs in #let_to_have true
/-- info: no change -/
#guard_msgs in #let_to_have fun (x : Nat) => x + 1
/-- info: no change -/
#guard_msgs in #let_to_have ∀ (x : Nat), x = x
/-- info: no change -/
#guard_msgs in #let_to_have have x := 1; x + 1

/-!
Basic tests of nondependent `let`s.
-/
/--
info: have x : Nat := 1;
true
-/
#guard_msgs in #let_to_have let x := 1; true
/--
info: have x : Nat := 1;
x + 1
-/
#guard_msgs in #let_to_have let x := 1; x + 1
/--
info: have x : Nat := 1;
have x' : Nat := x;
have x'' : Nat := x + x';
have x''' : Nat := x + x' + x'';
x + x' + x'' + x'''
-/
#guard_msgs in #let_to_have
  let x : Nat := 1; let x' := x; let x'' := x + x'; let x''' := x + x' + x''; x + x' + x'' + x'''
/--
info: fun x =>
  have x' : Nat := x;
  have x'' : Nat := x + x';
  have x''' : Nat := x + x' + x'';
  x + x' + x'' + x'''
-/
#guard_msgs in #let_to_have
  fun x : Nat => let x' := x; let x'' := x + x'; let x''' := x + x' + x''; x + x' + x'' + x'''
/--
info: (x : Nat) →
  have x' : Nat := x;
  have x'' : Nat := x + x';
  have x''' : Nat := x + x' + x'';
  Fin (x + x' + x'' + x''')
-/
#guard_msgs in #let_to_have
  ∀ x : Nat, let x' := x; let x'' := x + x'; let x''' := x + x' + x''; Fin (x + x' + x'' + x''')

/-!
Testing the cache. Reports one expression transformed.
-/
/--
info: (have x : Nat := 1;
  x + 1) +
  have x : Nat := 1;
  x + 1
---
trace: [Meta.letToHave] ✅️ transformed 1 `let` expressions into `have` expressions
  [Meta.letToHave] result:
        (have x : Nat := 1;
          x + 1) +
          have x : Nat := 1;
          x + 1
-/
#guard_msgs in
set_option trace.Meta.letToHave true in
#let_to_have (let x := 1; x + 1) + (let x := 1; x + 1)

/-!
Cache uses strict equality. Preserves binder names.
-/
/--
info: (have x : Nat := 1;
  x + 1) +
  have y : Nat := 1;
  y + 1
-/
#guard_msgs in
#let_to_have (let x := 1; x + 1) + (let y := 1; y + 1)

/-!
The expression `(1 + 2 + 3 + 4 + 5 + 6)` enters the cache first without a type,
but then a type needs to be computed under the `let`.
-/
/--
info: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 +
  have y : Nat := 1;
  1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + y
-/
#guard_msgs in
#let_to_have (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8) + (let y := 1; (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8) + y)

/-!
Dependence in a let value.
-/
/--
info: let x : Nat := 1;
have h : x = 1 := ⋯;
x
-/
#guard_msgs in #let_to_have let x := 1; let h : x = 1 := rfl; x

/-!
Dependence in a let type.
-/
/--
info: let x : Nat := 1;
have h : 0 = 0 := ⋯;
x
-/
#guard_msgs in #let_to_have let x := 1; let h : (0 : Fin x) = (0 : Fin x) := rfl; x

/-!
No dependence from the let type.
-/
/--
info: have x : Nat := 1;
have h : 0 = 0 := ⋯;
x
-/
#guard_msgs in #let_to_have let x := 1; let h : (0 : Fin (x + 1)) = (0 : Fin (x + 1)) := rfl; x
/-!
Another dependence in the let type.
-/
/--
info: let x : Nat := 1;
have h : 0 = 0 := ⋯;
x
-/
#guard_msgs in #let_to_have let x := 1; let h : (0 : Fin (x + 1)) = (0 : Fin (1 + 1)) := rfl; x

/-!
Dependence in a forall type
-/
/--
info: let U : Type 1 := Type;
have α : U := Nat;
∀ (n : α), n = n
-/
#guard_msgs in #let_to_have let U := Type; let α : U := Nat; ∀ (n : α), n = n

/-!
Dependence in a forall body
-/
/--
info: let U : Type 1 := Type;
have α : U := Nat;
Bool → α
-/
#guard_msgs in #let_to_have let U := Type; let α : U := Nat; Bool → α

/-!
Dependence in a lambda type
-/
/--
info: let U : Type 1 := Type;
have α : U := Nat;
fun n => n
-/
#guard_msgs in #let_to_have let U := Type; let α : U := Nat; fun (n : α) => n

/-!
Metavariable under binder, might be dependent, doesn't change.
-/
/-- info: no change -/
#guard_msgs in #let_to_have let x := 1; ?m
/-!
Metavariable has a context that doesn't include `x`, so it doesn't depend on it.
-/
/--
info: have x : ?_ := ?m;
?m
-/
#guard_msgs in #let_to_have let x := ?m; ?m
/-!
Similar, but we see that the outer `let` remains dependent.
-/
/--
info: let x : Nat := 1;
have y : ?_ := ?m;
?m
-/
#guard_msgs in #let_to_have let x := 1; let y := ?m; ?m

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
  let b' : Bool := !true;
  let x : Nat := 1 * (0 + a);
  let b' : Bool := !b';
  let x : Nat := 1 * x;
  let b' : Bool := !b';
  let x : Nat := 1 * x;
  let b' : Bool := !b';
  let x : Nat := 1 * x;
  let b' : Bool := !b';
  let x : Nat := 1 * x;
  if b' = true then x else 0 : Nat → Nat
-/
#guard_msgs in #check fun a => deepLets% 5 true (0 + a)
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
#guard_msgs in #let_to_have fun a => deepLets% 5 true (0 + a)

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
#guard_msgs in set_option pp.deepTerms.threshold 10 in #let_to_have fun a => deepLets% 33 true (0 + a)
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
#guard_msgs in set_option pp.deepTerms.threshold 10 in #let_to_have fun a => deepLets% 150 true (0 + a)

/-!
Tests of the `let_to_have` tactic.
-/
/--
trace: h :
  have x : Nat := 1;
  x = x
⊢ have y : Nat := 1;
  y = y
-/
#guard_msgs in
example (h : let x := 1; x = x) : let y := 1; y = y := by
  let_to_have at *
  trace_state
  rfl
/--
trace: h :
  let x : Nat := 1;
  x = x
⊢ have y : Nat := 1;
  y = y
-/
#guard_msgs in
example (h : let x := 1; x = x) : let y := 1; y = y := by
  let_to_have
  trace_state
  rfl
/--
trace: h :
  have x : Nat := 1;
  x = x
⊢ let y : Nat := 1;
  y = y
-/
#guard_msgs in
example (h : let x := 1; x = x) : let y := 1; y = y := by
  let_to_have at h
  trace_state
  rfl
