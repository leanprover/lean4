module

import Lean

/-!
Regression tests for equation lemmas preserving shared values, nested binding scopes, and binding
kinds while splitting matches (#16122).
-/
@[expose] public section

set_option linter.unusedVariables false

-- 1. A `have` inside the value of a `have` whose `match` is split.
def innerHave (x : Nat) : Nat :=
  have a :=
    have b := x * x + x
    match x with
    | 0 => b
    | n + 1 => b + b + n
  a + a

/--
info: innerHave.eq_1 :
  innerHave 0 =
    have a :=
      have b := 0 * 0 + 0;
      b;
    a + a
-/
#guard_msgs in #check innerHave.eq_1

/--
info: innerHave.eq_2 (n : Nat) :
  innerHave n.succ =
    have a :=
      have b := n.succ * n.succ + n.succ;
      b + b + n;
    a + a
-/
#guard_msgs in #check innerHave.eq_2

-- 2. The same, with a non-variable discriminant `x + 1`.
def mixedUnderHave (x : Nat) : Nat :=
  have a :=
    have b := x * x
    match x, x + 1 with
    | 0, _ => b
    | n + 1, m => b + b + n + m
  a + a

/--
info: mixedUnderHave.eq_1 :
  mixedUnderHave 0 =
    have a :=
      have b := 0 * 0;
      b;
    a + a
-/
#guard_msgs in #check mixedUnderHave.eq_1

/--
info: mixedUnderHave.eq_2 (n : Nat) :
  mixedUnderHave n.succ =
    have a :=
      have b := n.succ * n.succ;
      b + b + n + (n.succ + 1);
    a + a
-/
#guard_msgs in #check mixedUnderHave.eq_2

-- 3. A `have` that is a discriminant, with a value that depends on the split variable.
def discrDep (x : Nat) : Nat :=
  have k := x * x + x
  match x, k with
  | 0, _ => 1
  | n + 1, m => n + m + m

/-- info: discrDep.eq_1 : discrDep 0 = 1 -/
#guard_msgs in #check discrDep.eq_1

/--
info: discrDep.eq_2 (n : Nat) :
  discrDep n.succ =
    have k := n.succ * n.succ + n.succ;
    n + k + k
-/
#guard_msgs in #check discrDep.eq_2

-- 4. With `cleanup.letToHave false`, the `have` stays a `have`.
set_option cleanup.letToHave false in
def noCleanup (x : Nat) : Nat :=
  have y := x + 1
  y + y

/--
info: noCleanup.eq_1 (x : Nat) :
  noCleanup x =
    have y := x + 1;
    y + y
-/
#guard_msgs in #check noCleanup.eq_1

-- A dependent binding and a nondependent `let` retain their binding kinds too.
set_option cleanup.letToHave false in
def noCleanupLet (x : Nat) : Nat :=
  let y := x + 1
  y + y

/--
info: noCleanupLet.eq_1 (x : Nat) :
  noCleanupLet x =
    let y := x + 1;
    y + y
-/
#guard_msgs in #check noCleanupLet.eq_1

set_option cleanup.letToHave false in
def noCleanupDependent (x : Nat) : Fin 5 :=
  let n := 4
  match x with
  | 0 => (⟨n, by decide⟩ : Fin (n + 1))
  | _ + 1 => 0

/--
info: noCleanupDependent.eq_1 :
  noCleanupDependent 0 =
    let n := 4;
    ⟨n, noCleanupDependent._proof_1⟩
-/
#guard_msgs in #check noCleanupDependent.eq_1

-- The computed discriminant remains shared even when it also occurs in a branch hypothesis.
def computedPremise (f : Nat → Nat) (x : Nat) : Nat :=
  have k := f x
  match x, k with
  | 0, _ => 1
  | _, 0 => 2
  | n + 1, m + 1 => n + k + k + m

/--
info: equations:
@[backward_defeq] theorem computedPremise.eq_1 : ∀ (f : Nat → Nat), computedPremise f 0 = 1
theorem computedPremise.eq_2 : ∀ (f : Nat → Nat) (x_1 : Nat), (x_1 = 0 → False) → f x_1 = 0 → computedPremise f x_1 = 2
theorem computedPremise.eq_3 : ∀ (f : Nat → Nat) (n m : Nat),
  f n.succ = m.succ →
    computedPremise f n.succ =
      have k := f n.succ;
      n + k + k + m
-/
#guard_msgs in #print equations computedPremise

-- Each inner `y` belongs to its own binding value, including the value without a match.
def nestedScopes (x : Nat) : Nat :=
  have a :=
    have y := x + 1
    match x with
    | 0 => y + y
    | n + 1 => y + y + n
  have b :=
    have y := x * x
    a + y + y
  a + b + b

/--
info: nestedScopes.eq_2 (n : Nat) :
  nestedScopes n.succ =
    have a :=
      have y := n.succ + 1;
      y + y + n;
    have b :=
      have y := n.succ * n.succ;
      a + y + y;
    a + b + b
-/
#guard_msgs in #check nestedScopes.eq_2

-- A match in a dead binding must not produce extra equations.
def unusedValue (x : Nat) : Nat :=
  have y := match x with
    | 0 => 1
    | _ + 1 => 2
  7

/--
info: equations:
@[backward_defeq] theorem unusedValue.eq_1 : ∀ (x : Nat), unusedValue x = 7
-/
#guard_msgs in #print equations unusedValue

-- Matches capturing a lambda parameter stay inside the lambda; independent matches can split.
def lambdaCapture (x : Nat) (ys : List Nat) : List Nat :=
  ys.map fun y => match x with
    | 0 => y
    | n + 1 => n + y

def lambdaIndependent (x : Nat) (ys : List Nat) : List Nat :=
  ys.map fun _ => match x with
    | 0 => 7
    | n + 1 => n

open Lean Meta in
run_meta do
  for (decl, count) in #[(``lambdaCapture, 1), (``lambdaIndependent, 2)] do
    let some eqns ← getEqnsFor? decl | throwError "missing equations for {decl}"
    unless eqns.size == count do
      throwError "expected {count} equations for {decl}, got {eqns.size}"

-- A value fixed by the result type still reduces matches through local constructor aliases.
set_option cleanup.letToHave false in
def fixedValue (x : Nat) : Fin (x + 1) :=
  let n :=
    have a := some x
    have b := a
    match b with
    | none => 0
    | some k => k
  (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))

open Lean Meta in
run_meta do
  let some eqns ← getEqnsFor? ``fixedValue | throwError "missing equations"
  unless eqns.size == 1 do throwError "expected one equation, got {eqns.size}"
  forallTelescope (← getConstInfo eqns[0]!).type fun xs body => do
    let some (_, _, .letE _ _ value _ false) := body.eq?
      | throwError "dependent binding was lost"
    unless value == xs[0]! do throwError "constructor aliases in the fixed value did not reduce"

example (x : Nat) : (fixedValue x).val = 0 := by
  rw [fixedValue.eq_1]

-- Once a branch drops dependent uses, its remaining shared value can simplify propositionally.
set_option cleanup.letToHave false in
def branchDeadValueBarrier (x : Nat) : Nat :=
  have a := match x with | 5 => 1 | _ => 2
  let n := a + 1
  have v : Fin n := ⟨a, Nat.lt_succ_self a⟩
  match x with
  | 5 => v.val
  | _ => a + a

open Lean Meta in
run_meta do
  let some eqns ← getEqnsFor? ``branchDeadValueBarrier | throwError "missing equations"
  unless eqns.size == 2 do throwError "expected two equations, got {eqns.size}"
  for eqn in eqns do
    discard <| getConstInfo eqn
  forallTelescope (← getConstInfo eqns[1]!).type fun _ body => do
    let some (_, _, .letE _ _ value _ true) := body.eq?
      | throwError "shared value was lost"
    unless ← isDefEq value (mkNatLit 2) do throwError "branch value did not simplify"

-- Expanding this value before finding the match would duplicate the chain exponentially.
def nestedChain (x : Nat) : Nat :=
  have a :=
    have v0 := x * x + x
    have v1 := v0 + v0
    have v2 := v1 + v1
    have v3 := v2 + v2
    have v4 := v3 + v3
    have v5 := v4 + v4
    have v6 := v5 + v5
    have v7 := v6 + v6
    have v8 := v7 + v7
    have v9 := v8 + v8
    have v10 := v9 + v9
    have v11 := v10 + v10
    have v12 := v11 + v11
    have v13 := v12 + v12
    have v14 := v13 + v13
    have v15 := v14 + v14
    have v16 := v15 + v15
    have v17 := v16 + v16
    have v18 := v17 + v17
    have v19 := v18 + v18
    have v20 := v19 + v19
    have v21 := v20 + v20
    have v22 := v21 + v21
    have v23 := v22 + v22
    have v24 := v23 + v23
    match x with
    | 0 => v24
    | n + 1 => v24 + v24 + n
  a + a

open Lean Meta in
run_meta do
  let some eqns ← getEqnsFor? ``nestedChain | throwError "missing equations"
  unless eqns.size == 2 do throwError "expected two equations, got {eqns.size}"
  for eqn in eqns do
    let type := (← getConstInfo eqn).type
    forallTelescope type fun _ body => do
      let some (_, _, rhs) := body.eq? | throwError "expected an equation"
      let .letE `a _ value _ true := rhs | throwError "outer have was lost"
      let mut value := value
      let mut count : Nat := 0
      while let .letE _ _ _ body true := value do
        count := count + 1
        value := body
      unless count == 25 do throwError "expected 25 nested haves, got {count}"
      unless (← rhs.numObjs) < 1000 do throwError "equation exceeded the size bound"

open Lean Meta in
run_meta do
  for (decl, nondep) in #[(``noCleanup, true), (``noCleanupLet, false),
      (``noCleanupDependent, false)] do
    let some eqns ← getEqnsFor? decl | throwError "missing equations for {decl}"
    forallTelescope (← getConstInfo eqns[0]!).type fun _ body => do
      let some (_, _, .letE _ _ _ _ actual) := body.eq?
        | throwError "binding was lost in {decl}"
      unless actual == nondep do throwError "binding kind changed in {decl}"

/--
info: nestedChain.eq_2 (n : Nat) :
  nestedChain n.succ =
    have a :=
      have v0 := n.succ * n.succ + n.succ;
      have v1 := v0 + v0;
      have v2 := v1 + v1;
      have v3 := v2 + v2;
      have v4 := v3 + v3;
      have v5 := v4 + v4;
      have v6 := v5 + v5;
      have v7 := v6 + v6;
      have v8 := v7 + v7;
      have v9 := v8 + v8;
      have v10 := v9 + v9;
      have v11 := v10 + v10;
      have v12 := v11 + v11;
      have v13 := v12 + v12;
      have v14 := v13 + v13;
      have v15 := v14 + v14;
      have v16 := v15 + v15;
      have v17 := v16 + v16;
      have v18 := v17 + v17;
      have v19 := v18 + v18;
      have v20 := v19 + v19;
      have v21 := v20 + v20;
      have v22 := v21 + v21;
      have v23 := v22 + v22;
      have v24 := v23 + v23;
      v24 + v24 + n;
    a + a
-/
#guard_msgs in
#check nestedChain.eq_2
