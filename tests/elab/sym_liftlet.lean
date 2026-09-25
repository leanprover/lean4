module

import Lean

/-!
Tests for `Lean.Meta.Sym.liftLets`: lifting `let`/`have` declarations to the root of a
maximally shared term inside a `SymM` session. Covers flattening of nested declarations,
merging of pointer-equal definitions, `let`/`have` upgrade on merge, opaque binders
(`fun`/`∀` are not descended into), de Bruijn index adjustment for binder bodies that
reference lifted `let`s, and pointer-equal results when no progress is made.
-/

open Lean Meta Sym

axiom S : Type
axiom c : S
axiom f : S → S → S
axiom g : S → S
axiom g3 : S → S → S → S
axiom h3 : S → S → S → S
axiom hof : (S → S) → S

/-- Lifts the lets in the value of `declName`, checks the result is defeq, and prints it. -/
def checkLift (declName : Name) : MetaM Unit := do
  let some info := (← getEnv).find? declName | throwError "unknown declaration {declName}"
  let e := info.value!
  SymM.run do
    let e ← shareCommon e
    let r ← Sym.liftLets e
    unless ← isDefEq e r do
      throwError "`Sym.liftLets` result is not defeq to the input{indentExpr r}"
    logInfo m!"{r}"

/-- Like `checkLift`, but expects `liftLets` to make no progress (pointer-equal result). -/
def checkNoProgress (declName : Name) : MetaM Unit := do
  let some info := (← getEnv).find? declName | throwError "unknown declaration {declName}"
  let e := info.value!
  SymM.run do
    let e ← shareCommon e
    let r ← Sym.liftLets e
    unless isSameExpr e r do
      throwError "expected pointer-equal result, got{indentExpr r}"
    logInfo "no progress (pointer-equal)"

/-! Parallel branches: all three lets lift to the top, in dependency order. -/

noncomputable def ex1 : S := let a := c; f (let x := g a; g3 x a x) (let y := f a a; h3 y a y)

/--
info: have a := c;
have x := g a;
have y := f a a;
f (g3 x a x) (h3 y a y)
-/
#guard_msgs in
run_meta checkLift ``ex1

/-! A let nested in the value of another let is flattened. -/

noncomputable def ex2 : S := f (let x := (let y := g c; g y); g x) c

/--
info: have y := g c;
have x := g y;
f (g x) c
-/
#guard_msgs in
run_meta checkLift ``ex2

/-! Pointer-equal values are merged into a single declaration. -/

noncomputable def ex3 : S := f (let x := g c; f x x) (let z := g c; g z)

/--
info: have x := g c;
f (f x x) (g x)
-/
#guard_msgs in
run_meta checkLift ``ex3

/-! `have` (nondependent let) is preserved. -/

noncomputable def ex4 : S := f (have x := g c; g x) c

/--
info: have x := g c;
f (g x) c
-/
#guard_msgs in
run_meta checkLift ``ex4

/-! Merging a `have` with a `let` with the same definition produces a `let`. -/

noncomputable def ex5 : S := f (have x := g c; f x x) (let z := g c; g z)

/--
info: have x := g c;
f (f x x) (g x)
-/
#guard_msgs in
run_meta checkLift ``ex5

/-! Lets under a lambda are not lifted; the term is unchanged (pointer-equal). -/

noncomputable def ex6 : S := f (hof fun z => let u := g c; f z u) c

/--
info: no progress (pointer-equal)
-/
#guard_msgs in
run_meta checkNoProgress ``ex6

/-!
A lambda body referencing a lifted let: the occurrence must be reindexed, since the
second let is inserted between the lambda and the binder it references.
-/

noncomputable def ex7 : S := f (let a := g c; hof fun z => f a z) (let y := f c c; g y)

/--
info: have a := g c;
have y := f c c;
f (hof fun z => f a z) (g y)
-/
#guard_msgs in
run_meta checkLift ``ex7

/-! A term already in lifted form is returned unchanged (pointer-equal). -/

noncomputable def ex8 : S := let a := c; g a

/--
info: no progress (pointer-equal)
-/
#guard_msgs in
run_meta checkNoProgress ``ex8

/-! A single let lifts from deep inside an application spine. -/

noncomputable def ex9 : S := g (g (g (let x := c; g x)))

/--
info: have x := c;
g (g (g (g x)))
-/
#guard_msgs in
run_meta checkLift ``ex9

/-!
A genuinely dependent `let` (`nondep := false`): the proof `Nat.one_pos : 0 < 1` only
typechecks against `Fin n` by unfolding `n := 1`, so the elaborator must keep a real
`let`, and lifting must preserve it.
-/

noncomputable def ex10 : Nat := Nat.succ ((let n := 1; (⟨0, Nat.one_pos⟩ : Fin n)).val)

/--
info: let n := 1;
(↑⟨0, Nat.zero_lt_one⟩).succ
-/
#guard_msgs in
run_meta checkLift ``ex10

/-!
Merging a `have` with a `let` with pointer-equal definition produces a `let`.
Constructed with raw expressions: elaborated `have` binder types carry `borrowed`
metadata, so surface syntax cannot produce pointer-equal definitions across
`have`/`let` pairs.
-/

def checkMerge : MetaM Unit := do
  let Sc := mkConst ``S
  let fc := mkConst ``f
  let gc := mkConst ``g
  SymM.run do
    let v ← shareCommon (mkApp gc (mkConst ``c))
    -- f (have x := g c; g x) (let y := g c; f y y)
    let e := mkApp2 fc
      (.letE `x Sc v (mkApp gc (.bvar 0)) true)
      (.letE `y Sc v (mkApp2 fc (.bvar 0) (.bvar 0)) false)
    let e ← shareCommon e
    let r ← Sym.liftLets e
    unless ← isDefEq e r do
      throwError "`Sym.liftLets` result is not defeq to the input{indentExpr r}"
    logInfo m!"{r}"

/--
info: let x := g c;
f (g x) (f x x)
-/
#guard_msgs in
run_meta checkMerge

noncomputable def ex11 : Nat := (have a := 1; a) + (have b := 1; b + 2)

/--
info: have a := 1;
a + (a + 2)
-/
#guard_msgs in
run_meta checkLift ``ex11

noncomputable def ex12 : Nat := (let a := 1; a) + (let b := 1; b + 2)

/-!
The `lift_lets` tactic in `sym =>` mode: lifts lets in the goal target, replaces the
goal with a definitionally equal one (proof by `rfl`), and the final proof is accepted
by the kernel.
-/

/--
trace: case grind
P : S → Prop
x : S
h : ∀ (y : S), P y
⊢ let a := f x x;
  let b := g x;
  P (f (g a) (g b))
-/
#guard_msgs in
example (P : S → Prop) (x : S) (h : ∀ y, P y) :
    P (f (let a := f x x; g a) (let b := g x; g b)) := by
  sym =>
    lift_lets
    show_goals
    exact h _

/-! `lift_lets` fails when there is nothing to lift (here, the `let` is under a lambda). -/

example (P : S → Prop) (h : ∀ y, P y) : P (hof fun z => let u := g z; f z u) := by
  sym =>
  fail_if_success lift_lets
  exact h _
