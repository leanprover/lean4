module

import Lean

/-!
Tests for `Lean.Meta.Sym.letToHave`: converting nondependent `let` declarations of a
maximally shared term into `have` declarations inside a `SymM` session. The harness
re-flags every `let`/`have` of an elaborated value as a dependent `let` first, so the
transformation has to rediscover the nondependent ones. Covers the verdict families of
`tests/elab/letToHaveStress.lean` (sort-obligation dependence, instance-defeq
dependence, clean closures), `let`s under binders, lambda arguments (`checkFun`), and
pointer-equal results when no progress is made.
-/

open Lean Meta Sym

axiom S : Type
axiom c : S
axiom f : S → S → S
axiom g : S → S
axiom hof : (S → S) → S

set_option linter.unusedVariables false

/-- Recursively re-flags every `let`/`have` as a dependent `let`. -/
partial def resetHaves (e : Expr) : Expr :=
  match e with
  | .letE n t v b _ => .letE n (resetHaves t) (resetHaves v) (resetHaves b) false
  | .app fn a => .app (resetHaves fn) (resetHaves a)
  | .lam n t b bi => .lam n (resetHaves t) (resetHaves b) bi
  | .forallE n t b bi => .forallE n (resetHaves t) (resetHaves b) bi
  | .mdata d b => .mdata d (resetHaves b)
  | .proj s i b => .proj s i (resetHaves b)
  | _ => e

/--
Re-flags all `let`s of the value of `declName` as dependent, runs `Sym.letToHave`,
checks the result is defeq and type correct, and prints it.
-/
def checkL2H (declName : Name) : MetaM Unit := do
  let some info := (← getEnv).find? declName | throwError "unknown declaration {declName}"
  let e := resetHaves info.value!
  SymM.run do
    let e ← shareCommon e
    let r ← Sym.letToHave e
    unless ← isDefEq e r do
      throwError "`Sym.letToHave` result is not defeq to the input{indentExpr r}"
    check r
    logInfo m!"{r}"

/-- Like `checkL2H`, but expects `letToHave` to make no progress (pointer-equal result). -/
def checkNoProgress (declName : Name) : MetaM Unit := do
  let some info := (← getEnv).find? declName | throwError "unknown declaration {declName}"
  let e := resetHaves info.value!
  SymM.run do
    let e ← shareCommon e
    let r ← Sym.letToHave e
    unless isSameExpr e r do
      throwError "expected pointer-equal result, got{indentExpr r}"
    logInfo "no progress (pointer-equal)"

/-! A chain of nondependent `let`s: all are converted. -/

noncomputable def exChain : S := let a := c; let b := f a c; let d := f b c; d

/--
info: have a := c;
have b := f a c;
have d := f b c;
d
-/
#guard_msgs in
run_meta checkL2H ``exChain

/-! Dependence in a `let` value: `x` must stay a `let`, `h` becomes a `have`. -/

def exDepVal : Nat := let x : Nat := 1; let h : x = 1 := rfl; x

/--
info: let x := 1;
have h := ⋯;
x
-/
#guard_msgs in
run_meta checkL2H ``exDepVal

/-!
Dependence discovered only through a whnf-to-sort obligation: the domain `G x` has type
`H x`, which is a sort only after zeta-unfolding `x`. The `let` must be kept.
-/

def H : Bool → Type 1 := fun b => match b with | true => Type | false => Type
axiom G : (b : Bool) → H b

def exSort : Prop := let x := true; ∀ (_ : G x), True

/-- info: no progress (pointer-equal) -/
#guard_msgs in
run_meta checkNoProgress ``exSort

/-!
Dependence through instance defeq: elaborating `(1 : α)` uses `instOfNatNat`, which
requires `α ≡ Nat` by zeta-unfolding. The `let` must be kept.
-/

def exInst := let α := Nat; ((1, 2) : α × α).1

/-- info: no progress (pointer-equal) -/
#guard_msgs in
run_meta checkNoProgress ``exInst

/-! A clean closure under the `let`: the closure body cannot create a dependence. -/

def exClosure : Nat := let x := 10; List.foldl (fun a b => a + b) x [1, 2]

/--
info: have x := 10;
List.foldl (fun a b => a + b) x [1, 2]
-/
#guard_msgs in
run_meta checkL2H ``exClosure

/-! A nondependent `let` with loose bound variables (under a lambda). -/

noncomputable def exUnder : S → S := fun y => let x := f y y; g x

/--
info: fun y =>
  have x := f y y;
  g x
-/
#guard_msgs in
run_meta checkL2H ``exUnder

/-! A lambda argument mentioning the `let` variable (`checkFun` path). -/

noncomputable def exLamArg : S := let x := c; f (hof (fun y => f y x)) x

/--
info: have x := c;
f (hof fun y => f y x) x
-/
#guard_msgs in
run_meta checkL2H ``exLamArg

/-! No `let`s at all: pointer-equal result. -/

noncomputable def exNoLet : S := f c c

/-- info: no progress (pointer-equal) -/
#guard_msgs in
run_meta checkNoProgress ``exNoLet
