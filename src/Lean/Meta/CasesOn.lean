/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.KAbstract
import Lean.Meta.Check

namespace Lean.Meta

structure CasesOnApp where
  declName     : Name
  us           : List Level
  params       : Array Expr
  motive       : Expr
  indices      : Array Expr
  major        : Expr
  alts         : Array Expr
  altNumParams : Array Nat
  remaining    : Array Expr
  /-- `true` if the `casesOn` can only eliminate into `Prop` -/
  propOnly     : Bool

/-- Return `some c` if `e` is a `casesOn` application. -/
def toCasesOnApp? (e : Expr) : MetaM (Option CasesOnApp) := do
  let f := e.getAppFn
  let .const declName us _ := f | return none
  unless isCasesOnRecursor (← getEnv) declName do return none
  let indName := declName.getPrefix
  let .inductInfo info ← getConstInfo indName | return none
  let args := e.getAppArgs
  unless args.size >= info.numParams + 1 /- motive -/ + info.numIndices + 1 /- major -/ + info.numCtors do return none
  let params    := args[:info.numParams]
  let motive    := args[info.numParams]
  let indices   := args[info.numParams + 1 : info.numParams + 1 + info.numIndices]
  let major     := args[info.numParams + 1 + info.numIndices]
  let alts      := args[info.numParams + 1 + info.numIndices + 1 : info.numParams + 1 + info.numIndices + 1 + info.numCtors]
  let remaining := args[info.numParams + 1 + info.numIndices + 1 + info.numCtors :]
  let propOnly  := info.levelParams.length == us.length
  let mut altNumParams := #[]
  for ctor in info.ctors do
    let .ctorInfo ctorInfo ← getConstInfo ctor | unreachable!
    altNumParams := altNumParams.push ctorInfo.numFields
  return some { declName, us, params, motive, indices, major, alts, remaining, propOnly, altNumParams }

/-- Convert `c` back to `Expr` -/
def CasesOnApp.toExpr (c : CasesOnApp) : Expr :=
  mkAppN (mkAppN (mkApp (mkAppN (mkApp (mkAppN (mkConst c.declName c.us) c.params) c.motive) c.indices) c.major) c.alts) c.remaining

/--
  Given a `casesOn` application `c` of the form
  ```
  casesOn As (fun is x => motive[i, xs]) is major  (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining
  ```
  and an expression `e : B[is, major]`, construct the term
  ```
  casesOn As (fun is x => B[is, x] → motive[i, xs]) is major (fun ys_1 (y : B[C_1[ys_1]]) => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n (y : B[C_n[ys_n]]) => (alt_n : motive (C_n[ys_n]) e remaining
  ```
  We use `kabstract` to abstract the `is` and `major` from `B[is, major]`.
-/
def CasesOnApp.addArg (c : CasesOnApp) (arg : Expr) (checkIfRefined : Bool := false) : MetaM CasesOnApp := do
  lambdaTelescope c.motive fun motiveArgs motiveBody => do
    unless motiveArgs.size == c.indices.size + 1 do
      throwError "failed to add argument to `casesOn` application, motive must be lambda expression with #{c.indices.size + 1} binders"
    let argType ← inferType arg
    let discrs := c.indices ++ #[c.major]
    let mut argTypeAbst := argType
    for motiveArg in motiveArgs.reverse, discr in discrs.reverse do
      argTypeAbst := (← kabstract argTypeAbst discr).instantiate1 motiveArg
    let motiveBody ← mkArrow argTypeAbst motiveBody
    let us ← if c.propOnly then pure c.us else pure ((← getLevel motiveBody) :: c.us.tail!)
    let motive ← mkLambdaFVars motiveArgs motiveBody
    let remaining := #[arg] ++ c.remaining
    let aux := mkAppN (mkConst c.declName us) c.params
    let aux := mkApp aux motive
    let aux := mkAppN aux discrs
    check aux
    unless (← isTypeCorrect aux) do
      throwError "failed to add argument to `casesOn` application, type error when constructing the new motive{indentExpr aux}"
    let auxType ← inferType aux
    let alts ← updateAlts argType auxType
    return { c with us, motive, alts, remaining }
where
  updateAlts (argType : Expr) (auxType : Expr) : MetaM (Array Expr) := do
    let mut auxType := auxType
    let mut altsNew := #[]
    let mut refined := false
    for alt in c.alts, numParams in c.altNumParams do
      auxType ← whnfD auxType
      match auxType with
      | .forallE _ d b _ =>
        let (altNew, refinedAt) ← forallBoundedTelescope d (some numParams) fun xs d => do
          forallBoundedTelescope d (some 1) fun x _ => do
            let alt := alt.beta xs
            let alt ← mkLambdaFVars x alt -- x is the new argument we are adding to the alternative
            if checkIfRefined then
              return (← mkLambdaFVars xs alt, !(← isDefEq argType (← inferType x[0])))
            else
              return (← mkLambdaFVars xs alt, true)
        if refinedAt then
          refined := true
        auxType := b.instantiate1 altNew
        altsNew := altsNew.push altNew
      | _ => throwError "unexpected type at `casesOnAddArg`"
    unless refined do
      throwError "failed to add argument to `casesOn` application, argument type was not refined by `casesOn`"
    return altsNew

/-- Similar `CasesOnApp.addArg`, but returns `none` on failure. -/
def CasesOnApp.addArg? (c : CasesOnApp) (arg : Expr) (checkIfRefined : Bool := false) : MetaM (Option CasesOnApp) :=
  try
    return some (← c.addArg arg checkIfRefined)
  catch _ =>
    return none

end Lean.Meta
