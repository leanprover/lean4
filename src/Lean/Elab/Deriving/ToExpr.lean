/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.ToLevel
import Lean.ToExpr

/-!
# `ToExpr` deriving handler

This module defines a `ToExpr` deriving handler for inductive types.
It supports mutually inductive types as well.

The `ToExpr` deriving handlers support universe level polymorphism, via the `Lean.ToLevel` class.
To use `ToExpr` in places where there is universe polymorphism, make sure a `[ToLevel.{u}]` instance is available,
though be aware that the `ToLevel` mechanism does not support `max` or `imax` expressions.

Implementation note: this deriving handler was initially modeled after the `Repr` deriving handler, but
1. we need to account for universe levels,
2. the `ToExpr` class has two fields rather than one, and
3. we don't handle structures specially.
-/

namespace Lean.Elab.Deriving.ToExpr

open Lean Elab Parser.Term
open Meta Command Deriving

/--
Given `args := #[e₁, e₂, …, eₙ]`, constructs the syntax `Expr.app (… (Expr.app (Expr.app f e₁) e₂) …) eₙ`.
-/
def mkAppNTerm (f : Term) (args : Array Term) : MetaM Term :=
  args.foldlM (fun a b => ``(Expr.app $a $b)) f

/-- Fixes the output of `mkInductiveApp` to explicitly reference universe levels. -/
def updateIndType (indVal : InductiveVal) (t : Term) : TermElabM Term :=
  let levels := indVal.levelParams.toArray.map mkIdent
  match t with
  | `(@$f $args*) => `(@$f.{$levels,*} $args*)
  | _ => throwError "(internal error) expecting output of `mkInductiveApp`"

/--
Creates a term that evaluates to an expression representing the inductive type.
Uses `toExpr` and `toTypeExpr` for the arguments to the type constructor.
-/
def mkToTypeExpr (indVal : InductiveVal) (argNames : Array Name) : TermElabM Term := do
  let levels ← indVal.levelParams.toArray.mapM (fun u => `(Lean.toLevel.{$(mkIdent u)}))
  forallTelescopeReducing indVal.type fun xs _ => do
    let mut args : Array Term := #[]
    for argName in argNames, x in xs do
      let a := mkIdent argName
      if ← Meta.isType x then
        args := args.push <| ← ``(toTypeExpr $a)
      else
        args := args.push <| ← ``(toExpr $a)
    mkAppNTerm (← ``(Expr.const $(quote indVal.name) [$levels,*])) args

/--
Creates the body of the `toExpr` function for the `ToExpr` instance, which is a `match` expression
that calls `toExpr` and `toTypeExpr` to assemble an expression for a given term.
For recursive inductive types, `auxFunName` refers to the `ToExpr` instance for the current type.
For mutually recursive types, we rely on the local instances set up by `mkLocalInstanceLetDecls`.
-/
def mkToExprBody (header : Header) (indVal : InductiveVal) (auxFunName : Name) (levelInsts : Array Term) :
    TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  /-- Create the `match` cases, one per constructor. -/
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let levels ← levelInsts.mapM fun inst => `($(inst).toLevel)
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patterns := #[]
        -- add `_` pattern for indices, before the constructor's pattern
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        let mut rhsArgs : Array Term := #[]
        let mkArg (x : Expr) (a : Term) : TermElabM Term := do
          if (← inferType x).isAppOf indVal.name then
            `($(mkIdent auxFunName) $levelInsts* $a)
          else if ← Meta.isType x then
            ``(toTypeExpr $a)
          else
            ``(toExpr $a)
        -- add `_` pattern for inductive parameters, which are inaccessible
        for i in [:ctorInfo.numParams] do
          let a := mkIdent header.argNames[i]!
          ctorArgs := ctorArgs.push (← `(_))
          rhsArgs := rhsArgs.push <| ← mkArg xs[i]! a
        for i in [:ctorInfo.numFields] do
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          rhsArgs := rhsArgs.push <| ← mkArg xs[ctorInfo.numParams + i]! a
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        let rhs : Term ← mkAppNTerm (← ``(Expr.const $(quote ctorInfo.name) [$levels,*])) rhsArgs
        `(matchAltExpr| | $[$patterns:term],* => $rhs)
      alts := alts.push alt
    return alts

/--
For nested and mutually recursive inductive types, we define `partial` instances,
and the strategy is to have local `ToExpr` instances in scope for the body of each instance.
This way, each instance can freely use `toExpr` and `toTypeExpr` for each of the types in `ctx`.

This is a modified copy of `Lean.Elab.Deriving.mkLocalInstanceLetDecls`,
since we need to include the `toTypeExpr` field in the `letDecl`
Note that, for simplicity, each instance gets its own definition of each others' `toTypeExpr` fields.
These are very simple fields, so avoiding the duplication is not worth it.
-/
def mkLocalInstanceLetDecls (ctx : Deriving.Context) (argNames : Array Name) (levelInsts : Array Term) :
    TermElabM (Array (TSyntax ``Parser.Term.letDecl)) := do
  let mut letDecls := #[]
  for indVal in ctx.typeInfos, auxFunName in ctx.auxFunNames do
    let currArgNames ← mkInductArgNames indVal
    let numParams    := indVal.numParams
    let currIndices  := currArgNames[numParams:]
    let binders      ← mkImplicitBinders currIndices
    let argNamesNew  := argNames[:numParams] ++ currIndices
    let indType      ← mkInductiveApp indVal argNamesNew
    let instName     ← mkFreshUserName `localinst
    let toTypeExpr   ← mkToTypeExpr indVal argNames
    -- Recall that mutually inductive types all use the same universe levels, hence we pass the same ToLevel instances to each aux function.
    let letDecl      ← `(Parser.Term.letDecl| $(mkIdent instName):ident $binders:implicitBinder* : ToExpr $indType :=
                          { toExpr     := $(mkIdent auxFunName) $levelInsts*,
                            toTypeExpr := $toTypeExpr })
    letDecls := letDecls.push letDecl
  return letDecls

open TSyntax.Compat in
/--
Makes a `toExpr` function for the given inductive type.
The implementation of each `toExpr` function for a (mutual) inductive type is given as top-level private definitions.
These are assembled into `ToExpr` instances in `mkInstanceCmds`.
For mutual/nested inductive types, then each of the types' `ToExpr` instances are provided as local instances,
to wire together the recursion (necessitating these auxiliary definitions being `partial`).
-/
def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkHeader ``ToExpr 1 indVal
  /- We make the `ToLevel` instances be explicit here so that we can pass the instances from the instances to the
     aux functions. This lets us ensure universe level variables are being lined up,
     without needing to use `ident.{u₁,…,uₙ}` syntax, which could conditionally be incorrect
     depending on the ambient CommandElabM scope state.
     TODO(kmill): deriving handlers should run in a scope with no `universes` or `variables`. -/
  let (toLevelInsts, levelBinders) := Array.unzip <| ← indVal.levelParams.toArray.mapM fun u => do
    let inst := mkIdent (← mkFreshUserName `inst)
    return (inst, ← `(explicitBinderF| ($inst : ToLevel.{$(mkIdent u)})))
  let mut body ← mkToExprBody header indVal auxFunName toLevelInsts
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx header.argNames toLevelInsts
    body ← mkLet letDecls body
  /- We need to alter the last binder (the one for the "target") to have explicit universe levels
     so that the `ToLevel` instance arguments can use them. -/
  let addLevels binder :=
    match binder with
    | `(bracketedBinderF| ($a : $ty)) => do `(bracketedBinderF| ($a : $(← updateIndType indVal ty)))
    | _ => throwError "(internal error) expecting inst binder"
  let binders := header.binders.pop ++ levelBinders ++ #[← addLevels header.binders.back!]
  if ctx.usePartial then
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Expr := $body:term)
  else
    `(private         def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Expr := $body:term)

/--
Creates all the auxiliary functions (using `mkAuxFunction`) for the (mutual) inductive type(s).
Wraps the resulting definition commands in `mutual ... end`.
-/
def mkAuxFunctions (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

open TSyntax.Compat in
/--
Assuming all of the auxiliary definitions exist,
creates all the `instance` commands for the `ToExpr` instances for the (mutual) inductive type(s).
This is a modified copy of `Lean.Elab.Deriving.mkInstanceCmds` to account for `ToLevel` instances.
-/
def mkInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name) :
    TermElabM (Array Command) := do
  let mut instances := #[]
  for indVal in ctx.typeInfos, auxFunName in ctx.auxFunNames do
    if typeNames.contains indVal.name then
      let argNames     ← mkInductArgNames indVal
      let binders      ← mkImplicitBinders argNames
      let binders      := binders ++ (← mkInstImplicitBinders ``ToExpr indVal argNames)
      let (toLevelInsts, levelBinders) := Array.unzip <| ← indVal.levelParams.toArray.mapM fun u => do
        let inst := mkIdent (← mkFreshUserName `inst)
        return (inst, ← `(instBinderF| [$inst : ToLevel.{$(mkIdent u)}]))
      let binders      := binders ++ levelBinders
      let indType      ← updateIndType indVal (← mkInductiveApp indVal argNames)
      let toTypeExpr   ← mkToTypeExpr indVal argNames
      let instCmd ← `(instance $binders:implicitBinder* : ToExpr $indType where
                        toExpr := $(mkIdent auxFunName) $toLevelInsts*
                        toTypeExpr := $toTypeExpr)
      instances := instances.push instCmd
  return instances

/--
Returns all the commands necessary to construct the `ToExpr` instances.
-/
def mkToExprInstanceCmds (declNames : Array Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "toExpr" declNames[0]!
  let cmds := #[← mkAuxFunctions ctx] ++ (← mkInstanceCmds ctx declNames)
  trace[Elab.Deriving.toExpr] "\n{cmds}"
  return cmds

/--
The main entry point to the `ToExpr` deriving handler.
-/
def mkToExprInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← withFreshMacroScope <| liftTermElabM <| mkToExprInstanceCmds declNames
    -- Enable autoimplicits, used for universe levels.
    withScope (fun scope => { scope with opts := autoImplicit.set scope.opts true }) do
      elabCommand (mkNullNode cmds)
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler ``Lean.ToExpr mkToExprInstanceHandler
  registerTraceClass `Elab.Deriving.toExpr

end Lean.Elab.Deriving.ToExpr
