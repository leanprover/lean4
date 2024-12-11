/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.ToExpr
import Lean.ToLevel


/-!
# A `ToExpr` derive handler

This module defines a `ToExpr` derive handler for inductive types. It supports mutually inductive
types as well.

The `ToExpr` derive handlers support universe level polymorphism. This is implemented using the
`Lean.ToLevel` class. To use `ToExpr` in places where there is universe polymorphism, make sure
to have a `[ToLevel.{u}]` instance available.

Implementation note: this derive handler was originally modeled after the `Repr` derive handler.
-/

namespace Lean.Elab.Deriving.ToExpr

open Lean Elab Lean.Parser.Term
open Meta Command Deriving

/-- Specialization of `Lean.Elab.Deriving.mkHeader` for `ToExpr`. -/
def mkToExprHeader (indVal : InductiveVal) : TermElabM Header := do
  -- The auxiliary functions we produce are `indtype -> Expr`.
  let header ← mkHeader ``ToExpr 1 indVal
  return header

/-- Give a term that is equivalent to `(term| mkAppN $f #[$args,*])`.
As an optimization, `mkAppN` is pre-expanded out to use `Expr.app` directly. -/
def mkAppNTerm (f : Term) (args : Array Term) : MetaM Term :=
  args.foldlM (fun a b => `(Expr.app $a $b)) f

/-- Create the body of the `toExpr` function
for the `ToExpr` instance, which is a `match` expression
that calls `toExpr` and `toTypeExpr` to assemble an expression for a given term.
For recursive inductive types, `auxFunName` refers to the `ToExpr` instance
for the current type.
For mutually recursive types, we rely on the local instances set up by `mkLocalInstanceLetDecls`. -/
def mkToExprBody (header : Header) (indVal : InductiveVal) (auxFunName : Name) :
    TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  /-- Create the `match` cases, one per constructor. -/
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patterns := #[]
        -- add `_` pattern for indices
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        let mut rhsArgs : Array Term := #[]
        let mkArg (x : Expr) (a : Term) : TermElabM Term := do
          if (← inferType x).isAppOf indVal.name then
            `($(mkIdent auxFunName) $a)
          else if ← Meta.isType x then
            `(toTypeExpr $a)
          else
            `(toExpr $a)
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
        let levels ← indVal.levelParams.toArray.mapM (fun u => `(toLevel.{$(mkIdent u)}))
        let rhs : Term ←
          mkAppNTerm (← `(Expr.const $(quote ctorInfo.name) [$levels,*])) rhsArgs
        `(matchAltExpr| | $[$patterns:term],* => $rhs)
      alts := alts.push alt
    return alts

/-- Create the body of the `toTypeExpr` function for the `ToExpr` instance.
Calls `toExpr` and `toTypeExpr` to the arguments to the type constructor. -/
def mkToTypeExpr (argNames : Array Name) (indVal : InductiveVal) : TermElabM Term := do
  let levels ← indVal.levelParams.toArray.mapM (fun u => `(toLevel.{$(mkIdent u)}))
  forallTelescopeReducing indVal.type fun xs _ => do
    let mut args : Array Term := #[]
    for i in [:xs.size] do
      let x := xs[i]!
      let a := mkIdent argNames[i]!
      if ← Meta.isType x then
        args := args.push <| ← `(toTypeExpr $a)
      else
        args := args.push <| ← `(toExpr $a)
    mkAppNTerm (← `((Expr.const $(quote indVal.name) [$levels,*]))) args

/--
For mutually recursive inductive types, the strategy is to have local `ToExpr` instances in scope
for each of the inductives when defining each instance.
This way, each instance can freely use `toExpr` and `toTypeExpr` for each of the other types.

Note that each instance gets its own definition of each of the others' `toTypeExpr` fields.
(This is working around the fact that the `Deriving.Context` API assumes
that each instance in mutual recursion only has a single auxiliary definition.
There are other ways to work around it, but `toTypeExpr` implementations
are very simple, so duplicating them seemed to be OK.) -/
def mkLocalInstanceLetDecls (ctx : Deriving.Context) (argNames : Array Name) :
    TermElabM (Array (TSyntax ``Parser.Term.letDecl)) := do
  let mut letDecls := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]!
    let auxFunName   := ctx.auxFunNames[i]!
    let currArgNames ← mkInductArgNames indVal
    let numParams    := indVal.numParams
    let currIndices  := currArgNames[numParams:]
    let binders      ← mkImplicitBinders currIndices
    let argNamesNew  := argNames[:numParams] ++ currIndices
    let indType      ← mkInductiveApp indVal argNamesNew
    let instName     ← mkFreshUserName `localinst
    let toTypeExpr   ← mkToTypeExpr argNames indVal
    let letDecl      ← `(Parser.Term.letDecl| $(mkIdent instName):ident $binders:implicitBinder* :
                            ToExpr $indType :=
                          { toExpr := $(mkIdent auxFunName), toTypeExpr := $toTypeExpr })
    letDecls := letDecls.push letDecl
  return letDecls

/-- Fix the output of `mkInductiveApp` to explicitly reference universe levels. -/
def fixIndType (indVal : InductiveVal) (t : Term) : TermElabM Term :=
  match t with
  | `(@$f $args*) =>
    let levels := indVal.levelParams.toArray.map mkIdent
    `(@$f.{$levels,*} $args*)
  | _ => throwError "(internal error) expecting output of `mkInductiveApp`"

/-- Make `ToLevel` instance binders for all the level variables. -/
def mkToLevelBinders (indVal : InductiveVal) : TermElabM (TSyntaxArray ``instBinderF) := do
  indVal.levelParams.toArray.mapM (fun u => `(instBinderF| [ToLevel.{$(mkIdent u)}]))

open TSyntax.Compat in
/-- Make a `toExpr` function for the given inductive type.
The implementations of each `toExpr` function for a (mutual) inductive type
are given as top-level private definitions.
These end up being assembled into `ToExpr` instances in `mkInstanceCmds`.
For mutual inductive types,
then each of the other types' `ToExpr` instances are provided as local instances,
to wire together the recursion (this necessitates these auxiliary definitions being `partial`). -/
def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkToExprHeader indVal
  let mut body   ← mkToExprBody header indVal auxFunName
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx header.argNames
    body ← mkLet letDecls body
  -- We need to alter the last binder (the one for the "target") to have explicit universe levels
  -- so that the `ToLevel` instance arguments can use them.
  let addLevels binder :=
    match binder with
    | `(bracketedBinderF| ($a : $ty)) => do `(bracketedBinderF| ($a : $(← fixIndType indVal ty)))
    | _ => throwError "(internal error) expecting inst binder"
  let binders := header.binders.pop
    ++ (← mkToLevelBinders indVal)
    ++ #[← addLevels header.binders.back!]
  let levels := indVal.levelParams.toArray.map mkIdent
  if ctx.usePartial then
    `(private partial def $(mkIdent auxFunName):ident.{$levels,*} $binders:bracketedBinder* :
        Expr := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident.{$levels,*} $binders:bracketedBinder* :
        Expr := $body:term)

/-- Create all the auxiliary functions using `mkAuxFunction` for the (mutual) inductive type(s).
Wraps the resulting definition commands in `mutual ... end`. -/
def mkMutualBlock (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

open TSyntax.Compat in
/-- Assuming all of the auxiliary definitions exist, create all the `instance` commands
for the `ToExpr` instances for the (mutual) inductive type(s). -/
def mkInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name) :
    TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName   := ctx.auxFunNames[i]!
      let argNames     ← mkInductArgNames indVal
      let binders      ← mkImplicitBinders argNames
      let binders      := binders ++ (← mkInstImplicitBinders ``ToExpr indVal argNames)
      let binders      := binders ++ (← mkToLevelBinders indVal)
      let indType      ← fixIndType indVal (← mkInductiveApp indVal argNames)
      let toTypeExpr   ← mkToTypeExpr argNames indVal
      let levels       := indVal.levelParams.toArray.map mkIdent
      let instCmd ← `(instance $binders:implicitBinder* : ToExpr $indType where
                        toExpr := $(mkIdent auxFunName).{$levels,*}
                        toTypeExpr := $toTypeExpr)
      instances := instances.push instCmd
  return instances

/-- Returns all the commands generated by `mkMutualBlock` and `mkInstanceCmds`. -/
def mkToExprInstanceCmds (declNames : Array Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "toExpr" declNames[0]!
  let cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx declNames)
  trace[Elab.Deriving.toExpr] "\n{cmds}"
  return cmds

/-- The main entry point to the `ToExpr` derive handler. -/
def mkToExprInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← liftTermElabM <| mkToExprInstanceCmds declNames
    cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler ``Lean.ToExpr mkToExprInstanceHandler
  registerTraceClass `Elab.Deriving.toExpr

end Lean.Elab.Deriving.ToExpr
