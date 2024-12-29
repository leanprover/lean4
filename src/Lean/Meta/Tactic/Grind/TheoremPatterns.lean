/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.HeadIndex
import Lean.Util.FoldConsts
import Lean.Meta.Basic
import Lean.Meta.InferType

namespace Lean.Meta.Grind

inductive Origin where
  /-- A global declaration in the environment. -/
  | decl (declName : Name)
  /-- A local hypothesis. -/
  | fvar (fvarId : FVarId)
  /--
  A proof term provided directly to a call to `grind` where `ref`
  is the provided grind argument. The `id` is a unique identifier for the call.
  -/
  | stx (id : Name) (ref : Syntax)
  | other
  deriving Inhabited, Repr

structure TheoremPattern where
  proof       : Expr
  numParams   : Nat
  patterns    : List Expr
  /-- Contains all symbols used in `pattterns`. -/
  symbols     : List HeadIndex
  origin      : Origin
  deriving Inhabited

abbrev TheoremPatterns := SMap Name (List TheoremPattern)

builtin_initialize theoremPatternsExt : SimpleScopedEnvExtension TheoremPattern TheoremPatterns ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s t => Id.run do
      let .const declName :: _ := t.symbols | unreachable!
      if let some ts := s.find? declName then
        s.insert declName (t::ts)
      else
        s.insert declName [t]
    initial  := .empty
  }

-- TODO: create attribute?
private def forbiddenDeclNames := #[``Eq, ``HEq, ``Iff, ``And, ``Or, ``Not]

private def isForbidden (declName : Name) := forbiddenDeclNames.contains declName

private def dontCare := mkConst (Name.mkSimple "[grind_dontcare]")

private def mkGroundPattern (e : Expr) : Expr :=
  mkAnnotation `grind.ground_pat e

private def groundPattern? (e : Expr) : Option Expr :=
  annotation? `grind.ground_pat e

private def isGroundPattern (e : Expr) : Bool :=
  groundPattern? e |>.isSome

private def isAtomicPattern (e : Expr) : Bool :=
  e.isBVar || e == dontCare || isGroundPattern e

partial def ppPattern (pattern : Expr) : MessageData := Id.run do
  if let some e := groundPattern? pattern then
    return m!"`[{e}]"
  else if pattern == dontCare then
    return m!"?"
  else match pattern with
    | .bvar idx => return m!"#{idx}"
    | _ =>
      let mut r := m!"{pattern.getAppFn}"
      for arg in pattern.getAppArgs do
        let mut argFmt ← ppPattern arg
        if !isAtomicPattern arg then
          argFmt := MessageData.paren argFmt
        r := r ++ " " ++ argFmt
      return r

namespace NormalizePattern

structure State where
  symbols    : Array HeadIndex := #[]
  symbolSet  : Std.HashSet HeadIndex := {}
  bvarsFound : Std.HashSet Nat := {}

abbrev M := StateRefT State MetaM

private def saveSymbol (h : HeadIndex) : M Unit := do
  unless (← get).symbolSet.contains h do
    modify fun s => { s with symbols := s.symbols.push h, symbolSet := s.symbolSet.insert h }

private def foundBVar (idx : Nat) : M Bool :=
  return (← get).bvarsFound.contains idx

private def saveBVar (idx : Nat) : M Unit := do
  modify fun s => { s with bvarsFound := s.bvarsFound.insert idx }

private def getPatternFn? (pattern : Expr) : Option Expr :=
  if !pattern.isApp then
    none
  else match pattern.getAppFn with
    | f@(.const declName _) => if isForbidden declName then none else some f
    | f@(.fvar _) => some f
    | _ => none

private structure PatternFunInfo where
  instImplicitMask : Array Bool
  typeMask : Array Bool

private def getPatternFunInfo (f : Expr) (numArgs : Nat) : MetaM PatternFunInfo := do
  forallBoundedTelescope (← inferType f) numArgs fun xs _ => do
    let typeMask ← xs.mapM fun x => isTypeFormer x
    let instImplicitMask ← xs.mapM fun x => return (← x.fvarId!.getDecl).binderInfo matches .instImplicit
    return { typeMask, instImplicitMask }

private partial def go (pattern : Expr) (root := false) : M Expr := do
  if root && !pattern.hasLooseBVars then
    throwError "invalid pattern, it does not have pattern variables"
  let some f := getPatternFn? pattern
    | throwError "invalid pattern, (non-forbidden) application expected"
  assert! f.isConst || f.isFVar
  saveSymbol f.toHeadIndex
  let mut args := pattern.getAppArgs
  let { instImplicitMask, typeMask }  ← getPatternFunInfo f args.size
  for i in [:args.size] do
    let arg := args[i]!
    let isType := typeMask[i]?.getD false
    let isInstImplicit := instImplicitMask[i]?.getD false
    let arg ← if !arg.hasLooseBVars then
      if arg.hasMVar then
        pure dontCare
      else
        pure <| mkGroundPattern arg
    else match arg with
      | .bvar idx =>
        if (isType || isInstImplicit) && (← foundBVar idx) then
          pure dontCare
        else
          saveBVar idx
          pure arg
      | _ =>
        if isType || isInstImplicit then
          pure dontCare
        else if let some _ := getPatternFn? arg then
          go arg
        else
          pure dontCare
    args := args.set! i arg
  return mkAppN f args

def main (patterns : List Expr) : MetaM (List Expr × List HeadIndex) := do
  let (patterns, s) ← patterns.mapM go |>.run {}
  return (patterns, s.symbols.toList)

end NormalizePattern

def addTheoremPattern (declName : Name) (numParams : Nat) (patterns : List Expr) : MetaM Unit := do
  let .thmInfo info ← getConstInfo declName
    | throwError "`{declName}` is not a theorem, you cannot assign patterns to non-theorems for the `grind` tactic"
  let us := info.levelParams.map mkLevelParam
  let proof := mkConst declName us
  let (patterns, symbols) ← NormalizePattern.main patterns
  trace[grind.pattern] "{declName}: {patterns.map ppPattern}"
  theoremPatternsExt.add {
     proof, patterns, numParams, symbols
     origin := .decl declName
  }

end Lean.Meta.Grind
