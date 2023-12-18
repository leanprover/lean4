/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatchPatternAttr
import Lean.Elab.Arg
import Lean.Elab.MatchAltView

namespace Lean.Elab.Term

open Meta

abbrev PatternVar := Syntax  -- TODO: should be `Ident`

/-!
  Patterns define new local variables.
  This module collect them and preprocess `_` occurring in patterns.
  Recall that an `_` may represent anonymous variables or inaccessible terms
  that are implied by typing constraints. Thus, we represent them with fresh named holes `?x`.
  After we elaborate the pattern, if the metavariable remains unassigned, we transform it into
  a regular pattern variable. Otherwise, it becomes an inaccessible term.

  Macros occurring in patterns are expanded before the `collectPatternVars` method is executed.
  The following kinds of Syntax are handled by this module
  - Constructor applications
  - Applications of functions tagged with the `[match_pattern]` attribute
  - Identifiers
  - Anonymous constructors
  - Structure instances
  - Inaccessible terms
  - Named patterns
  - Tuple literals
  - Type ascriptions
  - Literals: num, string and char
-/
namespace CollectPatternVars

/-- State for the pattern variable collector monad. -/
structure State where
  /-- Pattern variables found so far. -/
  found     : NameSet := {}
  /-- Pattern variables found so far as an array. It contains the order they were found. -/
  vars      : Array PatternVar := #[]
  deriving Inhabited

abbrev M := StateRefT State TermElabM

private def throwCtorExpected {α} : M α :=
  throwError "invalid pattern, constructor or constant marked with '[match_pattern]' expected"

private def throwInvalidPattern {α} : M α :=
  throwError "invalid pattern"

/-!
An application in a pattern can be

1- A constructor application
   The elaborator assumes fields are accessible and inductive parameters are not accessible.

2- A regular application `(f ...)` where `f` is tagged with `[match_pattern]`.
   The elaborator assumes implicit arguments are not accessible and explicit ones are accessible.
-/

structure Context where
  funId         : Ident
  ctorVal?      : Option ConstructorVal -- It is `some`, if constructor application
  explicit      : Bool
  ellipsis      : Bool
  paramDecls    : Array (Name × BinderInfo) -- parameters names and binder information
  paramDeclIdx  : Nat := 0
  namedArgs     : Array NamedArg
  args          : List Arg
  newArgs       : Array Term := #[]
  deriving Inhabited

private def isDone (ctx : Context) : Bool :=
  ctx.paramDeclIdx ≥ ctx.paramDecls.size

private def finalize (ctx : Context) : M Syntax := do
  if ctx.namedArgs.isEmpty && ctx.args.isEmpty then
    let fStx ← `(@$(ctx.funId):ident)
    return Syntax.mkApp fStx ctx.newArgs
  else
    throwError "too many arguments"

private def isNextArgAccessible (ctx : Context) : Bool :=
  let i := ctx.paramDeclIdx
  match ctx.ctorVal? with
  | some ctorVal => i ≥ ctorVal.numParams -- For constructor applications only fields are accessible
  | none =>
    if h : i < ctx.paramDecls.size then
      -- For `[match_pattern]` applications, only explicit parameters are accessible.
      let d := ctx.paramDecls.get ⟨i, h⟩
      d.2.isExplicit
    else
      false

private def getNextParam (ctx : Context) : (Name × BinderInfo) × Context :=
  let i := ctx.paramDeclIdx
  let d := ctx.paramDecls[i]!
  (d, { ctx with paramDeclIdx := ctx.paramDeclIdx + 1 })

private def processVar (idStx : Syntax) : M Syntax := do
  unless idStx.isIdent do
    throwErrorAt idStx "identifier expected"
  let id := idStx.getId
  unless id.eraseMacroScopes.isAtomic do
    throwError "invalid pattern variable, must be atomic"
  if (← get).found.contains id then
    throwError "invalid pattern, variable '{id}' occurred more than once"
  modify fun s => { s with vars := s.vars.push idStx, found := s.found.insert id }
  return idStx

private def samePatternsVariables (startingAt : Nat) (s₁ s₂ : State) : Bool :=
  if h : s₁.vars.size = s₂.vars.size then
    Array.isEqvAux s₁.vars s₂.vars h (.==.) startingAt
  else
    false

open TSyntax.Compat in
partial def collect (stx : Syntax) : M Syntax := withRef stx <| withFreshMacroScope do
  let k := stx.getKind
  if k == identKind then
    processId stx
  else if k == ``Lean.Parser.Term.app then
    processCtorApp stx
  else if k == ``Lean.Parser.Term.anonymousCtor then
    let elems ← stx[1].getArgs.mapSepElemsM collect
    return stx.setArg 1 <| mkNullNode elems
  else if k == ``Lean.Parser.Term.dotIdent then
    return stx
  else if k == ``Lean.Parser.Term.hole then
    `(.( $stx ))
  else if k == ``Lean.Parser.Term.syntheticHole then
    `(.( $stx ))
  else if k == ``Lean.Parser.Term.typeAscription then
    -- Ignore type term
    let t := stx[1]
    let t ← collect t
    return stx.setArg 1 t
  else if k == ``Lean.Parser.Term.explicitUniv then
    processCtor stx[0]
  else if k == ``Lean.Parser.Term.namedPattern then
    /- Recall that
      ```
      def namedPattern := check... >> trailing_parser "@" >> optional (atomic (ident >> ":")) >> termParser
      ```
     -/
    let id := stx[0]
    discard <| processVar id
    let h ← if stx[2].isNone then
      `(h)
    else
      pure stx[2][0]
    let pat := stx[3]
    let pat ← collect pat
    discard <| processVar h
    ``(_root_.namedPattern $id $pat $h)
  else if k == ``Lean.Parser.Term.binop then
    let lhs ← collect stx[2]
    let rhs ← collect stx[3]
    return stx.setArg 2 lhs |>.setArg 3 rhs
  else if k == ``Lean.Parser.Term.unop then
    let arg ← collect stx[2]
    return stx.setArg 2 arg
  else if k == ``Lean.Parser.Term.inaccessible then
    return stx
  else if k == strLitKind then
    return stx
  else if k == numLitKind then
    return stx
  else if k == scientificLitKind then
    return stx
  else if k == charLitKind then
    return stx
  else if k == ``Lean.Parser.Term.quotedName || k == ``Lean.Parser.Term.doubleQuotedName then
    return stx
  else if k == choiceKind then
    /- Remark: If there are `Term.structInst` alternatives, we keep only them. This is a hack to get rid of
       Set-like notation in patterns. Recall that in Mathlib `{a, b}` can be a set with two elements or the
       structure instance `{ a := a, b := b }`. Possible alternative solution: add a `pattern` category, or at least register
       the `Syntax` node kinds that are allowed in patterns. -/
    let args :=
      let args := stx.getArgs
      if args.any (·.isOfKind ``Parser.Term.structInst) then
        args.filter (·.isOfKind ``Parser.Term.structInst)
      else
        args
    let stateSaved ← get
    let arg0 ← collect args[0]!
    let stateNew ← get
    let mut argsNew := #[arg0]
    for arg in args[1:] do
      set stateSaved
      argsNew := argsNew.push (← collect arg)
      unless samePatternsVariables stateSaved.vars.size stateNew (← get) do
        throwError "invalid pattern, overloaded notation is only allowed when all alternative have the same set of pattern variables"
    set stateNew
    return mkNode choiceKind argsNew
  else match stx with
  | `({ $[$srcs?,* with]? $fields,* $[..%$ell?]? $[: $ty?]? }) =>
    if let some srcs := srcs? then
      throwErrorAt (mkNullNode srcs) "invalid struct instance pattern, 'with' is not allowed in patterns"
    let fields ← fields.getElems.mapM fun
      | `(Parser.Term.structInstField| $lval:structInstLVal := $val) => do
        let newVal ← collect val
        `(Parser.Term.structInstField| $lval:structInstLVal := $newVal)
      | _ => throwInvalidPattern  -- `structInstFieldAbbrev` should be expanded at this point
    `({ $[$srcs?,* with]? $fields,* $[..%$ell?]? $[: $ty?]? })
  | _ => throwInvalidPattern

where

  processCtorApp (stx : Syntax) : M Syntax := do
    let (f, namedArgs, args, ellipsis) ← expandApp stx
    if f.getKind == ``Parser.Term.dotIdent then
      let namedArgsNew ← namedArgs.mapM fun
        | { ref, name, val := Arg.stx arg } => withRef ref do `(Lean.Parser.Term.namedArgument| ($(mkIdentFrom ref name) := $(← collect arg)))
        | _ => unreachable!
      let mut argsNew ← args.mapM fun | Arg.stx arg => collect arg | _ => unreachable!
      if ellipsis then
        argsNew := argsNew.push (mkNode ``Parser.Term.ellipsis #[mkAtomFrom stx ".."])
      return Syntax.mkApp f (namedArgsNew ++ argsNew)
    else
      processCtorAppCore f namedArgs args ellipsis

  processCtor (stx : Syntax) : M Syntax := do
    processCtorAppCore stx #[] #[] false

  /-- Check whether `stx` is a pattern variable or constructor-like (i.e., constructor or constant tagged with `[match_pattern]` attribute) -/
  processId (stx : Syntax) : M Syntax := do
    match (← resolveId? stx "pattern") with
    | none   => processVar stx
    | some f => match f with
      | Expr.const fName _ =>
        match (← getEnv).find? fName with
        | some (ConstantInfo.ctorInfo _) => processCtor stx
        | some _ =>
          if hasMatchPatternAttribute (← getEnv) fName then
            processCtor stx
          else
            processVar stx
        | none => throwCtorExpected
      | _ => processVar stx

  pushNewArg (accessible : Bool) (ctx : Context) (arg : Arg) : M Context := do
    match arg with
    | Arg.stx stx =>
      let stx ← if accessible then collect stx else pure stx
      return { ctx with newArgs := ctx.newArgs.push stx }
    | _ => unreachable!

  processExplicitArg (accessible : Bool) (ctx : Context) : M Context := do
    match ctx.args with
    | [] =>
      if ctx.ellipsis then
        pushNewArg accessible ctx (Arg.stx (← `(_)))
      else
        throwError "explicit parameter is missing, unused named arguments {ctx.namedArgs.map fun narg => narg.name}"
    | arg::args =>
      pushNewArg accessible { ctx with args := args } arg

  processImplicitArg (accessible : Bool) (ctx : Context) : M Context := do
    if ctx.explicit then
      processExplicitArg accessible ctx
    else
      pushNewArg accessible ctx (Arg.stx (← `(_)))

  processCtorAppContext (ctx : Context) : M Syntax := do
    if isDone ctx then
      finalize ctx
    else
      let accessible := isNextArgAccessible ctx
      let (d, ctx)   := getNextParam ctx
      match ctx.namedArgs.findIdx? fun namedArg => namedArg.name == d.1 with
      | some idx =>
        let arg := ctx.namedArgs[idx]!
        let ctx := { ctx with namedArgs := ctx.namedArgs.eraseIdx idx }
        let ctx ← pushNewArg accessible ctx arg.val
        processCtorAppContext ctx
      | none =>
        let ctx ← match d.2 with
          | BinderInfo.implicit       => processImplicitArg accessible ctx
          | BinderInfo.strictImplicit => processImplicitArg accessible ctx
          | BinderInfo.instImplicit   => processImplicitArg accessible ctx
          | _                         => processExplicitArg accessible ctx
        processCtorAppContext ctx

  processCtorAppCore (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (ellipsis : Bool) : M Syntax := do
    let args := args.toList
    let (fId, explicit) ← match f with
      | `($fId:ident)  => pure (fId, false)
      | `(@$fId:ident) => pure (fId, true)
      | _              => throwError "identifier expected"
    let some (Expr.const fName _) ← resolveId? fId "pattern" (withInfo := true) | throwCtorExpected
    let fInfo ← getConstInfo fName
    let paramDecls ← forallTelescopeReducing fInfo.type fun xs _ => xs.mapM fun x => do
      let d ← getFVarLocalDecl x
      return (d.userName, d.binderInfo)
    match fInfo with
    | ConstantInfo.ctorInfo val =>
      processCtorAppContext
        { funId := fId, explicit := explicit, ctorVal? := val, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
    | _ =>
      if hasMatchPatternAttribute (← getEnv) fName then
        processCtorAppContext
          { funId := fId, explicit := explicit, ctorVal? := none, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
      else
        throwCtorExpected

def main (alt : MatchAltView) : M MatchAltView := do
  let patterns ← alt.patterns.mapM fun p => do
    trace[Elab.match] "collecting variables at pattern: {p}"
    collect p
  return { alt with patterns := patterns }

end CollectPatternVars

/--
Collect pattern variables occurring in the `match`-alternative object views.
It also returns the updated views.
-/
def collectPatternVars (alt : MatchAltView) : TermElabM (Array PatternVar × MatchAltView) := do
  let (alt, s) ← (CollectPatternVars.main alt).run {}
  return (s.vars, alt)

/--
Return the pattern variables in the given pattern.
Remark: this method is not used by the main `match` elaborator, but in the precheck hook and other macros (e.g., at `Do.lean`).
-/
def getPatternVars (patternStx : Syntax) : TermElabM (Array PatternVar) := do
  let patternStx ← liftMacroM <| expandMacros patternStx
  let (_, s) ← (CollectPatternVars.collect patternStx).run {}
  return s.vars

/--
Return the pattern variables occurring in the given patterns.
This method is used in the `match` and `do` notation elaborators
-/
def getPatternsVars (patterns : Array Syntax) : TermElabM (Array PatternVar) := do
  let collect : CollectPatternVars.M Unit := do
    for pattern in patterns do
      discard <| CollectPatternVars.collect (← liftMacroM <| expandMacros pattern)
  let (_, s) ← collect.run {}
  return s.vars

def getPatternVarNames (pvars : Array PatternVar) : Array Name :=
  pvars.map fun x => x.getId

end Lean.Elab.Term
