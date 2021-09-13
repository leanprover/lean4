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

inductive PatternVar where
  | localVar     (userName : Name)
  -- anonymous variables (`_`) are encoded using metavariables
  | anonymousVar (mvarId   : MVarId)

instance : ToString PatternVar := ⟨fun
  | PatternVar.localVar x          => toString x
  | PatternVar.anonymousVar mvarId => s!"?m{mvarId.name}"⟩

/--
  Create an auxiliary Syntax node wrapping a fresh metavariable id.
  We use this kind of Syntax for representing `_` occurring in patterns.
  The metavariables are created before we elaborate the patterns into `Expr`s. -/
private def mkMVarSyntax : TermElabM Syntax := do
  let mvarId ← mkFreshId
  return Syntax.node `MVarWithIdKind #[Syntax.node mvarId #[]]

/-- Given a syntax node constructed using `mkMVarSyntax`, return its MVarId -/
def getMVarSyntaxMVarId (stx : Syntax) : MVarId :=
  { name := stx[0].getKind }

/-
  Patterns define new local variables.
  This module collect them and preprocess `_` occurring in patterns.
  Recall that an `_` may represent anonymous variables or inaccessible terms
  that are implied by typing constraints. Thus, we represent them with fresh named holes `?x`.
  After we elaborate the pattern, if the metavariable remains unassigned, we transform it into
  a regular pattern variable. Otherwise, it becomes an inaccessible term.

  Macros occurring in patterns are expanded before the `collectPatternVars` method is executed.
  The following kinds of Syntax are handled by this module
  - Constructor applications
  - Applications of functions tagged with the `[matchPattern]` attribute
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

structure State where
  found     : NameSet := {}
  vars      : Array PatternVar := #[]

abbrev M := StateRefT State TermElabM

private def throwCtorExpected {α} : M α :=
  throwError "invalid pattern, constructor or constant marked with '[matchPattern]' expected"

private def getNumExplicitCtorParams (ctorVal : ConstructorVal) : TermElabM Nat :=
  forallBoundedTelescope ctorVal.type ctorVal.numParams fun ps _ => do
    let mut result := 0
    for p in ps do
      let localDecl ← getLocalDecl p.fvarId!
      if localDecl.binderInfo.isExplicit then
        result := result+1
    pure result

private def throwInvalidPattern {α} : M α :=
  throwError "invalid pattern"

/-
An application in a pattern can be

1- A constructor application
   The elaborator assumes fields are accessible and inductive parameters are not accessible.

2- A regular application `(f ...)` where `f` is tagged with `[matchPattern]`.
   The elaborator assumes implicit arguments are not accessible and explicit ones are accessible.
-/

structure Context where
  funId         : Syntax
  ctorVal?      : Option ConstructorVal -- It is `some`, if constructor application
  explicit      : Bool
  ellipsis      : Bool
  paramDecls    : Array (Name × BinderInfo) -- parameters names and binder information
  paramDeclIdx  : Nat := 0
  namedArgs     : Array NamedArg
  args          : List Arg
  newArgs       : Array Syntax := #[]
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
      -- For `[matchPattern]` applications, only explicit parameters are accessible.
      let d := ctx.paramDecls.get ⟨i, h⟩
      d.2.isExplicit
    else
      false

private def getNextParam (ctx : Context) : (Name × BinderInfo) × Context :=
  let i := ctx.paramDeclIdx
  let d := ctx.paramDecls[i]
  (d, { ctx with paramDeclIdx := ctx.paramDeclIdx + 1 })

private def processVar (idStx : Syntax) : M Syntax := do
  unless idStx.isIdent do
    throwErrorAt idStx "identifier expected"
  let id := idStx.getId
  unless id.eraseMacroScopes.isAtomic do
    throwError "invalid pattern variable, must be atomic"
  if (← get).found.contains id then
    throwError "invalid pattern, variable '{id}' occurred more than once"
  modify fun s => { s with vars := s.vars.push (PatternVar.localVar id), found := s.found.insert id }
  return idStx

private def nameToPattern : Name → TermElabM Syntax
  | Name.anonymous => `(Name.anonymous)
  | Name.str p s _ => do let p ← nameToPattern p; `(Name.str $p $(quote s) _)
  | Name.num p n _ => do let p ← nameToPattern p; `(Name.num $p $(quote n) _)

private def quotedNameToPattern (stx : Syntax) : TermElabM Syntax :=
  match stx[0].isNameLit? with
  | some val => nameToPattern val
  | none     => throwIllFormedSyntax

private def doubleQuotedNameToPattern (stx : Syntax) : TermElabM Syntax := do
  nameToPattern (← resolveGlobalConstNoOverloadWithInfo stx[2])

partial def collect (stx : Syntax) : M Syntax := withRef stx <| withFreshMacroScope do
  let k := stx.getKind
  if k == identKind then
    processId stx
  else if k == ``Lean.Parser.Term.app then
    processCtorApp stx
  else if k == ``Lean.Parser.Term.anonymousCtor then
    let elems ← stx[1].getArgs.mapSepElemsM collect
    return stx.setArg 1 <| mkNullNode elems
  else if k == ``Lean.Parser.Term.structInst then
    /-
    ```
    leading_parser "{" >> optional (atomic (termParser >> " with "))
                >> manyIndent (group (structInstField >> optional ", "))
                >> optional ".."
                >> optional (" : " >> termParser)
                >> " }"
    ```
    -/
    let withMod := stx[1]
    unless withMod.isNone do
      throwErrorAt withMod "invalid struct instance pattern, 'with' is not allowed in patterns"
    let fields ← stx[2].getArgs.mapM fun p => do
        -- p is of the form (group (structInstField >> optional ", "))
        let field := p[0]
        -- leading_parser structInstLVal >> " := " >> termParser
        let newVal ← collect field[2]
        let field := field.setArg 2 newVal
        pure <| field.setArg 0 field
    return stx.setArg 2 <| mkNullNode fields
  else if k == ``Lean.Parser.Term.hole then
    let r ← mkMVarSyntax
    modify fun s => { s with vars := s.vars.push <| PatternVar.anonymousVar <| getMVarSyntaxMVarId r }
    return r
  else if k == ``Lean.Parser.Term.paren then
    let arg := stx[1]
    if arg.isNone then
      return stx -- `()`
    else
      let t := arg[0]
      let s := arg[1]
      if s.isNone || s[0].getKind == ``Lean.Parser.Term.typeAscription then
        -- Ignore `s`, since it empty or it is a type ascription
        let t ← collect t
        let arg := arg.setArg 0 t
        return stx.setArg 1 arg
      else
        return stx
  else if k == ``Lean.Parser.Term.explicitUniv then
    processCtor stx[0]
  else if k == ``Lean.Parser.Term.namedPattern then
    /- Recall that
      def namedPattern := check... >> trailing_parser "@" >> termParser -/
    let id := stx[0]
    discard <| processVar id
    let pat := stx[2]
    let pat ← collect pat
    `(_root_.namedPattern $id $pat)
  else if k == ``Lean.Parser.Term.binop then
    let lhs ← collect stx[2]
    let rhs ← collect stx[3]
    return stx.setArg 2 lhs |>.setArg 3 rhs
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
  else if k == ``Lean.Parser.Term.quotedName then
    /- Quoted names have an elaboration function associated with them, and they will not be macro expanded.
      Note that macro expansion is not a good option since it produces a term using the smart constructors `Name.mkStr`, `Name.mkNum`
      instead of the constructors `Name.str` and `Name.num` -/
    quotedNameToPattern stx
  else if k == ``Lean.Parser.Term.doubleQuotedName then
    /- Similar to previous case -/
    doubleQuotedNameToPattern stx
  else if k == choiceKind then
    throwError "invalid pattern, notation is ambiguous"
  else
    throwInvalidPattern

where

  processCtorApp (stx : Syntax) : M Syntax := do
    let (f, namedArgs, args, ellipsis) ← expandApp stx true
    processCtorAppCore f namedArgs args ellipsis

  processCtor (stx : Syntax) : M Syntax := do
    processCtorAppCore stx #[] #[] false

  /- Check whether `stx` is a pattern variable or constructor-like (i.e., constructor or constant tagged with `[matchPattern]` attribute) -/
  processId (stx : Syntax) : M Syntax := do
    match (← resolveId? stx "pattern" (withInfo := true)) with
    | none   => processVar stx
    | some f => match f with
      | Expr.const fName _ _ =>
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
        let arg := ctx.namedArgs[idx]
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
    let some (Expr.const fName _ _) ← resolveId? fId "pattern" (withInfo := true) | throwCtorExpected
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

def collectPatternVars (alt : MatchAltView) : TermElabM (Array PatternVar × MatchAltView) := do
  let (alt, s) ← (CollectPatternVars.main alt).run {}
  return (s.vars, alt)

/- Return the pattern variables in the given pattern.
   Remark: this method is not used by the main `match` elaborator, but in the precheck hook and other macros (e.g., at `Do.lean`). -/
def getPatternVars (patternStx : Syntax) : TermElabM (Array PatternVar) := do
  let patternStx ← liftMacroM <| expandMacros patternStx
  let (_, s) ← (CollectPatternVars.collect patternStx).run {}
  return s.vars

def getPatternsVars (patterns : Array Syntax) : TermElabM (Array PatternVar) := do
  let collect : CollectPatternVars.M Unit := do
    for pattern in patterns do
      discard <| CollectPatternVars.collect (← liftMacroM <| expandMacros pattern)
  let (_, s) ← collect.run {}
  return s.vars

def getPatternVarNames (pvars : Array PatternVar) : Array Name :=
  pvars.filterMap fun
    | PatternVar.localVar x => some x
    | _ => none

end Lean.Elab.Term
