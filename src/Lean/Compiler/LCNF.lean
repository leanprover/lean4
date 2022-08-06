/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Transform
import Lean.Compiler.InlineAttrs
import Lean.Compiler.CompilerM

namespace Lean.Compiler
/-!
# Lean Compiler Normal Form (LCNF)

It is based on the [A-normal form](https://en.wikipedia.org/wiki/A-normal_form),
and the approach described in the paper
[Compiling  without continuations](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/compiling-without-continuations.pdf).
-/

/--
Return `true` if `e` is a `lcProof` application.
Recall that we use `lcProof` to erase all nested proofs.
-/
def isLCProof (e : Expr) : Bool :=
  e.isAppOfArity ``lcProof 1

/--
Recursors, noConfusion, constructors, and matchers are not treated as regular
functions by the code generator. We eta-expand all of them to make sure they are
not partially applied.
-/
def shouldEtaExpand (declName : Name) : CoreM Bool := do
  let env ← getEnv
  if isCasesOnRecursor env declName then return true
  if isNoConfusion env declName then return true
  if (← isRec declName) then return true
  if (← Meta.isMatcher declName) then return true
  if env.isConstructor declName then return true
  if declName == ``Quot.lift then return true
  return false

/--
Return `true` if `mdata` should be preserved.
Right now, we don't preserve any `MData`, but this may
change in the future when we add support for debugging information
-/
def isCompilerRelevantMData (_mdata : MData) : Bool :=
  false

/--
Inline constants tagged with the `[macroInline]` attribute occurring in `e`.
-/
def macroInline (e : Expr) : CoreM Expr :=
  Core.transform e fun e => do
    let .const declName us := e.getAppFn | return .visit e
    unless hasMacroInlineAttribute (← getEnv) declName do return .visit e
    let val ← Core.instantiateValueLevelParams (← getConstInfo declName) us
    return .visit <| val.beta e.getAppArgs

namespace ToLCNF

structure Context where
  root : Bool

structure State where
  cache     : ExprMap Expr := {}

abbrev M := ReaderT Context $ StateRefT State CompilerM

def mkFreshLetDecl (e : Expr) : M Expr := do
  if (← read).root then
    return e
  else
    mkLetDecl (← mkFreshUserName `x) (← inferType e) e (nonDep := false)

def withNewRoot (x : M α) : M α := do
  let s ← get
  try
    withReader (fun _ => { root := true }) <| Compiler.withNewScope x
  finally
    set s

/--
Put the given expression in `LCNF`.

- Nested proofs are replaced with `lcProof`-applications.
- Eta-expand applications of declarations that satisfy `shouldEtaExpand`.
- Put computationally relevant expressions in A-normal form.
-/
partial def toLCNF (lctx : LocalContext) (e : Expr) : CoreM Expr := do
  let ((e, _), s) ← visit e |>.run { root := true } |>.run {} |>.run { lctx }
  return s.lctx.mkLambda s.letFVars e
where
  visitChild (e : Expr) : M Expr :=
    withReader (fun _ => { root := false }) <| visit e

  visitApp (f : Expr) (args : Array Expr) : M Expr := do
    -- TODO: handle special cases
    let f := f
    let args ← args.mapM visitChild
    mkFreshLetDecl <| mkAppN f args

  visitLambda (e : Expr) : M Expr := do
    let r ← withNewRoot do
      let (as, e) ← Compiler.visitLambda e
      let e ← mkLetUsingScope (← visit e)
      mkLambda as e
    mkFreshLetDecl r

  visitMData (mdata : MData) (e : Expr) : M Expr := do
    if isCompilerRelevantMData mdata then
      mkFreshLetDecl <| .mdata mdata (← visitChild e)
    else
      visit e

  visitProj (s : Name) (i : Nat) (e : Expr) : M Expr := do
    mkFreshLetDecl <| .proj s i (← visitChild e)

  visit (e : Expr) : M Expr := withIncRecDepth do
    match e with
    | .mvar .. => throwError "unexpected occurrence of metavariable in code generator{indentExpr e}"
    | .bvar .. => unreachable!
    | .fvar .. | .sort .. | .forallE .. => return e -- Do nothing
    | _ =>
    if isLCProof e then
      return e
    let type ← inferType e
    if (← isProp type) then
      /- We replace proofs with `lcProof` applications. -/
      return mkApp (mkConst ``lcProof) type
    if (← isTypeFormerType type) then
      /- Types and Type formers are not put into A-normal form. -/
      return e
    if let some e := (← get).cache.find? e then
      return e
    let r ← match e with
      | .app ..     => e.withApp fun f args => visitApp f args
      | .const ..   => visitApp e #[]
      | .proj s i e => visitProj s i e
      | .mdata d e  => visitMData d e
      | .lam ..     => visitLambda e
      | .letE ..    => visit (← visitLet e visitChild)
      | .lit ..     => mkFreshLetDecl e
      | _           => pure e
    modify fun s => { s with cache := s.cache.insert e r }
    return r

end ToLCNF

end Lean.Compiler