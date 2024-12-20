/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Tactic.Replace

/-!
# Tactics to manipulate `let` expressions
-/

namespace Lean.Meta

/-!
### `let` extraction

Extracting `let`s means to locate `let`/`letFun`s in a term and to extract them
from the term by extending the local context with new declarations.
-/

/--
Configuration for the `extract_lets` tactic.
-/
structure ExtractLetsConfig where
  /-- If true (default: false), extract lets from subterms that are proofs. -/
  proofs : Bool := false
  /-- If true (default: true), extract lets from subterms that are types. -/
  types : Bool := true
  /-- If true (default: false), extract lets from subterms that are implicit arguments. -/
  implicits : Bool := false
  /-- If false (default: true), extracts only top-level lets, otherwise descends into subterms. -/
  descend : Bool := true
  /-- If true (default: true), descend into forall/lambda/let bodies when extracting. Only relevant when `descend` is true. -/
  underBinder : Bool := true
  /-- If true (default: false), eliminate unused lets rather than extract them. -/
  usedOnly : Bool := false
  /-- If true (default: true), reuse local declarations that have syntactically equal values.
  Note that even when false, the caching strategy for `extract_let`s may result in fewer extracted let bindings than expected. -/
  merge : Bool := true
  /-- If false (default: false), then once `givenNames` is exhausted, stop extracting lets. Otherwise continue extracting lets. -/
  onlyGivenNames : Bool := false

namespace ExtractLets

def containsLet (e : Expr) : Bool :=
  Option.isSome <| e.find? fun e' => e'.isLet || e'.isConstOf ``letFun

structure State where
  /-- Names to use for extracted -/
  givenNames : List Name

  -- fvarSubst : FVarSubst := {}
  decls : Array LocalDecl := #[]
  /-- Cache from `let` values to fvars. To support the `merge` option. -/
  valueCache : ExprStructMap LocalDecl := {}
  deriving Inhabited

abbrev M := ReaderT ExtractLetsConfig <| MonadCacheT ExprStructEq Expr <| StateRefT State MetaM

/-- Gets the next name to use for extracted `let`s -/
def nextName? : M (Option Name) := do
  let s ← get
  match s.givenNames, (← read).onlyGivenNames with
  | n :: ns, _      => set { s with givenNames := ns }; return n
  | []     , true   => return none
  | []     , false  => return `_

-- private def hasNextName? : M Bool := do
--   let s ← get
--   return !s.onlyGivenNames || !s.givenNames.isEmpty

def extractable (fvars : List Expr) (e : Expr) : Bool :=
  !e.hasAnyFVar (fvars.contains <| .fvar ·)

def nextNameForBinderName? (binderName : Name) : M (Option Name) := do
  if let some n ← nextName? then
    if n == `_ then
      let binderName := if binderName.isAnonymous then `a else binderName
      mkFreshUserName binderName
    else
      return n
  else
    return none

def extractableLet (fvars : List Expr) (n : Name) (t v : Expr) : M (Bool × Name) := do
  if extractable fvars t && extractable fvars v then
    if let some n ← nextNameForBinderName? n then
      return (true, n)
  return (false, n)

def withExistingDecl (decl : LocalDecl) (k : M α) : M α := do
  if (← getLCtx).contains decl.fvarId then
    k
  else
    withExistingLocalDecls [decl] k

/--
Extracts lets from `e`.
- `fvars` is an array of all the local variables from going under binders.

Does not handle `descend := false` mode.
-/
partial def extractCore (fvars : List Expr) (e : Expr) : M Expr := do
  let cfg ← read
  if e.isAtomic then
    return e
  else
    checkCache (e : ExprStructEq) fun _ => do
      if !containsLet e then
        return e
      if !cfg.proofs then
        if ← Meta.isProof e then
          return e
      if !cfg.types then
        if ← Meta.isType e then
          return e
      match e with
      | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => unreachable!
      | .mdata _ e'      => return e.updateMData! (← extractCore fvars e')
      | .proj _ _ s      => return e.updateProj! (← extractCore fvars s)
      | .app ..          => extractApp fvars e
      | .letE n t v b _  => extractLetLike fvars n t v b (fun t v b => pure <| e.updateLet! t v b)
      | .lam n t b i     => extractBinder fvars n t b i (fun t b => e.updateLambda! i t b)
      | .forallE n t b i => extractBinder fvars n t b i (fun t b => e.updateForall! i t b)
where
  extractBinder (fvars : List Expr) (n : Name) (t b : Expr) (i : BinderInfo) (mk : Expr → Expr → Expr) : M Expr := do
    let cfg ← read
    let t ← extractCore fvars t
    if cfg.underBinder then
      withLocalDecl n i t fun x => do
        let b ← extractCore (x :: fvars) (b.instantiate1 x)
        return mk t (b.abstract #[x])
    else
      return mk t b
  extractLetLike (fvars : List Expr) (n : Name) (t v b : Expr) (mk : Expr → Expr → Expr → M Expr) : M Expr := do
    let cfg ← read
    if cfg.usedOnly && !b.hasLooseBVars then
      return ← extractCore fvars b
    let t ← extractCore fvars t
    let v ← extractCore fvars v
    if cfg.merge then
      if let some decl := (← get).valueCache.get? v then
        return ← withExistingDecl decl <| extractCore fvars (b.instantiate1 decl.toExpr)
    let (extract, n) ← extractableLet fvars n t v
    if !extract && !cfg.underBinder then
      return ← mk t v b
    withLetDecl n t v fun x => do
      let decl ← x.fvarId!.getDecl
      if extract then
        modify fun s => { s with
          decls := s.decls.push decl
          valueCache := if cfg.merge then s.valueCache.insert v decl else s.valueCache
        }
        extractCore fvars (b.instantiate1 x)
      else
        let b ← extractCore (x :: fvars) (b.instantiate1 x)
        mk t v (b.abstract #[x])
  extractApp (fvars : List Expr) (e : Expr) : M Expr := do
    let cfg ← read
    let mut f := e.getAppFn
    let mut args := e.getAppArgs
    let f' ←
      if f.isConstOf ``letFun && 4 ≤ args.size then
        f := mkAppN f args[0:4]
        let (n, t, v, b) := f.letFun?.get!
        args := args[4:]
        -- TODO: Can be more efficient than using `mkLetFun`
        extractLetLike fvars n t v b (fun t v b => withLetDecl n t v fun x => mkLetFun x v (b.instantiate1 x))
      else
        extractCore fvars f
    let mut fty ← inferType f
    let mut j := 0
    for i in [0:args.size] do
      unless fty.isForall do
        fty ← withTransparency .all <| whnf (fty.instantiateRevRange j i args)
        j := i
      let .forallE _ _ fty' bi := fty | failure
      fty := fty'
      if bi.isExplicit || cfg.implicits then
        args := args.set! i <| ← extractCore fvars (args[i]!)
    return mkAppN f' args

end ExtractLets

/--
Implementation of the `extractLets` function.
- `e` is a term that is valid in the current local context.
- `k` is a callback that is run in the updated local context with all relevant `let`s extracted.
-/
private def extractLetsAux (e : Expr) (givenNames : List Name) (k : Expr → MetaM α) (config : ExtractLetsConfig := {}) : MetaM α := do
  let (e, s) ← ExtractLets.extractCore [] e |>.run config |>.run' {} |>.run { givenNames }
  withExistingLocalDecls s.decls.toList (k e)

end Lean.Meta
