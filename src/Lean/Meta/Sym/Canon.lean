/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.ExprPtr
import Lean.Meta.SynthInstance
import Lean.Meta.Sym.SynthInstance
import Lean.Meta.IntInstTesters
import Lean.Meta.NatInstTesters
import Lean.Meta.Sym.Eta
import Lean.Meta.WHNF
import Init.Grind.Util
namespace Lean.Meta.Sym
namespace Canon

builtin_initialize registerTraceClass `sym.debug.canon

/-!
# Type-directed canonicalizer

Canonicalizes expressions by normalizing types and instances. At the top level, it traverses
applications, foralls, lambdas, and let-bindings, classifying each argument as a type, instance,
implicit, or value using `shouldCanon`. Targeted reductions (projection, match/ite/cond, Nat
arithmetic) are applied to all positions; instances are re-synthesized.

**Note about types:** `grind` is not built for reasoning about types that are not propositions.
We assume that definitionally equal types will be structurally identical after we apply the
canonicalizer. We also erase most of the subsingleton markers occurring inside types.

## Reductions

It also normalizes expressions using the following reductions. We can view it as a cheap/custom `dsimp`.
We used to reduce only terms inside types, but it restricted important normalizations that were important
when, for example, a term had a forward dependency. That is, the term is not directly in a type, but
there is a type that depends on it.

- **Eta**: `fun x => f x` → `f`
- **Projection**: `⟨a, b⟩.1` → `a` (structure projections, not class projections)
- **Match/ite/cond**: reduced when discriminant is a constructor or literal
- **Nat arithmetic**: ground evaluation (`2 + 1` → `3`) and offset normalization
  (`n.succ + 1` → `n + 2`)

**Note**: Eta is applied only if the lambda is occurring inside of a type. For lambdas occurring
in non type positions, we want to leverage the support in `grind` for lambda-expressions.

## Instance canonicalization

Instances are re-synthesized via `synthInstance`. The instance type is first normalized
using the type-level reductions above, so that `OfNat (Fin (2+1)) 0` and `OfNat (Fin 3) 0`
produce the same canonical instance. Two special cases:

- **`Decidable` instances** (`Grind.nestedDecidable`): the proposition is recursively
  canonicalized, then the `Decidable` instance is re-synthesized. If resynthesis fails,
  the original instance is kept (users often provide these via `haveI`).
  A `checkDefEqInst` guard is required because structurally different `Decidable` instances
  are not necessarily definitionally equal.

- **Propositional instances** (`Grind.nestedProof`): the proposition is recursively
  canonicalized, then the proof is re-synthesized. If resynthesis fails, the original
  proof is kept. No definitional-equality check is needed thanks to proof irrelevance.

In both cases, resynthesis failure is silent — the original instance or proof is kept.
Ideally we would report an issue when resynthesis fails inside a type (where structural
agreement matters most), but in practice users provide non-synthesizable instances via `haveI`,
and these instances propagate into types through forward dependencies. Reporting failures
for such instances produces noise that obscures real issues.

## Two caches

The canonicalizer maintains separate caches for type-level and value-level contexts.
The same expression may canonicalize differently depending on whether it appears in a
type position (where reductions are applied) or a value position (where it is only traversed).
Caches are keyed by `Expr` (structural equality), not pointer equality, because
the canonicalizer runs before `shareCommon` and enters binders using locally nameless
representation.

## Future work

If needed we should add support for user-defined extensions.
-/

structure Context where
  /-- `true` if we are visiting a type. -/
  insideType : Bool := false

abbrev CanonM := ReaderT Context SymM

/--
Auxiliary function for normalizing the arguments of `OfNat.ofNat` during canonicalization.
This is needed because satellite solvers create `Nat` and `Int` numerals using the
APIs `mkNatLit` and `mkIntLit`, which produce terms of the form
`@OfNat.ofNat Nat <num> inst` and `@OfNat.ofNat Int <num> inst`.
This becomes a problem when a term in the input goal has already been canonicalized
and its type is not exactly `Nat` or `Int`. For example, in issue #9477, we have:
```
structure T where
upper_bound : Nat
def T.range (a : T) := 0...a.upper_bound
theorem range_lower (a : T) : a.range.lower = 0 := by rfl
```
Here, the `0` in `range_lower` is actually represented as:
```
(@OfNat.ofNat
  (Std.PRange.Bound (Std.PRange.RangeShape.lower (Std.PRange.RangeShape.mk Std.PRange.BoundShape.closed Std.PRange.BoundShape.open)) Nat)
  (nat_lit 0)
  (instOfNatNat (nat_lit 0)))
```
Without this normalization step, the satellite solver would need to handle multiple
representations for `(0 : Nat)` and `(0 : Int)`, complicating reasoning.
-/
-- Remark: This is not a great solution. We should consider writing a custom canonicalizer for
-- `OfNat.ofNat` and other constants with built-in support in `grind`.
private def normOfNatArgs? (args : Array Expr) : MetaM (Option (Array Expr)) := do
  if h : args.size = 3 then
    let mut args : Vector Expr 3 := h ▸ args.toVector
    let mut modified := false
    if args[1].isAppOf ``OfNat.ofNat then
      -- If nested `OfNat.ofNat`, convert to raw nat literal
      let some val ← getNatValue? args[1] | pure ()
      args := args.set 1 (mkRawNatLit val)
      modified := true
    let inst := args[2]
    if (← Structural.isInstOfNatNat inst) && !args[0].isConstOf ``Nat then
      return some (args.set 0 Nat.mkType |>.toArray)
    else if (← Structural.isInstOfNatInt inst) && !args[0].isConstOf ``Int then
      return some (args.set 0 Int.mkType |>.toArray)
    else if modified then
      return some args.toArray
  return none

abbrev withCaching (e : Expr) (k : CanonM Expr) : CanonM Expr := do
  if (← read).insideType then
    if let some r := (← get).canon.cacheInType.get? e then
      return r
    else
      let r ← k
      modify fun s => { s with canon.cacheInType := s.canon.cacheInType.insert e r }
      return r
  else
    if let some r := (← get).canon.cache.get? e then
      return r
    else
      let r ← k
      modify fun s => { s with canon.cache := s.canon.cache.insert e r }
      return r

def isTrueCond (e : Expr) : Bool :=
  match_expr e with
  | True => true
  | Eq _ a b => a.isBoolTrue && b.isBoolTrue
  | _ => false

def isFalseCond (e : Expr) : Bool :=
  match_expr e with
  | False => true
  | Eq _ a b => a.isBoolFalse && b.isBoolTrue
  | _ => false

/--
Return type for the `shouldCanon` function.
-/
inductive ShouldCanonResult where
  | /- Nested types (and type formers) are canonicalized. -/
    canonType
  | /- Nested instances are canonicalized. -/
    canonInst
  | /- Implicit argument that is not an instance nor a type. -/
    canonImplicit
  | /-
    Term is not a proof, type (former), nor an instance.
    Thus, it must be recursively visited by the canonicalizer.
    -/
    visit
  deriving Inhabited

instance : Repr ShouldCanonResult where
  reprPrec r _ := private match r with
    | .canonType => "canonType"
    | .canonInst => "canonInst"
    | .canonImplicit => "canonImplicit"
    | .visit => "visit"

/--
See comments at `ShouldCanonResult`.
-/
def shouldCanon (pinfos : Array ParamInfo) (i : Nat) (arg : Expr) : MetaM ShouldCanonResult := do
  if h : i < pinfos.size then
    let pinfo := pinfos[i]
    if pinfo.isInstance then
      return .canonInst
    else if pinfo.isProp then
      return .visit
    else if pinfo.isImplicit then
      if (← isTypeFormer arg) then
        return .canonType
      else
        return .canonImplicit
  if (← isProp arg) then
    return .visit
  else if (← isTypeFormer arg) then
    return .canonType
  else
    return .visit

/--
Reduce a projection function application (e.g., `@Sigma.fst _ _ ⟨a, b⟩` → `a`).
Class projections are not reduced — they are support elements handled by instance synthesis.
-/
def reduceProjFn? (info : ProjectionFunctionInfo) (e : Expr) : SymM (Option Expr) := do
  if info.fromClass then
    return none
  let some e ← unfoldDefinition? e | return none
  match (← reduceProj? e.getAppFn) with
  | some f => return some <| mkAppN f e.getAppArgs
  | none   => return none

def isNat (e : Expr) := e.isConstOf ``Nat

/-- Returns `true` if `e` is a Nat arithmetic expression that should be normalized
(ground evaluation or offset normalization). -/
def isNatArithApp (e : Expr) : Bool :=
  match_expr e with
  | Nat.zero => true
  | Nat.succ _ => true
  | HAdd.hAdd α _ _ _ _ _ => isNat α
  | HMul.hMul α _ _ _ _ _ => isNat α
  | HSub.hSub α _ _ _ _ _ => isNat α
  | HDiv.hDiv α _ _ _ _ _ => isNat α
  | HMod.hMod α _ _ _ _ _ => isNat α
  | _ => false

/-- Check that `e` is definitionally equal to `inst` at instance transparency.
Returns `inst` on success, `e` with a reported issue on failure. -/
def checkDefEqInst (e : Expr) (inst : Expr) : SymM Expr := do
  unless (← isDefEqI e inst) do
    reportIssue! "failed to canonicalize instance{indentExpr e}\nsynthesized instance is not definitionally equal{indentExpr inst}"
    return e
  return inst

/-- Canonicalize `e`. Applies targeted reductions and re-synthesizes instances. -/
partial def canon (e : Expr) : CanonM Expr := do
  match e with
  | .forallE ..    => withCaching e <| canonForall #[] e
  | .lam ..        => withCaching e <| canonLambda e
  | .letE ..       => withCaching e <| canonLet #[] e
  | .app ..        => withCaching e <| canonApp e
  | .proj ..       => withCaching e <| canonProj e
  | .mdata _ b     => return e.updateMData! (← canon b)
  | _              => return e
where
  canonInsideType (e : Expr) : CanonM Expr := do
    if (← read).insideType then
      canon e
    else if (← isProp e) then
      /-
      If the body is a proposition (like `a ∈ m → ...`), normalizing inside it could change the
      shape of the proposition and confuse grind's proposition handling.
      -/
      canon e
    else
      withReader (fun ctx => { ctx with insideType := true }) <| canon e

  /--
  Similar to `canonInsideType`, but skips the `isProp` check.
  Use only when `e` is known not to be a proposition.
  -/
  canonInsideType' (e : Expr) : CanonM Expr := do
    if (← read).insideType then
      canon e
    else
      withReader (fun ctx => { ctx with insideType := true }) <| canon e

  /--
  Canonicalize `e : type` where `e` is an instance by trying to resynthesize `type`.
  If `report` is `true`, we report an issue when the instance cannot be resynthesized.
  -/
  canonInstCore (e : Expr) (type : Expr) (report := true) : CanonM Expr := do
    let some inst ← Sym.synthInstance? type |
      if report then
        reportIssue! "failed to canonicalize instance{indentExpr e}\nfailed to synthesize{indentExpr type}"
      return e
    checkDefEqInst e inst

  /--
  Canonicalize an instance by trying to resynthesize it without caching.
  Recall that we have special support for `Decidable` and propositional instances.
  -/
  canonInst' (e : Expr) (report := true) : CanonM Expr := do
    /-
    We normalize the type to make sure `OfNat (Fin (2+1)) 1` and `OfNat (Fin 3) 1` will produce
    the same instances.
    -/
    let type ← inferType e
    let type' ← canonInsideType' type
    canonInstCore e type' report

  /-- `withCaching` + `canonInst'` -/
  canonInst (e : Expr) (report := true) : CanonM Expr := withCaching e do
    canonInst' e report

  /--
  Canonicalize a proposition that is also a term instance.
  Given a term `e` of the form `@Grind.nestedProof prop h`, where `g` is the constant `Grind.nestedProof`,
  we canonicalize it as follows:
  1- We recursively canonicalize the proposition `prop`.
  2- Try to resynthesize the instance, but keep the original one in case of failure since users often
  provide them using `haveI`.
  -/
  canonInstProp (g : Expr) (prop : Expr) (h : Expr) (e : Expr) : CanonM Expr := withCaching e do
    let prop' ← canon prop
    if (← read).insideType then
      /- We suppress reporting here because `haveI`-provided instances propagate into types
         through forward dependencies, and reporting them produces noise. See module doc. -/
      canonInstCore h prop' (report := false)
    else
      /-
      **Note**: We try to resynthesize the proposition, but if it fails we keep the current one.
      This may happen because propositional instances are often provided manually using `haveI`.
      -/
      let h' := (← Sym.synthInstance? prop').getD h
      /- **Note**: We don't need to check whether `h` and `h'` are definitionally equal because of proof irrelevance. -/
      return if isSameExpr prop prop' && isSameExpr h h' then e else mkApp2 g prop' h'

  /--
  Canonicalize a decidable instance without checking the cache.
  Given a term `e` of the form `@Grind.nestedDecidable prop inst`, where `g` is the constant `Grind.nestedDecidable`,
  we canonicalize it as follows:
  1- We recursively canonicalize the proposition `prop`.
  2- Try to resynthesize the instance, but keep the original one in case of failure since users often
  provide them using `haveI`.
  -/
  canonInstDec' (g : Expr) (prop : Expr) (inst : Expr) (e : Expr) : CanonM Expr := do
    let prop' ← canon prop
    let type := mkApp (mkConst ``Decidable) prop'
    if (← read).insideType then
      /- See comment in `canonInstProp` for why we suppress reporting here. -/
      canonInstCore inst type (report := false)
    else
      /-
      **Note**: We try to resynthesize the instance, but if it fails we keep the current one.
      We use `checkDefEqInst` here because two structurally different decidable instances are not necessarily
      definitionally equal.
      This may happen because propositional instances are often provided manually using `haveI`.
      -/
      let inst' := (← Sym.synthInstance? type).getD inst
      let inst' ← checkDefEqInst inst inst'
      return if isSameExpr prop prop' && isSameExpr inst inst' then e else mkApp2 g prop' inst'

  /-- `withCaching` + `canonInstDec'` -/
  canonInstDec (g : Expr) (prop : Expr) (h : Expr) (e : Expr) : CanonM Expr := withCaching e do
    canonInstDec' g prop h e

  /-- `canonInstDec` variant for normalizing `if-then-else` expressions. -/
  canonInstDecCore (e : Expr) : CanonM Expr := do
    match_expr e with
    | g@Grind.nestedDecidable prop inst => canonInstDec g prop inst e
    | _  => canonInst e (report := false)

  canonLambda (e : Expr) : CanonM Expr := do
    if (← read).insideType then
      canonLambdaLoop #[] (etaReduce e)
    else
      canonLambdaLoop #[] e

  canonLambdaLoop (fvars : Array Expr) (e : Expr) : CanonM Expr := do
    match e with
    | .lam n d b c =>
      withLocalDecl n c (← canonInsideType (d.instantiateRev fvars)) fun x =>
        canonLambdaLoop (fvars.push x) b
    | e =>
      mkLambdaFVars fvars (← canon (e.instantiateRev fvars))

  canonForall (fvars : Array Expr) (e : Expr) : CanonM Expr := do
    match e with
    | .forallE n d b c =>
      withLocalDecl n c (← canonInsideType (d.instantiateRev fvars)) fun x =>
        canonForall (fvars.push x) b
    | e =>
      mkForallFVars fvars (← canonInsideType (e.instantiateRev fvars))

  canonLet (fvars : Array Expr) (e : Expr) : CanonM Expr := do
    match e with
    | .letE n t v b nondep =>
      withLetDecl n (← canonInsideType (t.instantiateRev fvars)) (← canon (v.instantiateRev fvars)) (nondep := nondep) fun x =>
        canonLet (fvars.push x) b
    | e =>
      mkLetFVars (generalizeNondepLet := false) fvars (← canon (e.instantiateRev fvars))

  canonAppDefault (e : Expr) : CanonM Expr := e.withApp fun f args => do
    if args.size == 2 then
      if f.isConstOf ``Grind.nestedProof then
        /- **Note**: We don't have special treatment if `e` inside a type. -/
        let prop := args[0]!
        let prop' ← canon prop
        let e' := if isSameExpr prop prop' then e else mkApp2 f prop' args[1]!
        return e'
      else if f.isConstOf ``Grind.nestedDecidable then
        return (← canonInstDec' f args[0]! args[1]! e)
    let mut modified := false
    let args ← if f.isConstOf ``OfNat.ofNat then
      let some args ← normOfNatArgs? args | pure args
      modified := true
      pure args
    else
      pure args
    let mut f := f
    let f' ← canon f
    unless isSameExpr f f' do
      f := f'
      modified := true
    let pinfos := (← getFunInfo f).paramInfo
    let mut args := args.toVector
    for h : i in *...args.size do
      let arg := args[i]
      trace[sym.debug.canon] "[{repr (← shouldCanon pinfos i arg)}]: {arg} : {← inferType arg}"
      let arg' ← match (← shouldCanon pinfos i arg) with
        | .canonType =>
          /-
          The type may have nested propositions and terms that may need to be canonicalized too.
          So, we must recurse over it. See issue #10232
          -/
          canonInsideType' arg
        | .canonImplicit => canon arg
        | .visit => canon arg
        | .canonInst =>
          match_expr arg with
          | g@Grind.nestedDecidable prop h => canonInstDec g prop h arg
          | g@Grind.nestedProof prop h => canonInstProp g prop h arg
          | _ => canonInst arg
      unless isSameExpr arg arg' do
        args := args.set i arg'
        modified := true
    return if modified then mkAppN f args.toArray else e

  canonIte (f : Expr) (α c inst a b : Expr) : CanonM Expr := do
    let c ← canon c
    if isTrueCond c then canon a
    else if isFalseCond c then canon b
    else return mkApp5 f (← canonInsideType α) c (← canonInstDecCore inst) (← canon a) (← canon b)

  canonCond (f : Expr) (α c a b : Expr) : CanonM Expr := do
    let c ← canon c
    if c.isBoolTrue then canon a
    else if c.isBoolFalse then canon b
    else return mkApp4 f (← canonInsideType α) c (← canon a) (← canon b)

  postReduce (e : Expr) : CanonM Expr := do
    if isNatArithApp e then
      if let some e ← evalNat e |>.run then
        return mkNatLit e
      else if let some (e, k) ← isOffset? e |>.run then
        mkOffset e k
      else
        return e
    else
      let f := e.getAppFn
      let .const declName _ := f | return e
      if let some info ← getProjectionFnInfo? declName then
        return (← reduceProjFn? info e).getD e
      else
        return e

  /-- Canonicalize `e` and apply post reductions. -/
  canonAppAndPost (e : Expr) : CanonM Expr := do
    let e ← canonAppDefault e
    postReduce e

  canonMatch (e : Expr) : CanonM Expr := do
    if let .reduced e ← reduceMatcher? e then
      canon e
    else
      let e ← canonAppDefault e
      -- Remark: try again, discriminants may have been simplified.
      if let .reduced e ← reduceMatcher? e then
        canon e
      else
        return e

  canonApp (e : Expr) : CanonM Expr := do
    match_expr e with
    | f@ite α c i a b => canonIte f α c i a b
    | f@cond α c a b => canonCond f α c a b
    -- Remark: We currently don't normalize dependent-if-then-else occurring in types.
    | _ =>
      let f := e.getAppFn
      let .const declName _ := f | canonAppAndPost e
      if (← isMatcher declName) then
        canonMatch e
      else
        canonAppAndPost e

  canonProj (e : Expr) : CanonM Expr := do
    let e := e.updateProj! (← canon e.projExpr!)
    return (← reduceProj? e).getD e

/--
Returns `true` if `shouldCanon pinfos i arg` is not `.visit`.
This is a helper function used to implement mbtc.
-/
public def isSupport (pinfos : Array ParamInfo) (i : Nat) (arg : Expr) : MetaM Bool := do
  let r ← Canon.shouldCanon pinfos i arg
  return !r matches .visit

end Canon

/--
Canonicalize `e` by normalizing types, instances, and support arguments.
Applies targeted reductions (projection, match/ite/cond, Nat arithmetic) in all positions;
eta reduction is applied only inside types. Instances are re-synthesized.
Runs at reducible transparency.
-/
public def canon (e : Expr) : SymM Expr := do profileitM Exception "sym canon" (← getOptions) do
  withReducible do Canon.canon e {}

end Lean.Meta.Sym
