/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Tactic.Simp
public import Lean.Meta.Sym.Pattern
public import Std.Tactic.Do.Syntax
public import Std.Internal.Do.Triple.Basic
import Init.While
import Init.Syntax
import Lean.Meta.Sym.Simp.DiscrTree

public section

namespace Lean.Elab.Tactic.Do.SpecAttr

open Lean Meta Std.Do

builtin_initialize registerTraceClass `Elab.Tactic.Do.specAttr

/--
  This attribute should not be used directly.
  It is an implementation detail of the `mvcgen` tactic.
-/
builtin_initialize mvcgenSimpExt : Meta.SimpExtension ←
  Meta.registerSimpAttr `mvcgen_simp "simp theorems internally used by `mvcgen`"

/--
  The simp set accumulated by the `@[spec]` attribute.
  (This does not include Hoare triple specs.)
  It is an implementation detail of the `mvcgen` tactic.
-/
def getSpecSimpTheorems : CoreM SimpTheorems :=
  mvcgenSimpExt.getTheorems

inductive SpecProof where
  | global (declName : Name)
  | local (fvarId : FVarId)
  | stx (id : Name) (ref : Syntax) (proof : Expr)
  deriving Inhabited, BEq

/-- A unique identifier corresponding to the origin. -/
def SpecProof.key : SpecProof → Name
  | .global declName => declName
  | .local fvarId => fvarId.name
  | .stx id _ _ => id

/-- Convert a simp `Origin` to a `SpecProof`. -/
def SpecProof.ofOrigin : Origin → Option SpecProof
  | .decl declName .. => some (.global declName)
  | .fvar fvarId => some (.local fvarId)
  | _ => none

def SpecProof.getProof : SpecProof → MetaM (List Name × Expr)
  | .stx _ _ proof => pure ([], proof)
  | .local fvarId => pure ([], mkFVar fvarId)
  | .global declName => do
    let info ← getConstInfo declName
    pure (info.levelParams, mkConst declName (info.levelParams.map mkLevelParam))

instance : Hashable SpecProof where
  hash sp := hash sp.key

def SpecProof.instantiate (proof : SpecProof) : MetaM (Array Expr × Array BinderInfo × Expr × Expr) := do
  let prf ← match proof with
    | .global declName => mkConstWithFreshMVarLevels declName
    | .local fvarId => pure <| mkFVar fvarId
    | .stx _ _ proof => pure proof -- TODO: Think about simp-like generalization
  -- We instantiate here deeply specifically for local hypotheses, the type of which
  -- may contain MVars at multiple levels.
  -- An example is `ih` in `serialize_bytesize` from the serialization schema test
  let type ← instantiateMVars (← inferType prf)
  let (xs, bs, type) ← forallMetaTelescope type
  return (xs, bs, prf.beta xs, type)

instance : ToMessageData SpecProof where
  toMessageData := fun
    | .global declName => m!"SpecProof.global {declName}"
    | .local fvarId => m!"SpecProof.local {mkFVar fvarId}"
    | .stx _ ref proof => m!"SpecProof.stx _ {ref} {proof}"

structure SpecTheorem where
  keys : Array DiscrTree.Key
  /--
  Expr key tested for matching, in ∀-quantified form.
  `keys = (← mkPath (← forallMetaTelescope prog).2.2)`.
  -/
  prog : Expr
  /-- The proof for the theorem. -/
  proof : SpecProof
  /--
  If `etaPotential` is non-zero, then the precondition contains meta variables that can be
  instantiated after applying `mintro ∀s` `etaPotential` many times.
  -/
  etaPotential : Nat := 0
  priority : Nat  := eval_prio default
  deriving Inhabited, BEq

abbrev SpecEntry := SpecTheorem

structure SpecTheorems where
  specs : DiscrTree SpecTheorem := DiscrTree.empty
  erased : PHashSet SpecProof := {}
  deriving Inhabited

def SpecTheorems.insert (d : SpecTheorems) (e : SpecTheorem) : SpecTheorems :=
  { d with specs := d.specs.insertKeyValue e.keys e }

def SpecTheorems.isErased (d : SpecTheorems) (thmId : SpecProof) : Bool :=
  d.erased.contains thmId

def SpecTheorems.erase (d : SpecTheorems) (thmId : SpecProof) : SpecTheorems :=
  { d with erased := d.erased.insert thmId }

abbrev SpecExtension := SimpleScopedEnvExtension SpecEntry SpecTheorems

private partial def countBVarDependentMVars (xs : Array Expr) (e : Expr) : MetaM Nat :=
  go e
  where
    go (e : Expr) : MetaM Nat := do
      if !e.hasExprMVar then return 0
      match e with
      | .app f a =>
        if let some (_, lhs, rhs) := e.eq? then
          let l := lhs.getAppFn'
          let r := rhs.getAppFn'
          if l.isMVar && rhs.hasLooseBVars && xs.contains l then return 1
          if r.isMVar && lhs.hasLooseBVars && xs.contains r then return 1
          return ← (· + ·) <$> go lhs <*> go rhs
        return ← (· + ·) <$> go f <*> go a
      | .mdata _ e => go e
      | .lam _ ty b _ => (· + ·) <$> go ty <*> go b
      | .letE _ ty v b _ => (· + · + ·) <$> go ty <*> go v <*> go b
      | .forallE _ ty b _ => (· + ·) <$> go ty <*> go b
      | .proj _ _ e => go e
      | .mvar .. => return 0
      | .lit .. | .fvar .. | .bvar .. | .sort .. | .const .. => return 0

def simpSPredConfig : ConfigWithKey :=
  { simpGlobalConfig.config with
    iota := true,
    beta := true,
    zeta := true,
    zetaDelta := true,
    proj := .yesWithDelta }.toConfigWithKey

/-- If `σs : List Type`, then `e : SPred σs`.
Return the number of times `e` needs to be applied
in order to assign closed solutions to meta variables. -/
partial def computeMVarBetaPotentialForSPred (xs : Array Expr) (σs : Expr) (e : Expr) : MetaM Nat :=
  withNewMCtxDepth do
  withConfigWithKey simpSPredConfig do
  if xs.isEmpty then return 0
  let ctx ← Simp.Context.mkDefault
  let mut σs ← whnfR σs
  let mut e := e
  let mut n : Nat := 0
  let mut lastSuccess := 0
  let mut boundAssignments ← countBVarDependentMVars xs e
  while σs.isAppOfArity ``List.cons 3 do
    n := n+1
    let σ := σs.getArg! 1
    let s ← mkFreshExprMVar σ
    e := e.beta #[s]
    let (r, _) ← simp e ctx
      -- In practice we only need to reduce `fun s => ...` and `SPred.pure`.
      -- We could write a custom function should `simp` become a bottleneck.
    e := r.expr
    let count ← countBVarDependentMVars xs e
    if count < boundAssignments || e.getAppFn'.isMVar then
      lastSuccess := n
      boundAssignments := count
    σs ← whnfR (σs.getArg! 2)
  return lastSuccess

private def mkSpecTheorem (type : Expr) (proof : SpecProof) (prio : Nat) : MetaM SpecTheorem := do
  -- cf. mkSimpTheoremCore
  let type ← instantiateMVars type
  unless (← isProp type) do
    throwError "invalid 'spec', proposition expected{indentExpr type}"
  withNewMCtxDepth do
  let (xs, _, type) ← withSimpGlobalConfig (forallMetaTelescopeReducing type)
  let type ← whnfR type
  let_expr c@Triple _m ps _inst _α prog P _Q := type
    | throwError "unexpected kind of spec theorem; not a triple{indentExpr type}"
  let keys ← DiscrTree.mkPath prog (noIndexAtArgs := false)
  -- beta potential of `P` describes how many times we want to `mintro ∀s`, that is,
  -- *eta*-expand the goal.
  let σs := mkApp (mkConst ``PostShape.args [c.constLevels![0]!]) ps
  let etaPotential ← computeMVarBetaPotentialForSPred xs σs P
  -- logInfo m!"Beta potential {etaPotential} for {P}"
  -- logInfo m!"mkSpecTheorem: {keys}, proof: {proof}"
  return { keys, prog := (← mkForallFVars xs prog), proof, etaPotential, priority := prio }

def mkSpecTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM SpecTheorem := do
  -- cf. mkSimpTheoremsFromConst
  let cinfo ← getConstInfo declName
  let us := cinfo.levelParams.map mkLevelParam
  let val := mkConst declName us
--  withSimpGlobalConfig do -- This sets iota := false, which we do not want (for computeMVarBetaPotentialForSPred)
  let type ← inferType val
  mkSpecTheorem type (.global declName) prio

def mkSpecTheoremFromLocal (fvar : FVarId) (prio : Nat := eval_prio default) : MetaM SpecTheorem := do
  let some decl ← fvar.findDecl? | throwError "invalid 'spec', local declaration {fvar.name} not found"
  mkSpecTheorem decl.type (.local fvar) prio

def mkSpecTheoremFromStx (ref : Syntax) (proof : Expr) (prio : Nat := eval_prio default) : MetaM SpecTheorem := do
  let type ← inferType proof
  mkSpecTheorem type (.stx (← mkFreshId) ref proof) prio

def SpecExtension.addSpecTheoremFromConst (ext : SpecExtension) (declName : Name) (prio : Nat) (attrKind : AttributeKind) : MetaM Unit := do
  let thm ← mkSpecTheoremFromConst declName prio
  ext.add thm attrKind

def SpecExtension.addSpecTheoremFromLocal (ext : SpecExtension) (fvar : FVarId) (prio : Nat := eval_prio default) : MetaM Unit := do
  let thm ← mkSpecTheoremFromLocal fvar prio
  ext.add thm .local

def mkSpecExt : SimpleScopedEnvExtension.Descr SpecEntry SpecTheorems where
  name     := `specMap
  initial  := {}
  addEntry := fun d e => d.insert e

builtin_initialize specAttr : SpecExtension ← registerSimpleScopedEnvExtension mkSpecExt

def SpecExtension.getTheorems (ext : SpecExtension) : CoreM SpecTheorems :=
  return ext.getState (← getEnv)

def getSpecTheorems : CoreM SpecTheorems :=
  specAttr.getTheorems

end Lean.Elab.Tactic.Do.SpecAttr

namespace Lean.Elab.Tactic.Do.Internal.SpecAttr

open Lean Meta Std.Internal.Do Lean.Order

inductive SpecProof where
  | global (declName : Name)
  | local (fvarId : FVarId)
  | stx (id : Name) (ref : Syntax) (proof : Expr)
  deriving Inhabited, BEq

/-- A unique identifier corresponding to the origin. -/
def SpecProof.key : SpecProof → Name
  | .global declName => declName
  | .local fvarId => fvarId.name
  | .stx id _ _ => id

/-- Convert a simp `Origin` to a `SpecProof`. -/
def SpecProof.ofOrigin : Origin → Option SpecProof
  | .decl declName .. => some (.global declName)
  | .fvar fvarId => some (.local fvarId)
  | _ => none

def SpecProof.getProof : SpecProof → MetaM (List Name × Expr)
  | .stx _ _ proof => pure ([], proof)
  | .local fvarId => pure ([], mkFVar fvarId)
  | .global declName => do
    let info ← getConstInfo declName
    pure (info.levelParams, mkConst declName (info.levelParams.map mkLevelParam))

instance : Hashable SpecProof where
  hash sp := hash sp.key

/--
Normalises a specification proof so its conclusion is in `pre ⊑ wp …` form.

- Returns `some` for `Triple` proofs (rewriting via `Triple.hwp`) and proofs already in
  `pre ⊑ wp …` form (passed through unchanged).
- Returns `none` if `type` is neither shape; callers should `throwError`.
-/
private def tripleToWpProof? (proof type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR type
  if type.isAppOfArity ``Triple 12 then
    let proof ← mkAppM ``Triple.hwp #[proof]
    let type ← instantiateMVars (← inferType proof)
    return some (proof, type)
  else if type.isAppOfArity ``PartialOrder.rel 4 then
    return some (proof, type)
  else
    return none

def SpecProof.instantiate (proof : SpecProof) : MetaM (Array Expr × Array BinderInfo × Expr × Expr) := do
  let prf ← match proof with
    | .global declName => mkConstWithFreshMVarLevels declName
    | .local fvarId => pure <| mkFVar fvarId
    | .stx _ _ proof => pure proof
  let type ← instantiateMVars (← inferType prf)
  let (xs, bs, type) ← forallMetaTelescope type
  let prf := prf.beta xs
  let some (prf, type) ← tripleToWpProof? prf type
    | throwError "expected `Triple` or `⊑ wp` specification, got{indentExpr type}"
  return (xs, bs, prf, type)

instance : ToMessageData SpecProof where
  toMessageData := fun
    | .global declName => m!"SpecProof.global {declName}"
    | .local fvarId => m!"SpecProof.local {mkFVar fvarId}"
    | .stx _ ref proof => m!"SpecProof.stx _ {ref} {proof}"

structure SpecTheorem where
  /--
  Pattern for the program expression.
  This is the key used in the discrimination tree.
  If the proof has type `∀ a b c, ⦃P⦄ prog ⦃Q⦄`, then the pattern is `prog[a:=#2, b:=#1, c:=#0]`.
  For specs stated as `pre ⊑ wp prog post epost`, the pattern is keyed on `prog`.
  -/
  pattern : Sym.Pattern
  /-- The proof for the theorem. -/
  proof : SpecProof
  priority : Nat := eval_prio default
  deriving Inhabited

instance : BEq SpecTheorem where
  beq a b := a.proof == b.proof

abbrev SpecEntry := SpecTheorem

structure SpecTheorems where
  specs : DiscrTree SpecTheorem := DiscrTree.empty
  erased : PHashSet SpecProof := {}
  deriving Inhabited

def SpecTheorems.insert (d : SpecTheorems) (e : SpecTheorem) : SpecTheorems :=
  { d with specs := Sym.insertPattern d.specs e.pattern e }

def SpecTheorems.isErased (d : SpecTheorems) (thmId : SpecProof) : Bool :=
  d.erased.contains thmId

def SpecTheorems.erase (d : SpecTheorems) (thmId : SpecProof) : SpecTheorems :=
  { d with erased := d.erased.insert thmId }

abbrev SpecExtension := SimpleScopedEnvExtension SpecEntry SpecTheorems

/--
Drops pattern variables that the pattern expression does not depend on.

`Sym.mkPatternFromExprWithKey`/`Sym.mkPatternFromDeclWithKey` turn *every* leading `∀`-binder of the
source type into a pattern variable, even binders the selected key (e.g. the program of a `Triple`
conclusion) never mentions. During matching those variables only ever become fresh metavariables
(see `Sym.mkPreResult`); for instance binders they additionally trigger spurious `trySynthInstance`
calls. This keeps only the variables that the pattern expression references, together with the
transitive closure of variables their types depend on, and renumbers the remaining de Bruijn
indices. `varInfos?` and `checkTypeMask?` are filtered to the surviving telescope; `fnInfos`,
`levelParams`, and the discrimination-tree key are unchanged because the pattern expression's
structure is untouched (bound variables are wildcards in the key).

**Important:** only use this when the matched arguments are *not* reused to rebuild a proof term,
as `Sym.BackwardRule`/`Sym.mkValue` do — dropping variables would drop arguments those need. It is
meant for databases such as `mvcgen'`'s spec table, where the proof is re-elaborated independently
of the pattern.
-/
def eraseUnusedVarsFromPattern (p : Sym.Pattern) : Sym.Pattern := Id.run do
  let n := p.varTypes.size
  -- Variable `j` (0 = outermost binder) is bound variable `#(ctx-1-j)` in a context of `ctx`
  -- binders. `used[j]` becomes `true` once we know variable `j` is reachable from the pattern.
  let mut used := Array.replicate n false
  for j in *...n do
    if p.pattern.hasLooseBVar (n - 1 - j) then
      used := used.set! j true
  -- A variable's type may reference earlier variables, so propagate top-down: when a kept variable
  -- is reached, mark every variable occurring in its type as kept too.
  for j in *...n do
    let i := n - 1 - j
    if used[i]! then
      for k in *...i do
        if p.varTypes[i]!.hasLooseBVar (i - 1 - k) then
          used := used.set! k true
  if used.all (· == true) then return p
  let kept := (Array.range n).filter (used[·]!)
  -- Rebuild the telescope via fvar placeholders to avoid manual de Bruijn arithmetic.
  let fvars := (Array.range n).map fun i => mkFVar ⟨.num `_sym_prune i⟩
  let keptFVars := kept.map (fvars[·]!)
  let newPattern := (p.pattern.instantiateRev fvars).abstract keptFVars
  let newVarTypes := kept.mapIdx fun k i =>
    (p.varTypes[i]!.instantiateRev (fvars.extract 0 i)).abstract (keptFVars.extract 0 k)
  -- `varInfos?`/`checkTypeMask?` are parallel to `varTypes`; their per-variable meaning does not
  -- depend on the de Bruijn numbering, so we simply keep the surviving entries.
  let newVarInfos? := p.varInfos?.bind fun infos =>
    let argsInfo := kept.map (infos.argsInfo[·]!)
    if argsInfo.any fun a => a.isProof || a.isInstance then some { argsInfo } else none
  let newCheckTypeMask? := p.checkTypeMask?.bind fun mask =>
    let newMask := kept.map (mask[·]!)
    if newMask.all (· == false) then none else some newMask
  return { p with
    varTypes := newVarTypes
    pattern := newPattern
    varInfos? := newVarInfos?
    checkTypeMask? := newCheckTypeMask? }

/--
Builds a `Sym.Pattern` keyed on the program inside a spec conclusion.
Accepts both `Triple` and `pre ⊑ wp prog post epost` shapes.
-/
def mkSpecPatternFromExpr (expr : Expr) (levelParams : List Name := []) : MetaM Sym.Pattern := do
  let (pattern, _) ← Sym.mkPatternFromExprWithKey expr levelParams fun type => do
    let type ← whnfR type
    if type.isAppOfArity ``Triple 12 then
      return (type.getArg! 9, ())
    else if type.isAppOfArity ``PartialOrder.rel 4 then
      let rhs := type.getArg! 3
      let_expr wp _m _Pred _EPred _monad _instAL _instEAL _wpInst _α prog _post _epost := rhs
        | throwError "RHS of ⊑ is not a `wp` application{indentExpr rhs}"
      return (prog, ())
    else
      throwError "unexpected kind of spec theorem; expected `Triple` or `⊑ wp`{indentExpr type}"
  return eraseUnusedVarsFromPattern pattern

private def mkSpecTheorem (proof : SpecProof) (prio : Nat) : MetaM SpecTheorem := do
  let (levelParams, expr) ← proof.getProof
  let pattern ← mkSpecPatternFromExpr expr levelParams
  return { pattern, proof, priority := prio }

def mkSpecTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM SpecTheorem :=
  mkSpecTheorem (.global declName) prio

def mkSpecTheoremFromLocal (fvar : FVarId) (prio : Nat := eval_prio default) : MetaM SpecTheorem := do
  let some _ ← fvar.findDecl? | throwError "invalid 'spec', local declaration {fvar.name} not found"
  mkSpecTheorem (.local fvar) prio

def mkSpecTheoremFromStx (ref : Syntax) (proof : Expr) (prio : Nat := eval_prio default) : MetaM SpecTheorem := do
  mkSpecTheorem (.stx (← mkFreshId) ref proof) prio

def SpecExtension.addSpecTheoremFromConst (ext : SpecExtension) (declName : Name) (prio : Nat) (attrKind : AttributeKind) : MetaM Unit := do
  let thm ← mkSpecTheoremFromConst declName prio
  ext.add thm attrKind

def SpecExtension.addSpecTheoremFromLocal (ext : SpecExtension) (fvar : FVarId) (prio : Nat := eval_prio default) : MetaM Unit := do
  let thm ← mkSpecTheoremFromLocal fvar prio
  ext.add thm .local

def mkSpecExt : SimpleScopedEnvExtension.Descr SpecEntry SpecTheorems where
  name     := `internalSpecMap
  initial  := {}
  addEntry := fun d e => d.insert e

builtin_initialize specAttr : SpecExtension ← registerSimpleScopedEnvExtension mkSpecExt

def SpecExtension.getTheorems (ext : SpecExtension) : CoreM SpecTheorems :=
  return ext.getState (← getEnv)

def getSpecTheorems : CoreM SpecTheorems :=
  specAttr.getTheorems

end Lean.Elab.Tactic.Do.Internal.SpecAttr

namespace Lean.Elab.Tactic.Do.SpecAttr

def mkSpecAttr : AttributeImpl where
  name  := `spec
  descr := "Marks Hoare triple specifications and simp theorems for use with `mvcgen` tactics"
  applicationTime := AttributeApplicationTime.afterCompilation
  add := fun declName stx attrKind => do
    let go : MetaM Unit := do
      let _ ← getAsyncConstInfo declName
      let prio ← getAttrParamOptPrio stx[1]
      try
        -- Legacy `Std.Do.Triple` specs.
        specAttr.addSpecTheoremFromConst declName prio attrKind
      catch _ =>
      try
        -- New metatheory `Std.Internal.Do.Triple` / `⊑ wp` specs.
        Internal.SpecAttr.specAttr.addSpecTheoremFromConst declName prio attrKind
      catch _ =>
      let impl ← getBuiltinAttributeImpl `mvcgen_simp
      try
        let newStx ← `(attr| mvcgen_simp)
        let newStx := newStx.raw.setArg 3 stx[1]
        impl.add declName newStx attrKind
      catch e =>
      trace[Elab.Tactic.Do.specAttr] "Reason for failure to apply spec attribute: {e.toMessageData}"
      throwError "Invalid 'spec': target was neither a Hoare triple specification nor a 'simp' lemma"
    discard <| go.run {} {}

builtin_initialize registerBuiltinAttribute mkSpecAttr

/--
Marks a type as an invariant type for the `mvcgen` tactic.
Goals whose type is an application of a tagged type will be classified
as invariants rather than verification conditions.
-/
builtin_initialize specInvariantAttr : TagAttribute ←
  registerTagAttribute `spec_invariant_type
    "marks a type as an invariant type for the `mvcgen` tactic"

/--
Returns `true` if `ty` is an application of a type tagged with `@[spec_invariant_type]`.
-/
def isSpecInvariantType (env : Environment) (ty : Expr) : Bool :=
  if let .const name .. := ty.getAppFn then
    specInvariantAttr.hasTag env name
  else
    false

end Lean.Elab.Tactic.Do.SpecAttr
