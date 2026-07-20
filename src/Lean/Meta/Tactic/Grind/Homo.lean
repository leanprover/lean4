/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Attr
import Lean.Meta.DiscrTree.Util
import Lean.Meta.AppBuilder
public section
namespace Lean.Meta.Grind

/-- Extension backing the `@[grind homo]` attribute. -/
builtin_initialize homoExt : Sym.Simp.SymSimpExtension ← Sym.Simp.mkSymSimpExt

/-- Returns the homomorphism rules tagged with the `[grind homo]` attribute. -/
def getHomoTheorems : CoreM Sym.Simp.Theorems :=
  homoExt.getTheorems

/--
Extension collecting the homomorphism *source types*: the head constants `F` of the
types `τ = F …` for which a `[grind homo]` rule translates `Eq τ`. The engine marks
terms of these types as solver terms so that the E-graph reports their equalities and
disequalities (see `SolverExtension.markTerm`).
-/
builtin_initialize homoSourceTypesExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := fun s n => s.insert n
  }

/-- Returns the head constants of the homomorphism source types. -/
def getHomoSourceTypes : CoreM NameSet :=
  return homoSourceTypesExt.getState (← getEnv)

/--
Ensures a `[grind homo]` theorem can be applied by `Sym.simp` without a discharger.
Instance-implicit parameters are synthesized during rewriting and need not be
determined by the left-hand side. Every other parameter must be inferable from the
left-hand side: it must occur in the left-hand side itself (as in
`(BitVec.cast h a).toNat = a.toNat`, where `h` is instantiated by matching), or in the
type of a parameter that does (such parameters are assigned by type unification).
A propositional hypothesis failing this test makes the rule conditional: it would have
to be discharged when the rule is applied, so the rule would never fire. Any other
parameter failing the test cannot be instantiated at all (e.g. it occurs only in the
right-hand side).
-/
def validateHomoTheorem (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs concl => do
    let lhs := match_expr concl with
      | Eq _ lhs _ => lhs
      | Iff lhs _ => lhs
      | Not p => p
      | _ => concl
    let mut covered : FVarIdSet := {}
    for x in xs do
      if lhs.containsFVar x.fvarId! then
        covered := covered.insert x.fvarId!
    -- Close under occurrence in the types of covered parameters.
    let mut changed := true
    while changed do
      changed := false
      for x in xs do
        unless covered.contains x.fvarId! do
          for y in xs do
            if covered.contains y.fvarId! && (← inferType y).containsFVar x.fvarId! then
              covered := covered.insert x.fvarId!
              changed := true
              break
    for x in xs do
      if (← getFVarLocalDecl x).binderInfo matches .instImplicit then
        continue
      unless covered.contains x.fvarId! do
        let xType ← inferType x
        if (← isProp xType) then
          throwError "invalid `[grind homo]` theorem, `{.ofConstName declName}` is conditional: \
            hypothesis{indentExpr xType}\nis not determined by the left-hand side and would have \
            to be discharged when the rule is applied. Homomorphism rules must be unconditional; \
            use E-matching attributes such as `[grind =]` or `[grind →]` for conditional theorems"
        else
          throwError "invalid `[grind homo]` theorem, parameter `{x}` of \
            `{.ofConstName declName}` is not determined by the left-hand side of the rule"

/--
If `declName` is an `=`-injection rule — a rule whose left-hand side is an equality
`Eq τ _ _` — checks that its source type `τ` is headed by a constant `F` and returns
`F`. The engine marks terms as solver terms by the head constant of their type; a rule
over a variable type (e.g. a class-generic injection `(a = b) ↔ toI a = toI b`) has no
head constant, and would silently never fire on asserted equalities.
-/
private def checkEqInjection? (declName : Name) : MetaM (Option Name) := do
  let info ← getConstInfo declName
  forallTelescope info.type fun _ concl => do
    let lhs := match_expr concl with
      | Eq _ lhs _ => lhs
      | Iff lhs _ => lhs
      | _ => concl
    let_expr Eq τ _ _ := lhs | return none
    let .const F _ := τ.getAppFn
      | throwError "invalid `[grind homo]` theorem, the source type of the `=`-injection rule \
          `{.ofConstName declName}` is not headed by a constant{indentExpr τ}\nhomomorphism rules \
          translate concrete types; generic injections cannot be tracked by the E-graph"
    return some F

/--
Validates and registers a `[grind homo]` theorem, recording the source type of
`=`-injection rules. See `validateHomoTheorem`.
-/
def addHomoAttr (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  Sym.Simp.addSymSimpDecl homoExt "grind homo" declName attrKind (validate := fun declName => do
    validateHomoTheorem declName
    if let some F ← checkEqInjection? declName then
      homoSourceTypesExt.add F attrKind)

/-- A theorem tagged with the `[grind homo_pred]` attribute. -/
structure HomoPredTheorem where
  /-- Name of the theorem. -/
  declName : Name
  /-- Number of explicit parameters. The theorem is instantiated with the trailing
  `arity` arguments of the triggering application. -/
  arity : Nat
  deriving Inhabited, BEq

/-- Map from trigger head symbol to the `[grind homo_pred]` theorems it activates. -/
abbrev HomoPredTheorems := NameMap (List HomoPredTheorem)

/-- Extension backing the `@[grind homo_pred]` attribute. -/
builtin_initialize homoPredExt : SimpleScopedEnvExtension (Name × HomoPredTheorem) HomoPredTheorems ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := fun s (key, thm) => s.insert key (thm :: (s.find? key).getD [])
  }

/-- Returns the homomorphism predicates tagged with the `[grind homo_pred]` attribute. -/
def getHomoPredTheorems : CoreM HomoPredTheorems :=
  return homoPredExt.getState (← getEnv)

/--
Validates and registers a `[grind homo_pred]` theorem.
The conclusion of the theorem must contain an application whose trailing arguments are
exactly the theorem's explicit parameters. The head symbol of this application is the
trigger for the theorem.
-/
def addHomoPredAttr (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  let info ← getConstInfo declName
  unless (← isProp info.type) do
    throwError "invalid `[grind homo_pred]` theorem, `{.ofConstName declName}` is not a proposition"
  forallTelescope info.type fun xs type => do
    let xsExplicit ← xs.filterM fun x => return (← getFVarLocalDecl x).binderInfo.isExplicit
    if xsExplicit.isEmpty then
      throwError "invalid `[grind homo_pred]` theorem, `{.ofConstName declName}` must have \
        at least one explicit parameter; the trigger is inferred from an application whose \
        trailing arguments are the theorem's explicit parameters"
    let found? := type.find? fun e => Id.run do
      unless e.isApp && e.getAppFn.isConst do return false
      let args := e.getAppArgs
      if args.size < xsExplicit.size then return false
      return args.extract (args.size - xsExplicit.size) args.size == xsExplicit
    let some found := found?
      | throwError "invalid `[grind homo_pred]` theorem, the conclusion of `{.ofConstName declName}` does not contain an application whose trailing arguments are the theorem's explicit parameters"
    let .const key _ := found.getAppFn | unreachable!
    homoPredExt.add (key, { declName, arity := xsExplicit.size }) attrKind

/--
Returns the instances of the `[grind homo_pred]` theorems triggered by `e`.
Each instance is a pair `(proof, prop)` where `proof : prop`. A registered theorem
whose trigger matches `e`'s head symbol is instantiated with `e`'s trailing arguments;
instantiations that fail to elaborate (e.g. because the argument types do not match)
are discarded.
-/
def mkHomoPredInstances (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let .const declName _ := e.getAppFn | return #[]
  let some thms := (← getHomoPredTheorems).find? declName | return #[]
  let args := e.getAppArgs
  let mut result := #[]
  for thm in thms do
    if args.size ≥ thm.arity then
      try
        let proof ← mkAppM thm.declName (args.extract (args.size - thm.arity) args.size)
        result := result.push (proof, ← inferType proof)
      catch _ =>
        pure ()
  return result

end Lean.Meta.Grind
