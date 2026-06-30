module
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Sym.Simp.Attr
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.AppBuilder

namespace Homomorphism

open Lean Meta Grind Sym Simp

initialize registerTraceClass `homo
initialize registerTraceClass `homo.pred
initialize registerTraceClass `homo.visit

initialize homoPredExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  let add := fun s (f, thm) => s.insert f thm
  registerSimplePersistentEnvExtension {
    addEntryFn    := add
    addImportedFn := fun es => mkStateFromImportedEntries add {} es
  }

def getPredMap : CoreM (NameMap Name) :=
  return homoPredExt.getState (← getEnv)

def addPredicate (thmName : Name) : MetaM Unit := do
  let info ← getConstInfo thmName
  unless (← isProp info.type) do
    throwError "invalid homomorphism predicate, `{thmName}` is not a proposition"
  let vs := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs type => do
    let found? := type.find? fun e => Id.run do
      unless e.getAppNumArgs == xs.size do return false
      let .const _ us := e.getAppFn | return false
      return e.getAppArgs == xs && us == vs
    let some found := found? |
      throwError "invalid homomorphism predicate, `{thmName}` does not contain application that covers all parameters"
    let .const declName _ := found.getAppFn | unreachable!
    if (← getPredMap).contains declName then
      throwError "invalid homomorphism predicate, `{declName}` already contains a theorem associated with it."
    modifyEnv fun env => homoPredExt.addEntry env (declName, thmName)

initialize registerBuiltinAttribute {
    name := `grind_homo_pred
    descr := "add a theorem to be applied to atoms"
    add := fun declName _ _ =>
      discard <| addPredicate declName |>.run {} {}
  }

/--
Declares attribute `[grind_mono]` for marking theorems implementing the homomorphism.
-/
initialize homoSimpExtension : SymSimpExtension ←
  registerSymSimpAttr `grind_homo "`grind` homomorphism attribute"

/--
Returns theorems marked with `[grind_mono]`
-/
def getTheorems : CoreM Theorems :=
  homoSimpExtension.getTheorems

/--
Creates a simproc that applies the theorems marked with `[grind_mono]`.
This simproc is meant to be applied as a `pre` method.

Recall that `grind` internalizes terms bottom-up. By the time a
simplification set runs on a term `e`, all subterms of `e` are already
in the E-graph and have been processed by the pipeline.

**Stop condition.** When simp encounters a term `t` during traversal:

- If a rule matches `t`: apply it, continue (result is a new term).
- If no rule matches `t` AND `t` is already in the E-graph:
  stop, don't descend. Otherwise: descend normally.
-/
def mkRewriter : GoalM Sym.Simp.Simproc := do
  let s ← get
  -- Remark: We are not using any discharger. So, our rewriting rules are all context
  -- independent.
  let rw := (← getTheorems).rewrite
  return fun e => do
    trace[homo.visit] "{e}"
    let r ← rw e
    if !r.isRfl then return r
    -- If `e` is already in the E-graph, we don't revisit its children
    let done := s.enodeMap.contains { expr := e }
    return .rfl (done := done)

structure State where
  cache : Sym.Simp.Cache := {}
  processed : PHashSet ExprPtr := {}

initialize homoExt : SolverExtension State ←
  registerSolverExtension (return {})

def get' : GoalM State := do
  homoExt.getState

abbrev modify' (f : State → State) : GoalM Unit := do
  homoExt.modifyState f

/-- Apply the homomorphism theorems. -/
def applyHomo (e : Expr) : GoalM Sym.Simp.Result := do
  let methods := { pre := (← mkRewriter) }
  -- Reuse cache.
  let persistentCache := (← homoExt.getState).cache
  homoExt.modifyState fun s => { s with cache := {} } -- Improve uniqueness. This is a minor optimization
  let (r, simpState) ← Sym.Simp.SimpM.run (Sym.Simp.simp e) (methods := methods) (s := { persistentCache })
  homoExt.modifyState fun s => { s with cache := simpState.persistentCache }
  return r

/--
Returns `true` if some theorem marked with `[grind_homo]` is applicable to `e`.

Motivation: we don't want to start the simplifier and fail immediately.
-/
def isTarget (e : Expr) : CoreM Bool := do
  let thms ← getTheorems
  return !(thms.getMatch e).isEmpty

/--
Internalization procedure for this module. See `homoExt.setMethods`
-/
def internalize (e : Expr) (_ : Option Expr) : GoalM Unit := do
  let f := e.getAppFn
  if let .const declName us := f then
    let s ← get'
    unless s.processed.contains { expr := e } do
      modify' fun s => { s with processed := s.processed.insert { expr := e } }
      if let some thmName := (← getPredMap).find? declName then
        let thm := mkAppN (mkConst thmName us) e.getAppArgs
        let pred ← Meta.inferType thm
        trace[homo.pred] "{pred}"
        addNewRawFact thm (← Meta.inferType thm) (← getGeneration e) .input .other
        return ()
  unless (← isTarget e) do return ()
  if !(← alreadyInternalized e) then
    /-
    The `grind` core has an optimization: it does not internalize top-level equalities
    since they can be merged immediately. A satellite solver may implement the `newEq` handler,
    but this is too inconvenient. It is easier to force `e` to be internalized.
    -/
    let_expr Eq _ lhs rhs := e | return ()
    let gen := max (← getGeneration lhs) (← getGeneration rhs)
    Grind.internalize e gen
    return ()
  let .step e₁ h₁ _ ← applyHomo e | return ()
  let r ← preprocess e₁
  let h ← mkEqTrans h₁ (← r.getProof)
  let gen ← getGeneration e
  Grind.internalize r.expr gen
  trace[homo] "{e}\n====>\n{r.expr}"
  pushEq e r.expr h

initialize
  homoExt.setMethods
    (internalize := internalize)

end Homomorphism
