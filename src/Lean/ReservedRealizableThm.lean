/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
import Lean.Meta.Basic
import Lean.AddDecl
import Lean.ReservedNameAction

namespace Lean.Meta

/-!
This module provides a convenience layer over the the realizable constant and reserved name
mechanism for theorems attached to declaration names. It takes care of

* coherence of the dervied name between reserved name and actual generation
* the right visibility and environment
* inferring safety of the generated declaration, using an unsafe definition instead of a theorem
  when needed

It does not, but its interface anticipates
* more efficient name lookup (looking up the name suffix once in a data structure, rather than
  trying each in turn)
* asynchronous theorem body generation

This convenience layer is not meant for
* derived definitions
* when multiple derived theorems have to be generated together (e.g. due to common bookkeeping)
* when attributes need to be set on the derived theorem
-/

inductive RealizeableTheoremVisibility
  /-- The derived theorem is always private. -/
  | alwaysPrivate
  /-- The derived theorem is private iff the original declaration is private -/
  | sameAsDecl
  /-- The derived theorem is private iff the original declaration is exposed -/
  | sameAsDeclBody

structure RealizableTheoremSpec where
  /-- Suffix of the derive name (e.g. `.eq`, `.eq_def`) -/
  suffixBase : String
  /-- Whether the thereom has an index attached (`.eq_<n>`) -/
  hasIndex : Bool
  /-- Visiblity -/
  visibility  : RealizeableTheoremVisibility := .sameAsDecl
  /--
  Whether a given declaration should have this theorem attached

  The `index?` is zero-based.
  -/
  shouldExist : (env : Lean.Environment) → (declName : Name) → (index? : Option Nat) → Bool
  /--
  Generate the theorem type and proof. These are returned via continuations to allow
  for concurrency.

  The `index?` is zero-based.

  This runs in a `realizeConst` environment, so attributes set here can be found on other enviornment
  branches with with `(asyncDecl := thmName)`.
  -/
  generate : (declName thmName : Name) → (index? : Option Nat) →
    (kType : (levelParams : List Name) → (type : Expr) → MetaM Unit) →
    (kProof : (proof : Expr) → MetaM Unit) → MetaM Unit

/--
Calculates the expected name, and checks that the should exist according to
`RealizableTheoremSpec.shouldExist`.
-/
def RealizableTheoremSpec.getThmName (spec : RealizableTheoremSpec) (declName : Name) (index? : Option Nat) : MetaM Name := do
  let env ← getEnv
  let isPrivate ← match spec.visibility with
    | .alwaysPrivate =>
      pure true
    | .sameAsDecl   =>
      pure <| isPrivateName declName
    | .sameAsDeclBody => withExporting do
      let decl ← getConstInfo declName
      pure <| !decl.hasValue
  let suffix ← match spec.hasIndex, index? with
    | true, some idx => pure s!"{spec.suffixBase}_{idx + 1}"
    | true, none     => throwError "getThmName: expected an index for {spec.suffixBase}, but none was given"
    | false, _       => pure spec.suffixBase
  let thmName := if isPrivate then
    mkPrivateName env <| (privateToUserName declName).str suffix
  else
    declName.str spec.suffixBase
  unless spec.shouldExist env declName index? do
    throwError "RealizableTheoremSpec.getThmName: theorem {thmName} should not be generated"
  return thmName

/--
Generates the realizable theorem and returns its name.
This is the entry point for meta programs that need the generated name.
-/
def RealizableTheoremSpec.gen (spec : RealizableTheoremSpec) (declName : Name) (index? : Option Nat) : MetaM Name := do
  let thmName ← spec.getThmName declName index?
  -- TODO: Hook up to Environment.addConstAsync
  realizeConst declName thmName do
  withExporting (when := thmName.isPrivateName) do
    let typePromise  : IO.Promise (List Name × Expr) ← IO.Promise.new
    let proofPromise : IO.Promise Expr ← IO.Promise.new
    spec.generate declName thmName index?
      (fun lvlparams type => typePromise.resolve (lvlparams, type))
      (fun proof => proofPromise.resolve proof)
    unless (← typePromise.isResolved) do
      throwError "RealizableTheoremSpec.gen: `generate` did not set type"
    let (levelParams, type) := typePromise.result!.get
    unless (← proofPromise.isResolved) do
      throwError "RealizableTheoremSpec.gen: `generate` did not set proof"
    let value := proofPromise.result!.get
    let thmDecl := { name := thmName, levelParams, type, value }
    let decl ← mkThmOrUnsafeDef thmDecl
    addDecl decl
  return thmName

/--
Is `thmName` the name of a realizable theorem?
(Returns the optional index if so).
-/
def RealizableTheoremSpec.parseName (spec : RealizableTheoremSpec) (env : Environment) (thmName : Name) : Option (Option Nat) := do
  let .str declName suffix := thmName | none
  let mut index? := none
  if spec.hasIndex then
    let underscoreIdx ← suffix.revFind? '_'
    let suffixBase := (suffix.sliceTo underscoreIdx).toString
    guard <| suffixBase == spec.suffixBase
    let suffixIndex : String := (suffix.sliceFrom (← underscoreIdx.next?)).toString
    let idx1 ← suffixIndex.toNat?
    guard <| idx1 > 0
    let idx := idx1 - 1
    index? := some (idx - 1)
  else
    guard (suffix == spec.suffixBase)
  guard <| spec.shouldExist env declName index?
  return index?

/--
Register the realizable theorem with the reserved name machinery. To be used in `initialize` resp.
`builtin_initialize`.
-/
def RealizableTheoremSpec.register (spec : RealizableTheoremSpec) : IO Unit := do
  registerReservedNamePredicate fun env name => spec.parseName env name |>.isSome
  registerReservedNameAction fun name => do
    let some index? := spec.parseName (← getEnv) name | return false
    let _ ← MetaM.run' <| spec.gen name index?
    return true
