/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
prelude
import Init.Data.Array.InsertionSort
import Lean.Meta.DiscrTree

namespace Lean.Meta.Ext

/-!
### Environment extension for `ext` theorems
-/

/-- Information about an extensionality theorem, stored in the environment extension. -/
structure ExtTheorem where
  /-- Declaration name of the extensionality theorem. -/
  declName : Name
  /-- Priority of the extensionality theorem. -/
  priority : Nat
  /--
  Key in the discrimination tree,
  for the type in which the extensionality theorem holds.
  -/
  keys : Array DiscrTree.Key
  deriving Inhabited, Repr, BEq, Hashable

/-- The state of the `ext` extension environment -/
structure ExtTheorems where
  /-- The tree of `ext` extensions. -/
  tree   : DiscrTree ExtTheorem := {}
  /-- Erased `ext`s via `attribute [-ext]`. -/
  erased  : PHashSet Name := {}
  deriving Inhabited

/-- The environment extension to track `@[ext]` theorems. -/
builtin_initialize extExtension :
    SimpleScopedEnvExtension ExtTheorem ExtTheorems ←
  registerSimpleScopedEnvExtension {
    addEntry := fun { tree, erased } thm =>
      { tree := tree.insertCore thm.keys thm, erased := erased.erase thm.declName }
    initial := {}
  }

/-- Gets the list of `@[ext]` theorems corresponding to the key `ty`,
ordered from high priority to low. -/
@[inline] def getExtTheorems (ty : Expr) : MetaM (Array ExtTheorem) := do
  let extTheorems := extExtension.getState (← getEnv)
  let arr ← extTheorems.tree.getMatch ty
  let erasedArr := arr.filter fun thm => !extTheorems.erased.contains thm.declName
  -- Using insertion sort because it is stable and the list of matches should be mostly sorted.
  -- Most ext theorems have default priority.
  return erasedArr.insertionSort (·.priority < ·.priority) |>.reverse

/--
Erases a name marked `ext` by adding it to the state's `erased` field and
removing it from the state's list of `Entry`s.

This is triggered by `attribute [-ext] name`.
-/
def ExtTheorems.eraseCore (d : ExtTheorems) (declName : Name) : ExtTheorems :=
 { d with erased := d.erased.insert declName }

/-- Returns `true` if `d` contains theorem with name `declName`. -/
def ExtTheorems.contains (d : ExtTheorems) (declName : Name) : Bool :=
  d.tree.containsValueP (·.declName == declName) && !d.erased.contains declName

/-- Returns `true` if `declName` is tagged with `[ext]` attribute. -/
def isExtTheorem (declName : Name) : CoreM Bool := do
  let extTheorems := extExtension.getState (← getEnv)
  return extTheorems.contains declName

/--
Erases a name marked as a `ext` attribute.
Check that it does in fact have the `ext` attribute by making sure it names a `ExtTheorem`
found somewhere in the state's tree, and is not erased.
-/
def ExtTheorems.erase [Monad m] [MonadError m] (d : ExtTheorems) (declName : Name) :
    m ExtTheorems := do
  unless d.contains declName do
    throwError "'{declName}' does not have [ext] attribute"
  return d.eraseCore declName

end Lean.Meta.Ext
