/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Store
public import Lake.Build.Job.Basic
public import Std.Sync.Mutex

set_option doc.verso true
set_option linter.missingDocs true

/-!
# The Lake Build Store

The Lake build store is the map of Lake build keys to build task and/or
build results that is slowly filled during a recursive build (e.g., via
topological-based build of an initial key's dependencies).
-/

namespace Lake

/-! ## Pure State -/

/-- The type of the Lake build store. -/
public  abbrev BuildStore :=
  Std.DTreeMap BuildKey (Job <| BuildData ·) BuildKey.quickCmp

/-- Returns a new empty build store. -/
@[inline] public def BuildStore.empty : BuildStore := Std.DTreeMap.empty

/-! ## Atomic Mutable Reference -/

/-- A mutable reference to the Lake build store. -/
public abbrev BuildStoreRef := Std.Mutex BuildStore

namespace BuildStoreRef

/-- Creates a new mutable build store. -/
@[inline] public def new (s : BuildStore := {}) : BaseIO BuildStoreRef :=
  Std.Mutex.new s

/-- Atomically applies a pure modifucation to the build store. -/
@[inline] public def modify (f : BuildStore → BuildStore)  (r : BuildStoreRef) : BaseIO Unit :=
  r.atomically (·.modify f)

/-- Atomically pplies a pure modifucation to the build store and returns the paired value. -/
@[inline] public def modifyGet (f : BuildStore → (α × BuildStore)) (r : BuildStoreRef)  : BaseIO α :=
  r.atomically (·.modifyGet f)

/-- Reads the current value of the build store, returning a snapshot of its state. -/
@[inline] public def get (r : BuildStoreRef) : BaseIO BuildStore :=
  r.atomically (·.get)

/-- Atomically returns a projection of current value of the build store. -/
@[inline] public def getMap (f : BuildStore → α) (r : BuildStoreRef) : BaseIO α :=
  r.atomically fun ref => return f (← ref.get)

/--
Atomically returns the build store's saved job for the build key {lean}`k`, if any.
Otehrwise, returns {lean}`none`.
-/
@[inline] public def fetch? (k : BuildKey) [FamilyOut BuildData k α] (r : BuildStoreRef) : BaseIO (Option (Job α)) :=
  r.getMap fun s => cast (by simp) <| s.get? k

/-- Atomically inserts a new build job into the build store. -/
@[inline] public def store (k : BuildKey) [FamilyDef BuildData k α] (v : Job α)  (r : BuildStoreRef) : BaseIO Unit :=
  r.modify (·.insert k (cast (by simp) v))

end BuildStoreRef

/-! ## Monadic Interaction -/

/--
Transformer to equip a monad with a mutable Lake build store.

An internal monad. **Not intended for user use.**
-/
public abbrev BuildStoreT := ReaderT BuildStoreRef

/---
Runs the monadic action {lean}`x` over the build store {lean}`s`,
returning the monadic result paired with the final state of the build store.
-/
@[inline] public nonrec def BuildStoreT.run
  [Monad m] [MonadLiftT BaseIO m]
  (s : BuildStore := {}) (x : BuildStoreT m α)
: m (α × BuildStore) := do
  let ref ← BuildStoreRef.new s
  let a ← x.run ref
  let s ← ref.get
  return (a, s)

/-- A monad equipped with a Lake build store. -/
public abbrev MonadBuildStore (m) := MonadDStore BuildKey (Job <| BuildData ·) m

public instance [Monad m] [MonadLiftT BaseIO m] : MonadBuildStore (BuildStoreT m) where
  fetch? k := fun r => r.fetch? k
  store k v := fun r => r.store k v
