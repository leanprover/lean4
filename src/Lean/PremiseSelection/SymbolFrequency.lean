/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.CoreM
import Lean.Meta.InferType
import Lean.Meta.FunInfo
import Lean.AddDecl

/-!
# Symbol frequency

This module provides a persistent environment extension for computing the frequency of symbols in the environment.
-/

namespace Lean.PremiseSelection

namespace FoldRelevantConstsImpl

open Lean Meta

unsafe structure State where
 visited       : PtrSet Expr := mkPtrSet
 visitedConsts : NameHashSet := {}

unsafe abbrev FoldM := StateT State MetaM

unsafe def fold {α : Type} (f : Name → α → MetaM α) (e : Expr) (acc : α) : FoldM α :=
  let rec visit (e : Expr) (acc : α) : FoldM α := do
    if (← get).visited.contains e then
      return acc
    modify fun s => { s with visited := s.visited.insert e }
    if ← isProof e then
      -- Don't visit proofs.
      return acc
    match e with
    | .forallE n d b bi  =>
      let r ← visit d acc
      withLocalDecl n bi d fun x =>
        visit (b.instantiate1 x) r
    | .lam n d b bi      =>
      let r ← visit d acc
      withLocalDecl n bi d fun x =>
        visit (b.instantiate1 x) r
    | .mdata _ b         => visit b acc
    | .letE n t v b nondep    =>
      let r₁ ← visit t acc
      let r₂ ← visit v r₁
      withLetDecl n t v (nondep := nondep) fun x =>
        visit (b.instantiate1 x) r₂
    | .app f a           =>
      let fi ← getFunInfo f (some 1)
      if fi.paramInfo[0]!.isInstImplicit then
        -- Don't visit implicit arguments.
        visit f acc
      else
        visit a (← visit f acc)
    | .proj _ _ b        => visit b acc
    | .const c _         =>
      if (← get).visitedConsts.contains c then
        return acc
      else
        modify fun s => { s with visitedConsts := s.visitedConsts.insert c };
        f c acc
    | _ => return acc
  visit e acc

@[inline] unsafe def foldUnsafe {α : Type} (e : Expr) (init : α) (f : Name → α → MetaM α) : MetaM α :=
  (fold f e init).run' {}

end FoldRelevantConstsImpl

/-- Apply `f` to every constant occurring in `e` once, skipping instance arguments and proofs. -/
@[implemented_by FoldRelevantConstsImpl.foldUnsafe]
opaque foldRelevantConsts {α : Type} (e : Expr) (init : α) (f : Name → α → MetaM α) : MetaM α := pure init

/-- Helper function for running `MetaM` code during module export. We have nothing but an `Environment` available. -/
private def runMetaM [Inhabited α] (env : Environment) (x : MetaM α) : α :=
   match unsafe unsafeEIO ((((withoutExporting x).run' {} {}).run' { fileName := "symbolFrequency", fileMap := default } { env })) with
   | Except.ok a => a
   | Except.error ex => panic! match unsafe unsafeIO ex.toMessageData.toString with
     | Except.ok s => s
     | Except.error ex => ex.toString

/--
The state is just an array of array of maps.
We don't assemble these on import for efficiency reasons: most modules will not query this extension.

Instead, we use an `IO.Ref` below so that within each module we can assemble the global `NameMap Nat` once.

Since we never modify the extension state except on export, the `IO.Ref` does not need updating after first access.
-/
builtin_initialize symbolFrequencyExt : PersistentEnvExtension (NameMap Nat) Empty (Array (Array (NameMap Nat))) ←
  registerPersistentEnvExtension {
    name            := `symbolFrequency
    mkInitial       := pure ∅
    addImportedFn   := fun mapss _ => pure mapss
    addEntryFn      := nofun
    exportEntriesFnEx := fun env _ _ => runMetaM env do
      let r ← env.constants.map₂.foldlM (init := (∅ : NameMap Nat)) (fun acc n ci => do
        if n.isInternalDetail || !Lean.wasOriginallyTheorem env n then
          pure acc
        else
          foldRelevantConsts ci.type (init := acc) fun n' acc => pure (acc.alter n' fun i? => some (i?.getD 0 + 1)))
      return #[r]
    statsFn         := fun _ => "symbol frequency extension"
  }

/-- A global `IO.Ref` containing the symbol frequency map. This is initialized on first use. -/
builtin_initialize symbolFrequencyMapRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none

private local instance : Zero (NameMap Nat) := ⟨∅⟩
private local instance : Add (NameMap Nat) where
  add x y := y.foldl (init := x) fun x' n c => x'.insert n (x'.getD n 0 + c)

/-- The symbol frequency map for imported constants. This is initialized on first use. -/
def symbolFrequencyMap : CoreM (NameMap Nat) := do
  match ← symbolFrequencyMapRef.get with
  | some map => return map
  | none =>
    let mapss := symbolFrequencyExt.getState (← getEnv)
    let map := mapss.foldl (init := 0) fun acc maps => maps.foldl (init := acc) fun acc map => acc + map
    symbolFrequencyMapRef.set (some map)
    return map

/--
Return the number of times a `Name` appears
in the signatures of (non-internal) theorems in the imported environment,
skipping instance arguments and proofs.
-/
public def symbolFrequency (n : Name) : CoreM Nat :=
  return (← symbolFrequencyMap) |>.getD n 0
