import Lean

/-!
This tests that all polymorphic higher-order monadic definitions have a monotonicit lemma.
-/

open Lean Meta

def go : MetaM Unit := do
  let modNames := (← getEnv).allImportedModuleNames
  for (name, ci) in (← getEnv).constants do
    if ci.isTheorem then continue
    if name.isInternal then continue
    let some idx := (← getEnv).getModuleIdxFor? name | continue
    if (`Lean).isPrefixOf modNames[idx.toNat]! then continue

    forallTelescope ci.type fun xs r => do
      unless r.isApp do return
      unless r.appFn!.isFVar do return
      let m := r.appFn!
      let xst ← xs.mapM inferType
      unless xst.any (fun x => x.isAppOfArity ``Monad 1 && x.appArg! == m) do return
      unless (← xst.anyM fun x =>
        forallTelescope x fun _ x =>
          return x.getAppFn == m
        ) do return
      logInfo m!"{.ofConstName name}"

run_meta go
