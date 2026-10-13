module

meta import Lean

open Lean Meta

/-! Check imported lookups against the asynchronous path, including unfolding policies.
Current-module declarations must retain asynchronous lookup: theorem bodies need not be ready.
-/

private meta def referenceLookup (name : Name) : MetaM (Option ConstantInfo) := do
  let some info := (← getEnv).findAsync? name | throwUnknownConstantAt (← getRef) name
  match info.kind with
  | .defn => if (← canUnfold info.toConstantInfo) then return info.toConstantInfo else return none
  | _ => return none

private meta def checkLookup (name : Name) : MetaM Unit := do
  let expected ← referenceLookup name
  let actual ← getUnfoldableConst? name
  let summarize (info : ConstantInfo) := (info.name, info.type, info.value?)
  unless expected.map summarize == actual.map summarize do
    throwError "lookup differs for {name}"

private meta def checkImportedLookup : MetaM Unit := do
  let imported := #[``Nat.add, ``Bool.not, ``List.map, ``Nat.add_comm, ``Nat, ``Nat.zero,
    ``Nat.rec, ``True.intro, ``Eq.refl, ``Quot, ``Classical.choice]
  for name in imported do
    unless (← getEnv).isImportedConst name do
      throwError "expected imported constant: {name}"
  addDecl <| .defnDecl <| mkDefinitionValEx `localDef [] (mkConst ``Nat) (mkNatLit 0)
    .abbrev .safe []
  addDecl <| .axiomDecl <| mkAxiomValEx `localAxiom [] (mkConst ``Nat) false
  for mode in #[TransparencyMode.none, .reducible, .instances, .implicit, .default, .all] do
    withTransparency mode do
      for name in imported ++ #[`localDef, `localAxiom] do
        checkLookup name
  for allow in #[false, true] do
    withReader (fun ctx => { ctx with customCanUnfoldPredicate? := some fun _ _ => pure allow }) do
      for name in imported ++ #[`localDef, `localAxiom] do
        checkLookup name
      unless (← getUnfoldableConst? ``Nat.add).isSome == allow do
        throwError "custom unfolding predicate ignored"
  let failed ← try
    discard <| getUnfoldableConst? `missingConstant
    pure false
  catch _ => pure true
  unless failed do throwError "unknown constant did not fail"
  -- Keep both promises pending until after lookup. Waiting for either would deadlock.
  let pending ← (← getEnv).addConstAsync `pendingTheorem .thm
  let saved ← getEnv
  setEnv pending.mainEnv
  unless (← getUnfoldableConst? `pendingTheorem).isNone do
    throwError "pending theorem became unfoldable"
  setEnv saved
  pending.commitConst pending.asyncEnv (info? := some <| .thmInfo {
    name := `pendingTheorem, levelParams := [], type := mkConst ``True,
    value := mkConst ``True.intro })

run_meta checkImportedLookup
