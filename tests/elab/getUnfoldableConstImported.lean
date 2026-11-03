module

meta import Lean

open Lean Meta

/-!
Tests `getUnfoldableConst?`, which `whnf` and `isDefEq` use to find the definition to unfold.
Imported and current-module constants take different lookup paths, so the test checks both.
It also checks that a lookup of a theorem whose proof is still in elaboration returns `none`
without waiting for the proof.
-/

public abbrev localAbbrev : Nat := 0
public def localDef : Nat := 0
@[irreducible] public def localIrreducible : Nat := 0
public instance localInst : Inhabited Nat := ⟨0⟩
public theorem localThm : True := trivial
public axiom localAxiom : Nat

/-- Lists the transparency modes in which `getUnfoldableConst?` returns the constant. -/
private meta def unfoldModes (name : Name) : MetaM MessageData := do
  let mut modes := #[]
  for (mode, label) in #[(TransparencyMode.reducible, "reducible"), (.instances, "instances"),
      (.default, "default"), (.all, "all")] do
    if (← withTransparency mode <| getUnfoldableConst? name).isSome then
      modes := modes.push label
  return m!"{name}: {if modes.isEmpty then "never" else " ".intercalate modes.toList}"

/--
info: GE.ge: reducible instances default all
instAddNat: instances default all
List.map: default all
Nat.toDigits: never
Nat.add_comm: never
Nat: never
Nat.zero: never
Nat.rec: never
Quot: never
Classical.choice: never
localAbbrev: reducible instances default all
localDef: default all
localIrreducible: all
localInst: instances default all
localThm: never
localAxiom: never
-/
#guard_msgs in
run_meta do
  let names := #[``GE.ge, ``instAddNat, ``List.map, ``Nat.toDigits, ``Nat.add_comm, ``Nat,
    ``Nat.zero, ``Nat.rec, ``Quot, ``Classical.choice,
    ``localAbbrev, ``localDef, ``localIrreducible, ``localInst, ``localThm, ``localAxiom]
  logInfo <| .joinSep (← names.toList.mapM unfoldModes) "\n"

/-- error: Unknown constant `missingConstant` -/
#guard_msgs in
run_meta discard <| getUnfoldableConst? `missingConstant

/-! The proof is committed only after the lookup, so a lookup that waits for it never returns. -/
run_meta do
  let saved ← getEnv
  let pending ← saved.addConstAsync `pendingThm .thm
  setEnv pending.mainEnv
  unless (← getUnfoldableConst? `pendingThm).isNone do
    throwError "pending theorem became unfoldable"
  setEnv saved
  pending.commitConst pending.asyncEnv (info? := some <| .thmInfo {
    name := `pendingThm, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })
