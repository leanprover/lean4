import Lean
import SimpModuleIndex.B
import SimpModuleIndex.N

/-!
Simp sets imported from theorem trees stored in the oleans (`SimpModuleIndex`) equal those obtained
by adding each imported entry in module order.
-/

open Lean Meta

example : SMI.f 0 = 1 := by simp
example : SMI.f 1 = 2 := by simp
example : SMI.f (SMI.f 3) = 5 := by simp
example : SMI.f 2 = 3 := by
  fail_if_success simp
  rfl
open SMI.Sc in
example : SMI.f 2 = 3 := by simp
-- `M` is imported at the private level here
example : SMI.m 1 = 3 := by simp
example (n : Nat) : SMI.q n = SMI.p n := by simp

def sequentialState (ext : SimpExtension) (env : Environment) : SimpTheorems :=
  (ext.ext.toEnvExtension.getState env).importedEntries.foldl (init := {}) fun d es =>
    es.foldl (init := d) fun d e => match e with
      | .global e => d.addSimpEntry e
      | _ => d

def treeContents (t : SimpTheoremTree) : Array (Array DiscrTree.Key × Name × Nat × Bool × Bool) :=
  t.toArray.map fun (ks, thm) => (ks, thm.origin.key, thm.priority, thm.post, thm.perm)

def sortedNames (ns : List Name) : List Name :=
  ns.toArray.qsort Name.lt |>.toList

def sameState (d₁ d₂ : SimpTheorems) : Bool :=
  treeContents d₁.pre == treeContents d₂.pre &&
  treeContents d₁.post == treeContents d₂.post &&
  d₁.lemmaNames.toList.map (·.key) == d₂.lemmaNames.toList.map (·.key) &&
  d₁.erased.toList.map (·.key) == d₂.erased.toList.map (·.key) &&
  sortedNames d₁.toUnfold.toList == sortedNames d₂.toUnfold.toList &&
  sortedNames (d₁.toUnfoldThms.toList.map (·.1)) == sortedNames (d₂.toUnfoldThms.toList.map (·.1))

#eval show MetaM Unit from do
  let env ← getEnv
  -- the modules of this package store their index
  for mod in [`SimpModuleIndex.A, `SimpModuleIndex.B, `SimpModuleIndex.M] do
    let some modIdx := env.getModuleIdx? mod | throwError "{mod} not imported"
    let es := (simpExtension.ext.toEnvExtension.getState env).importedEntries[modIdx.toNat]!
    unless (es[0]? : Option (ScopedEnvExtension.Entry SimpEntry)) matches some (.index _) do
      throwError "{mod} has no stored index"
  for (attr, ext) in (← simpExtensionMapRef.get) do
    unless sameState (ext.getState env) (sequentialState ext env) do
      throwError "simp set `{attr}` differs from the sequentially built one"
  let d ← getSimpTheorems
  unless d.erased.contains (.decl ``SMI.p_q) do throwError "forward `p_q` not erased"
  unless (← d.post.getMatch (mkApp (mkConst ``SMI.f) (mkNatLit 0))).any (·.priority == 2000) do
    throwError "`f_zero` priority not replaced"
