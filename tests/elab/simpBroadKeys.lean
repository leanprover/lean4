import Lean

open Lean Meta in
#eval show MetaM Unit from do
  let thms ← getSimpTheorems
  let env ← getEnv
  let mut bad : Array (Name × Array DiscrTree.Key) := #[]
  let collect := fun (bad : Array (Name × Array DiscrTree.Key))
      (keys : Array DiscrTree.Key) (thm : SimpTheorem) =>
    if keys == #[.star] || keys == #[.arrow, .star] then
      match thm.origin with
      | .decl declName .. =>
        if let some modIdx := env.getModuleIdxFor? declName then
          let modName := env.allImportedModuleNames[modIdx.toNat]!
          if modName.getRoot == `Init || modName.getRoot == `Std || modName.getRoot == `Lean then
            bad.push (declName, keys)
          else
            bad
        else
          bad
      | _ => bad
    else
      bad
  bad := thms.post.fold collect bad
  bad := thms.pre.fold collect bad
  if !bad.isEmpty then
    let msgs := bad.map fun (n, keys) =>
      let keysStr := keys.map (fun k => s!"{k.format}") |>.toList |> String.intercalate " "
      s!"{n} [{keysStr}]"
    throwError "simp theorems with overly broad discrimination tree keys:\n{"\n".intercalate msgs.toList}"
  return ()
