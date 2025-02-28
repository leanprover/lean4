/-
Copyright (c) 2025 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Lean

/-!
For which ordered pairs of types `(X, Y)` does there exist a `X.toY` function, a `Y.ofX` function
or both?
-/

open Lean Meta

def blub : MetaM Unit := do
  let env ← getEnv
  let mut pairs : Array (String × String) := #[]
  let mut singles : Std.HashMap String (Array String × Array String) := ∅
  for (name, info) in env.constants do
    if info.isTheorem then
      continue
    if (`Lean).isPrefixOf name || (`_private).isPrefixOf name then
      continue
    let Name.str i@(Name.str inner n) s := name | continue
    if let some t := s.dropPrefix? "of" then
      let otherName := Name.str (Name.str inner t.toString) ("to" ++ n)
      if env.contains otherName then
        pairs := pairs.push (name.toString, otherName.toString)
      else
        singles := singles.alter i.toString (·.getD (#[], #[]) |>.map id (·.push s))
    else if s.startsWith "to" then
      singles := singles.alter i.toString (·.getD (#[], #[]) |>.map (·.push s) id)

  have : Ord (String × String) := lexOrd
  have : Ord (String × (Array String × Array String)) := ⟨(compare ·.1 ·.1)⟩
  pairs := pairs.qsortOrd
  let singlesArr := singles.toArray.qsortOrd

  for n in pairs do
    IO.println n
  for (n, tos, ofs) in singlesArr do
    IO.println s!"{n}|{String.intercalate ", " tos.toList}|{String.intercalate ", " ofs.toList}"

#eval blub
