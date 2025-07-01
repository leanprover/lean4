/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Simp.UsedSimps

/--
Returns all entries with the exact provided key sequence, or `#[]` if the key sequence could not be
found in the tree.
-/
private def traverseTree (keys : Array DiscrTree.Key) (d : DiscrTree α) : Array α :=
  match d.root.find? keys[0]! with
  | none => #[]
  | some t => go t 1
where
  go (t : DiscrTree.Trie α) (i : Nat) : Array α :=
    if _ : i < keys.size then
      let next := t.2
      match next.binSearch (keys[i], default) (fun a b => a.1 < b.1) with
      | none => #[]
      | some t => go t.2 (i + 1)
    else
      t.1

/--
List of references into the `result` array of theorems with equal keys with optional cached
entries and entry indices.
-/
private inductive Lookup (α : Type) where
  /-- Single entry, no duplicates -/
  | simple (idx : Nat) (entry : α)
  /--
  `idxs` = array of `(index into result, index into entries)`.
  Sorted by priority (if applicable) and index into entries.
  -/
  | collision (idxs : Array (Nat × Nat)) (entries : Array α)

/--
Inserts a reference entry and swaps it into the right place while adjust the result array order.
-/
private def insertLookupEntry [BEq α] [Inhabited α] (arr : Array Origin)
      (refs : Array (Nat × Nat)) (entries : Array α)
      (idx : Nat) (entry : α) (prio : α → Nat) :
    Array Origin × Array (Nat × Nat) :=
  let sz := refs.size
  let eidx := entries.idxOf entry
  let refs := refs.push (idx, eidx)
  go arr refs eidx sz
where
  -- insertion sort
  go (arr : Array Origin) (refs : Array (Nat × Nat)) (eidx : Nat) : Nat → Array Origin × Array (Nat × Nat)
  | 0 => (arr, refs)
  | k + 1 =>
    let (idx', eidx') := refs[k]!
    let entry' := entries.getD eidx' default
    -- need to swap?
    if (prio entry' < prio entry || (prio entry = prio entry' && eidx < eidx')) ^^ idx < idx' then
      go (arr.swapIfInBounds idx idx') (refs.swapIfInBounds k (k + 1)) eidx k
    else
      (arr, refs)

/--
Insert the reference `idx` into the lookup with the given keys and adjust the result array order.
Entries may be accessed using `findAll` and priorities may be calculated using `prio`.
-/
private def mergeLookup [BEq α] [Inhabited α] (idx : Nat) (entry : α)
    (keys : Array DiscrTree.Key) (prio : α → Nat) (findAll : Unit → Array α)
    (arr : Array Origin) (map : Std.HashMap (Array DiscrTree.Key) (Lookup α)) :
    Array Origin × Std.HashMap (Array DiscrTree.Key) (Lookup α) :=
  let result := map[keys]?
  match result with
  | none => (arr, map.insert keys (.simple idx entry))
  | some (.simple idx' e) =>
    let entries := findAll ()
    let (arr, refs) := insertLookupEntry arr #[(idx', entries.idxOf e)] entries idx entry prio
    (arr, map.insert keys (.collision refs entries))
  | some (.collision idxs entries) =>
    let map := map.erase keys
    let (arr, refs) := insertLookupEntry arr idxs entries idx entry prio
    (arr, map.insert keys (.collision refs entries))

/--
Returns all used simplification theorems in the correct order to allow roundtripping.

Note: The entries may still be in such an order that the resulting `simp only` differs in behavior
from `simp`. This however should only occur when custom simp sets are involved.
-/
def getEntries (s : UsedSimps) (thms : SimpTheoremsArray) (simprocs : SimprocsArray := #[]) :
    CoreM (Array Origin) := do
  let mut result : Array Origin := Array.replicate s.size default
  let mut pre : Std.HashMap (Array SimpTheoremKey) (Lookup SimpTheorem) := ∅
  let mut post : Std.HashMap (Array SimpTheoremKey) (Lookup SimpTheorem) := ∅
  let mut preSimprocs : Std.HashMap (Array SimpTheoremKey) (Lookup Name) := ∅
  let mut postSimprocs : Std.HashMap (Array SimpTheoremKey) (Lookup Name) := ∅
  for (origin, i, thm) in s.map do
    result := result.set! i origin
    if thm.keys.isEmpty then
      let .decl nm isPost false := origin | continue
      let some keys ← getSimprocDeclKeys? nm | continue
      if isPost then
        let (result', post') := mergeLookup i nm keys (fun _ => 0)
          (fun _ => simprocs.flatMap (fun a => (traverseTree keys a.post).map (·.declName)))
          result postSimprocs
        result := result'; postSimprocs := post'
      else
        let (result', pre') := mergeLookup i nm keys (fun _ => 0)
          (fun _ => simprocs.flatMap (fun a => (traverseTree keys a.pre).map (·.declName)))
          result postSimprocs
        result := result'; preSimprocs := pre'
    else if thm.post then
      let (result', post') := mergeLookup i thm thm.keys (·.priority)
        (fun _ => thms.flatMap (fun a => traverseTree thm.keys a.post)) result post
      result := result'; post := post'
    else
      let (result', pre') := mergeLookup i thm thm.keys (·.priority)
        (fun _ => thms.flatMap (fun a => traverseTree thm.keys a.pre)) result pre
      result := result'; pre := pre'
  return result

end Lean.Meta.Simp.UsedSimps
