import Lean.Meta.Tactic.Grind.EMatchTheorem
import Lean.Meta.Tactic.Grind.Attr

open Lean
open Lean.Meta.Grind

/-- info: Namespace `Lean.Meta.Grind.Lia` has scoped theorems: true -/
#guard_msgs in
#eval show CoreM Unit from do
  let ext := Lean.Meta.Grind.grindExt
  let theorems ← ext.getEMatchTheoremsForNamespace `Lean.Meta.Grind.Lia
  IO.println s!"Namespace `Lean.Meta.Grind.Lia` has scoped theorems: {decide (theorems.size > 0)}"

-- Test namespace-based theorem instantiation
example (x y : Int) (h : max x y < 7) : x + y < 13 := by
  grind =>
    use [namespace Lean.Meta.Grind.Lia]
    repeat (first (lia) (cases_next))
