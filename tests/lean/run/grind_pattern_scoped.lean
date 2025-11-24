import Lean.Meta.Tactic.Grind.EMatchTheorem

open Lean
open Lean.Meta.Grind

/-- info: Namespaces with `scoped grind_pattern` includes `Lean.Meta.Grind.Lia`: true -/
#guard_msgs in
run_cmd do
  let stateStack := ematchTheoremsExt.ext.getState (← getEnv)
  let allNamespaces := stateStack.scopedEntries.map.fold (init := #[]) (fun acc k _ => acc.push k)
  logInfo s!"Namespaces with `scoped grind_pattern` includes `Lean.Meta.Grind.Lia`: {allNamespaces.contains `Lean.Meta.Grind.Lia}"

-- Test namespace-based theorem instantiation
example (x y : Int) (h : max x y < 7) : x + y < 13 := by
  grind =>
    use [ns Lean.Meta.Grind.Lia]
    repeat (first (lia) (cases_next))
