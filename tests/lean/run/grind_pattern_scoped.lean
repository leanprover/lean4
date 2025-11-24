import Lean.Meta.Tactic.Grind.EMatchTheorem

open Lean
open Lean.Meta.Grind

-- This should show the scoped grind_pattern in `Int`
-- Check ALL scoped entries in the environment
run_cmd do
  let stateStack := ematchTheoremsExt.ext.getState (← getEnv)
  let allNamespaces := stateStack.scopedEntries.map.fold (init := #[]) (fun acc k _ => acc.push k)
  logInfo s!"All scoped grind_pattern namespaces: {allNamespaces}"

namespace Foo
scoped grind_pattern Int.max_def => max n m
end Foo

run_cmd do
  let stateStack := ematchTheoremsExt.ext.getState (← getEnv)
  let allNamespaces := stateStack.scopedEntries.map.fold (init := #[]) (fun acc k _ => acc.push k)
  logInfo s!"All scoped grind_pattern namespaces: {allNamespaces}"


-- Test namespace-based theorem instantiation
example (x y : Int) (h : max x y < 7) : x + y < 13 := by
  grind =>
    use [ns Int]
    repeat (first (lia) (cases_next))

-- Test namespace-based theorem instantiation
example (x y : Int) (h : max x y < 7) : x + y < 13 := by
  grind =>
    use [ns Foo]
    repeat (first (lia) (cases_next))
