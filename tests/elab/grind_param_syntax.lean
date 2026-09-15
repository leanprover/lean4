module
import Lean

/-!
Check that sharing modifier parsers preserves anonymous modifier quotations (#15116).
-/

open Lean

macro "lia_modified " mod:Lean.Parser.Attr.grindMod e:term : tactic => do
  let p ← `(Lean.Parser.Tactic.grindParam| $mod $e:term)
  `(tactic| lia [$p:grindParam])

private def bump (x : Int) := x + 1
private theorem bump_def (x : Int) : bump x = x + 1 := rfl

example (x : Int) : x < bump x := by lia_modified = bump_def
