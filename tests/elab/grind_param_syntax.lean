module
import Lean

/-!
Check that sharing modifier parsers preserves typed parameter-list splices and anonymous
modifier quotations (#15116).
-/

open Lean

macro "lia_with " ps:Lean.Parser.Tactic.grindParam,* : tactic =>
  `(tactic| lia [$ps,*])

macro "lia_modified " mod:Lean.Parser.Attr.grindMod e:term : tactic => do
  let p ← `(Lean.Parser.Tactic.grindParam| $mod $e:term)
  `(tactic| lia [$p:grindParam])

private def bump (x : Int) := x + 1
private theorem bump_def (x : Int) : bump x = x + 1 := rfl

example (x : Int) : x < bump x := by lia_with = bump_def
example (x : Int) : x < bump x := by lia_modified = bump_def
