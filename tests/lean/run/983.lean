import Lean

-- The `cases` tactic does not use `Lean.Meta.cases` under the hood,
-- so it is unaffected by this issue. We define a tactic
-- `mcases` that delegates to `Lean.Meta.cases`.
syntax (name := mcases) "mcases" ident : tactic

namespace Lean.Elab.Tactic

@[tactic mcases]
def evalMcases : Tactic
| `(tactic| mcases $hyp) => do
  let hyp ← getFVarId hyp
  liftMetaTactic fun goal => do
    let goals ← Lean.Meta.cases goal hyp
    return goals.map (·.mvarId) |>.toList
| _ => unreachable!

end Lean.Elab.Tactic

example : True := by
  let h : ∃ n, n = 0 := ⟨0, rfl⟩
  mcases h
  sorry -- sorry

example : True := by
  have h : ∃ n, n = 0 := ⟨0, rfl⟩
  mcases h
  apply True.intro
