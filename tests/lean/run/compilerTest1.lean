import Lean

import Lean.Meta.Constructions.CasesOn
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.SolveByElim

namespace Lean.Meta.IndPredBelow
open Match

-- def mkBelow'' (declName : Name) : MetaM Unit := do
--   if (← isInductivePredicate declName) then
--     let x ← getConstInfoInduct declName
--     if x.isRec && !x.isNested then
--       let ctx ← IndPredBelow.mkContext declName
--       let decl ← IndPredBelow.mkBelowDecl ctx
--       addDecl decl
--       trace[Meta.IndPredBelow] "added {ctx.belowNames}"
--       ctx.belowNames.forM Lean.mkCasesOn
--       for i in *...ctx.typeInfos.size do
--         try
--           let decl ← IndPredBelow.mkBrecOnDecl ctx i
--           -- disable async TC so we can catch its exceptions
--           withOptions (Elab.async.set · false) do
--             addDecl decl
--         catch e => trace[Meta.IndPredBelow] "failed to prove brecOn for {ctx.belowNames[i]!}\n{e.toMessageData}"
--     else trace[Meta.IndPredBelow] "Nested or not recursive"
--   else trace[Meta.IndPredBelow] "Not inductive predicate"

run_meta Lean.Compiler.compile #[``Lean.Elab.Structural.structuralRecursion, ``Lean.Elab.Command.elabInductives, ``Lean.Environment.displayStats, ``Lean.Meta.IndPredBelow.mkBelow', ``unexpandExists]
