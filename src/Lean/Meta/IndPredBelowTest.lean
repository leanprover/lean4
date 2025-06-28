/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
prelude
import Init.Data.Range.Polymorphic.Nat
import Lean.Meta.IndPredBelow

namespace Lean.Meta.IndPredBelow

/-- Generates the auxiliary lemmas `below` and `brecOn` for a recursive inductive predicate.
The current generator doesn't support nested predicates, but pattern-matching on them still works
thanks to well-founded recursion. -/
def mkBelow' (declName : Name) : MetaM Unit := do
  if (← isInductivePredicate declName) then
    let x ← getConstInfoInduct declName
    if x.isRec && !x.isNested then
      let ctx ← IndPredBelow.mkContext declName
      let decl ← IndPredBelow.mkBelowDecl ctx
      addDecl decl
      trace[Meta.IndPredBelow] "added {ctx.belowNames}"
      ctx.belowNames.forM Lean.mkCasesOn
      for i in *...ctx.typeInfos.size do
        try
          let decl ← IndPredBelow.mkBrecOnDecl ctx i
          -- disable async TC so we can catch its exceptions
          withOptions (Elab.async.set · false) do
            addDecl decl
        catch e => trace[Meta.IndPredBelow] "failed to prove brecOn for {ctx.belowNames[i]!}\n{e.toMessageData}"
    else trace[Meta.IndPredBelow] "Nested or not recursive"
  else trace[Meta.IndPredBelow] "Not inductive predicate"
