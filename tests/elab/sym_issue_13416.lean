import Lean.Meta.Sym
import Std.Data.HashMap.Lemmas

open Lean Meta Sym Simp in
/--
info: lhs: (Std.HashMap.emptyWithCapacity.insert "foo" 42)["foo"]
---
info: disc tree lookup match count: 1
-/
#guard_msgs in
#eval show MetaM Unit from do
  -- Insert `HashMap.getElem_insert` into a fresh Theorems tree.
  -- Its `dom` argument is `fun m a => Membership.mem m a` with loose bvars → key `.other`
  let thm ← mkTheoremFromDecl ``Std.HashMap.getElem_insert
  let tree : Theorems := ({} : Theorems).insert thm

  -- Build a concrete expression that should match.
  -- Its `dom` argument is the same lambda but closed → etaReduce → key `.const Membership.mem 3`
  let lhs ← do
    let ty ← Lean.Elab.Term.TermElabM.run' (ctx := {}) do
      return ← Lean.Elab.Term.elabTerm
        (← `(((Std.HashMap.emptyWithCapacity : Std.HashMap String Nat).insert "foo" 42)["foo"]'(by simp) = 42))
        none
    let ty ← instantiateMVars ty
    let some (_, lhs, _) := ty.eq? | throwError "not eq"
    pure lhs

  logInfo m!"lhs: {lhs}"

  guard <| lhs.getAppFn.constName? == some ``GetElem.getElem
  guard <| lhs.getAppNumArgs == 8

  -- Confirm the dom argument is eta-reducible in the concrete expression
  let dom := lhs.getAppArgs[3]!
  guard dom.isLambda
  guard <| !(Lean.Expr.eta dom).isLambda

  let nMatches := (tree.getMatchWithExtra lhs).size
  logInfo m!"disc tree lookup match count: {nMatches}"
