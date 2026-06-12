/-
MWE: `Sym.DiscrTree.getMatch` misses an entry whose `Pattern.match?` succeeds.

We insert patterns for `Spec.forIn_iterM_id` and `Spec.IterM.forIn_map` into a
`Sym.DiscrTree`. Looking up `forIn (IterM.map ...) ...` via `getMatch` returns only
`forIn_iterM_id`, but brute-force `Pattern.match?` also finds `IterM.forIn_map`.
-/
import Lean
import Std

open Lean Meta Sym Std Do

/-- Extract the program from a `@[spec]` theorem `∀ ..., Triple prog P Q`. -/
private def mkProgPattern (declName : Name) : MetaM Pattern := do
  let ci ← getConstInfo declName
  let expr ← mkExpectedTypeHint (← mkConstWithLevelParams declName) ci.type
  Prod.fst <$> (mkPatternFromExprWithKey expr ci.levelParams fun type => do
    let type ← whnfR type
    let_expr Triple _m _ps _inst _α prog _P _Q := type
      | throwError "not a Triple: {indentExpr type}"
    return (prog, ())).run' {}

/-- A `forIn` on a mapped iterator — the expression we want to look up. -/
noncomputable def lookupTerm : Id Unit :=
  forIn ((#[0].iterM Id).map id) () fun _ _ => pure (.yield ())

/--
info: getMatch:       [Std.Do.Spec.forIn_iterM_id, Std.Do.Spec.IterM.forIn_map]
pattern.match?: [Std.Do.Spec.IterM.forIn_map, Std.Do.Spec.forIn_iterM_id]
---
info: GOOD: getMatch and brute-force agree
-/
#guard_msgs in
#eval show MetaM Unit from do
  let patMap ← mkProgPattern ``Spec.IterM.forIn_map
  let patGeneric ← mkProgPattern ``Spec.forIn_iterM_id

  let mut tree : DiscrTree Name := .empty
  tree := insertPattern tree patMap ``Spec.IterM.forIn_map
  tree := insertPattern tree patGeneric ``Spec.forIn_iterM_id

  let e ← instantiateMVars (← getConstInfo ``lookupTerm).value?.get!
  let e ← SymM.run (shareCommon e)

  let treeResults := Sym.getMatch tree e
  let mut bruteResults : Array Name := #[]
  for (name, pat) in #[(``Spec.IterM.forIn_map, patMap), (``Spec.forIn_iterM_id, patGeneric)] do
    if let some _ ← SymM.run (pat.match? e) then
      bruteResults := bruteResults.push name

  logInfo m!"getMatch:       {treeResults}\npattern.match?: {bruteResults}"
  if treeResults.size < bruteResults.size then
    logInfo "BUG: getMatch missed entries that pattern.match? finds"
  else
    logInfo "GOOD: getMatch and brute-force agree"
