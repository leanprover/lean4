import Lean.Meta.Sym

open Lean Meta Sym

opaque P : (Type → Type) → Prop
axiom stateT_P : P (StateT Nat Id)

/--
info: disc tree lookup match count: 1
-/
#guard_msgs in
#eval show MetaM Unit from do
  -- `StateM Nat` unfolds to `fun α => StateT Nat Id α` (an eta redex)
  let e ← Sym.unfoldReducible (mkApp (mkConst ``P) (mkApp (mkConst ``StateM [0]) (mkConst ``Nat)))
  -- Verify the eta redex is present
  assert! e.appArg!.isLambda
  let pat ← mkPatternFromDecl ``stateT_P
  let dt := Sym.insertPattern (Lean.Meta.DiscrTree.empty (α := Unit)) pat ()
  let nMatches := (Sym.getMatch dt e).size
  logInfo m!"disc tree lookup match count: {nMatches}"
