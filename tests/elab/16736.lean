import Lean
open Lean

inductive Foo (α : Type) : Type | mk : Foo α   -- phantom parameter

/-- info: REJECTED: (kernel) unknown constant 'T.nil' -/
#guard_msgs in
run_meta do
  let T := Expr.const `T []
  -- D := (fun _ : T => Nat) T.nil   — mentions the block's own constructor
  let D := Expr.app (.lam `x T (.const ``Nat []) .default) (.const `T.nil [])
  let ctorMk := Expr.forallE `a (mkApp (.const `Foo []) D) T .default
  let d := Declaration.inductDecl [] 0
    [{ name := `T, type := .sort 1,
       ctors := [{ name := `T.nil, type := T }, { name := `T.mk, type := ctorMk }],
       isImpredicative := false, isK := false, hasProjections := false, hasEta := false,
       hasLargeElim := true }] false
  try
    addDecl d
    let some ci := (← getEnv).find? `T.mk | throwError "no T.mk"
    logInfo m!"ACCEPTED. stored T.mk : {ci.type}"
  catch e => logInfo m!"REJECTED: {e.toMessageData}"
