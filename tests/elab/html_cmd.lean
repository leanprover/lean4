import Lean.Data.Html

/-! Tests for the `#html` command. -/

open Lean Html Elab Command Meta

/-! # Pure values -/

/-- info: <p>hello</p> -/
#guard_msgs in
#html html%{<p>hello</p>}

/-! # Monadic values -/

/-- info: <i>IO</i> -/
#guard_msgs in
#html (pure html%{<i>IO</i>} : IO Html)

/-- info: <code>Nat</code> -/
#guard_msgs in
#html show MetaM Html from do
  let ty ← ppExpr (mkConst ``Nat)
  return html%{<code>{toString ty}</code>}

-- Like `#eval`, `#html` accepts any monad with a `MonadEval` instance.
abbrev M := ReaderT Nat IO

instance : MonadEval M IO where
  monadEval x := x.run 42

/-- info: <b>42</b> -/
#guard_msgs in
#html show M Html from return html%{<b>{toString (← read)}</b>}

/-! # Errors -/

/--
error: Expected a value of type `Html`, but got
  String
-/
#guard_msgs in
#html "not html"

/--
error: Expected a value of type `Html`, but got
  Unit
-/
#guard_msgs in
#html (pure () : IO Unit)

/--
error: Unable to synthesize `MonadEval` instance to adapt
  StateM Nat Html
to `IO` or `CommandElabM`.
-/
#guard_msgs in
#html (pure html%{<p/>} : StateM Nat Html)
