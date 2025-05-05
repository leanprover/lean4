namespace Test

open Lean

/-- info: `Test -/
#guard_msgs in
#eval Macro.getCurrNamespace

/-- error: thrown -/
#guard_msgs in
run_macro Macro.throwError (α := Unit) "thrown"

run_cmd_macro (TSyntax.mk <| mkNullNode ·) <$> #[`foo, `bar].mapM fun name =>
  `(def $(mkIdent name) := $(quote name.toString))

/-- info: "foobar" -/
#guard_msgs in #eval foo ++ bar
