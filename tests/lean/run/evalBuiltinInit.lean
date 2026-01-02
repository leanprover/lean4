import Lean

-- option should be ignored when evaluating a `[builtin_init]` decl
--set_option interpreter.prefer_native false
-- this test is broken without a stage0 update

/-- info: "formatter" -/
#guard_msgs in
#eval! toString Lean.PrettyPrinter.formatterAttribute.defn.name
