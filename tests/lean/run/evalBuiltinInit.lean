import Lean

-- option should be ignored when evaluating a `[builtin_init]` decl
set_option interpreter.prefer_native false
/-- info: "formatter" -/
#guard_msgs in
#eval toString Lean.PrettyPrinter.formatterAttribute.defn.name
