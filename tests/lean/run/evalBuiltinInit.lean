import Lean

-- option should be ignored when evaluating a `[builtinInit]` decl
set_option interpreter.prefer_native false
#eval toString Lean.PrettyPrinter.formatterAttribute.defn.name
