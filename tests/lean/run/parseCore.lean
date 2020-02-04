import Init.Lean.Parser

def test : IO Unit := do
env ← Lean.mkEmptyEnvironment;
Lean.Parser.parseFile env ("../../../src/Init/Core.lean");
IO.println "done"

#eval test
