import Lean.Parser

def test : IO Unit := do
  let env ← Lean.mkEmptyEnvironment;
  discard <| Lean.Parser.testParseFile env (System.mkFilePath ["..", "..", "..", "src", "Init", "Prelude.lean"]);
  IO.println "done"

#eval test
