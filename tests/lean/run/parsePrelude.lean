import Lean.Parser

def test : IO Unit :=
if System.Platform.isWindows then
  pure () -- TODO investigate why the following doesn't work on Windows
else do
  let env ← Lean.mkEmptyEnvironment;
  discard <| Lean.Parser.testParseFile env (System.mkFilePath ["..", "..", "..", "src", "Init", "Prelude.lean"]);
  IO.println "done"

#eval test
