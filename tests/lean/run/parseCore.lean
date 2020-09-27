import Lean.Parser
new_frontend
def test : IO Unit :=
if System.Platform.isWindows then
  pure () -- TODO investigate why the following doesn't work on Windows
else do
  let env ← Lean.mkEmptyEnvironment;
  Lean.Parser.parseFile env (System.mkFilePath ["..", "..", "..", "src", "Init", "Core.lean"]);
  IO.println "done"

#eval test
