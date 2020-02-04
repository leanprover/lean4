import Init.Lean.Parser

def test : IO Unit :=
if System.Platform.isWindows then
  pure () -- TODO investigate why the following doesn't work on Windows
else do
  env ← Lean.mkEmptyEnvironment;
  Lean.Parser.parseFile env (System.mkFilePath ["..", "..", "..", "src", "Init", "Core.lean"]);
  IO.println "done"

#eval test
