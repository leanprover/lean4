import GroveStdlib.Root
import GroveStdlib.Generated

def config : Grove.Framework.Project.Configuration where
  projectNamespace := `GroveStdlib

def project : Grove.Framework.Project where
  config := config
  rootNode := GroveStdlib.root
  restoreState := GroveStdlib.Generated.restoreState

def main (args : List String) : IO UInt32 :=
  Grove.Framework.main project #[`Init, `Std, `Lean] args
