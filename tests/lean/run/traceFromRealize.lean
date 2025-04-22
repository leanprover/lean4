import Lean

set_option trace.Elab.debug true

def foo := True

open Lean Meta

run_meta
    realizeConst ``foo `foo.test do
      trace[Elab.debug] "realized"
      addDecl <| Declaration.thmDecl {
        name := `foo.test
        type := mkConst ``True
        value := mkConst ``True.intro
        levelParams := []
      }
