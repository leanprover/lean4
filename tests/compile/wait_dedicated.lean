/- Ensure we wait on dedicated tasks even after main is finished -/

def stuff : IO Unit := do
  IO.sleep 100
  IO.println "Hi there"


def main : IO Unit := do
  discard <| IO.asTask (prio := .dedicated) stuff

