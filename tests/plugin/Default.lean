import Init.Lean

open Lean

def oh_no : Nat := 0

def snakeLinter : Linter :=
fun env n =>
  -- TODO(Sebastian): return actual message with position from syntax tree
  if n.toString.contains '_' then throw "SNAKES!!"
  else pure MessageLog.empty

@[init]
def registerSnakeLinter : IO Unit :=
addLinter snakeLinter
