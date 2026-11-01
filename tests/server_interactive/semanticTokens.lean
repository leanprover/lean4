/-! This file tests semantic token kinds. -/

def foo1 (x : Nat) := x.succ
def foo2 (x : Nat) : List Nat := .cons.{0} (x |>.succ) .nil
theorem foo3 (x : Nat) : True :=
  let y := x.succ
  .intro

#eval 1
--^ collectDiagnostics
--^ textDocument/semanticTokens/full
