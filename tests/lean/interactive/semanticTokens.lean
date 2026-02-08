def foo1 (x : Nat) := x.succ
def foo2 (x : Nat) := x |>.succ
theorem foo3 (x : Nat) : True :=
  let y := x.succ
  True.intro

#eval 1
--^ collectDiagnostics
--^ textDocument/semanticTokens/full
