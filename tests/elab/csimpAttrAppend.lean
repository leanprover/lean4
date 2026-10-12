set_option trace.Compiler.toImpure true
def f (as bs cs : List Nat) : List Nat :=
  as ++ bs ++ cs
