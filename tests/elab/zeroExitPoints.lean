set_option trace.Compiler.result true
def f (x : Empty) (y : Nat) : Nat :=
  let g (h : Unit → Empty) : Nat := h () |>.casesOn
  let aux := g fun _ => x
  y + aux
