set_option trace.Compiler.floatLetIn true in
def provokeFloatLet (x y : Nat) (cond : Bool) : Nat :=
  let a := x ^ y
  let b := x + y
  let c := x - y
  let dual := x * y
  if cond then
    match dual with
    | 0 => a
    | _ + 1 => c
  else
    b + dual
