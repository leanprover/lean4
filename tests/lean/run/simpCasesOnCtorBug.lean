import Lean

def test1 (y : Nat) : Nat :=
  let x := 3
  match x with
  | 0 => y+1
  | .succ x => y + x

run_meta Lean.Compiler.compile #[``test1]

def test2 (y : Nat) : Nat :=
  let x := 3
  match x with
  | 0 => y+1
  | .succ x =>
    match x with
    | 0 => y+2
    | .succ x => y + x

run_meta Lean.Compiler.compile #[``test2]

set_option trace.Compiler.result true
run_meta Lean.Compiler.compile #[``test1]
run_meta Lean.Compiler.compile #[``test2]
