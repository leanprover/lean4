import Lean

def one := 1
def zero := 0

def f (x : Nat) (b : Bool) :=
  let k := fun b =>
    let y := match b with
      | true => one
      | false => zero
    Nat.succ y
  x == k b

set_option trace.Compiler.simp true
#eval Lean.Compiler.compile #[``f]
