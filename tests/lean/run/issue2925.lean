def FunType := Nat → Nat
def Fun2Type := Nat → Nat → Nat

mutual
def foo : FunType
  | .zero => 0
  | .succ n => bar n
def bar : Nat → Nat
  | .zero => 0
  | .succ n => baz n 0
def baz : Fun2Type
  | .zero, m => 0
  | .succ n, m => foo n
end
termination_by foo n => n; bar n => n; baz n _ => n
