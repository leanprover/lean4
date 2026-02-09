inductive DNat : Nat → Type
  | zero : DNat 0
  | succ : DNat n → DNat (n+1)

def foo : DNat i → Nat
  | .zero => 0
  | .succ n => foo n
termination_by n => n


mutual
def bar1 : DNat i → Nat
  | .zero => 0
  | .succ n => bar2 n
termination_by n => n
def bar2 : DNat i → Nat
  | .zero => 0
  | .succ n => bar1 n
termination_by n => n
end


mutual
def baz1 : DNat i → Nat
  | .zero => 0
  | .succ n => baz2 n
termination_by n => sizeOf n
def baz2 : DNat i → Nat
  | .zero => 0
  | .succ n => baz1 n
termination_by n => n
end
