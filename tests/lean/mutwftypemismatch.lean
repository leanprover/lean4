namespace Ex1
mutual
def foo : Nat → Nat
 | 0   => 1
 | n+1 => bar n
termination_by n => n

def bar : Nat → Nat
 | 0   => 1
 | n+1 => foo n
termination_by n => n > 2
end
end Ex1

namespace Ex2
-- With dependency on fixed parameter
mutual
def foo (fixed : Nat) : Nat → Nat
 | 0   => 1
 | n+1 => bar fixed n
termination_by n => n

def bar (fixed : Nat) : Nat → Nat
 | 0   => 1
 | n+1 => foo fixed n
termination_by n => (⟨n, sorry⟩ : Fin fixed)
end
end Ex2
