inductive S
| mk : (_foo : Nat → Int) → S

namespace S

def bar (s : S) : Nat := 0

variable (s : S)
#check s.bar

end S
