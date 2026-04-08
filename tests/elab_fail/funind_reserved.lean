
-- Test that the reserved name availability is checked at function definition time

namespace Nonrec

def foo.induct := 1

def foo : (n : Nat) → Nat -- no error (yet)
  | 0 => 0
  | n+1 => n

end Nonrec

namespace Structural

def foo.induct := 1

def foo : (n : Nat) → Nat -- error
  | 0 => 0
  | n+1 => foo n

end Structural

namespace WF

def foo.induct := 1

def foo : (n : Nat) → Nat -- error
  | 0 => 0
  | n+1 => foo n
termination_by n => n

end WF

namespace Mutual1

def foo.induct := 1

mutual
def foo : (n : Nat) → Nat -- error
  | 0 => 0
  | n+1 => bar n
termination_by n => n

def bar : (n : Nat) → Nat -- error
  | 0 => 0
  | n+1 => foo n
termination_by n => n
end

end Mutual1

namespace Mutual2

def bar.induct := 1

mutual
def foo : (n : Nat) → Nat -- error
  | 0 => 0
  | n+1 => bar n
termination_by n => n

def bar : (n : Nat) → Nat
  | 0 => 0
  | n+1 => foo n
termination_by n => n
end

end Mutual2

namespace Mutual3

def foo.mutual_induct := 1

mutual
def foo : (n : Nat) → Nat -- error
  | 0 => 0
  | n+1 => bar n
termination_by n => n

def bar : (n : Nat) → Nat
  | 0 => 0
  | n+1 => foo n
termination_by n => n
end

end Mutual3

namespace Nested

def foo : (n : Nat) → Nat -- error
  | 0 => 0
  | n+1 => foo n
  where induct := 1

end Nested
