def foo : Nat → Nat → Nat
  | 0,   0   => 1
  | s+1, 0   => foo s 0 + 1
  | 0,   b+1 => foo 0 b + 1
  | s+1, b+1 => foo (s+1) b + foo s (b+1)
termination_by b s => (b, s)
