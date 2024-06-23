
def foo (n : Nat) : True := match n with
  | 0 => .intro
  | n+1 => foo n
termination_by structurally n

-- Check that we can still refer to a variable called `structurally` in
-- the `termination_by` syntax
def foo (structurally : Nat) : True := match structurally with
  | 0 => .intro
  | structurally+1 => foo structurally
termination_by «structurally»
