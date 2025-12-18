/-!
Various tests about `decreasing_by`.
-/

-- For concise recursive definition that need well-founded recursion
-- and `decreasing_by` tactics that would fail if run on the subgoal
opaque dec1 : Nat → Nat
axiom dec1_lt (n : Nat) : dec1 n < n
opaque dec2 : Nat → Nat
axiom dec2_lt (n : Nat) : dec2 n < n


def simple (n : Nat) := n + simple (dec1 n)
decreasing_by apply dec1_lt

namespace Ex1

-- Multiple goals, explicit termination_By
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100
termination_by (n, m)
decreasing_by
  · apply Prod.Lex.right
    apply dec2_lt
  · apply Prod.Lex.left
    apply dec1_lt

end Ex1

namespace Ex2

-- Multiple goals, no termination_By
-- This does *not* work, because GuessLex does not pass multiple goals to the tactic.
-- so this tactic script fails.
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100 -- Error
decreasing_by
  · apply Prod.Lex.right
    apply dec2_lt
  · apply Prod.Lex.left
    apply dec1_lt

end Ex2

namespace Ex3
-- Using `all_goals`, explicit termination_By
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100
termination_by (n, m)
decreasing_by all_goals
  first
    | apply Prod.Lex.right
      apply dec2_lt
    | apply Prod.Lex.left
      apply dec1_lt

end Ex3

namespace Ex4

-- Multiple goals, no termination_By
-- This does work, because the tactic is flexible enough
-- (Not a recommended way; complex `decreasing_by` should go along with `termination_by`.)
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100 -- Error
decreasing_by all_goals
  first
    | apply Prod.Lex.right
      apply dec2_lt
    | apply Prod.Lex.left
      apply dec1_lt

end Ex4

namespace Ex5
-- Empty proof. Produces parse error and unsolved goals.
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100
termination_by (n, m)
decreasing_by -- Error

end Ex5

namespace Ex6

-- Incomplete tactic
-- Unsolved goals reported
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100
termination_by (n, m)
decreasing_by apply id -- Error

end Ex6

namespace Ex7

-- Incomplete tactic, no termination_by
-- Shows guess-lex matrix
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100 -- Error
decreasing_by apply id

end Ex7

namespace Ex8

-- tactic solving just one goal
-- unsolved goals
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100
termination_by (n, m)
decreasing_by -- Error
  · apply Prod.Lex.right
    apply dec2_lt

end Ex8

namespace Ex9

-- Incomplete tactic, no termination_by
-- Shows guess-lex matrix
def foo (n m : Nat) : Nat := foo n (dec2 m) + foo (dec1 n) 100 -- Error
decreasing_by
  · apply Prod.Lex.right
    apply dec2_lt

end Ex9

namespace Ex10

-- This checks that guess-lex does not run tactics in “recover” mode.
-- (If it would it would produce the wrong termination order and then we should see errors)
def foo (n m : Nat) : Nat := foo (n - 1) (dec2 m)
decreasing_by all_goals
  · apply dec2_lt

end Ex10
