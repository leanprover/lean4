


/-!
Tests that docstring hovers are computed correctly for tactic extensions
-/

/-- Another `trivial` tactic -/
syntax (name := my_trivial) "my_trivial" : tactic

@[tactic_alt my_trivial]
syntax (name := very_trivial) "very_trivial" : tactic
macro_rules
| `(tactic|very_trivial) => `(tactic|my_trivial)

/-- It tries Lean's `trivial` -/
tactic_extension my_trivial
               --^ textDocument/hover
macro_rules
  | `(tactic|my_trivial) => `(tactic|trivial)
             --^ textDocument/hover

/-- It tries `simp_all` -/
tactic_extension my_trivial
macro_rules
  | `(tactic|my_trivial) => `(tactic|simp_all; done)


example : True := by
  my_trivial
      --^ textDocument/hover

/-- It tries `constructor` -/
tactic_extension my_trivial
               --^ textDocument/hover
-- On the preceding line, it was not yet extended.
-- Here, it is:
macro_rules
  | `(tactic|my_trivial) => `(tactic|constructor; done)
           --^ textDocument/hover

/--
It tries some useful things:
 * `omega`
 * `simp_arith [*]`
-/
tactic_extension my_trivial
macro_rules
  | `(tactic|my_trivial) => `(tactic|omega)
macro_rules
  | `(tactic|my_trivial) => `(tactic|simp_arith [*]; done)

-- This tests that nested lists work
example : True := by
  my_trivial
      --^ textDocument/hover

-- This tests that alts are resolved
example : True := by
  very_trivial
      --^ textDocument/hover
