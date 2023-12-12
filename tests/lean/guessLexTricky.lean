/-!
A “tricky” example from “Finding Lexicographic Orders for Termination Proofs in
Isabelle/HOL” by Lukas Bulwahn, Alexander Krauss, and Tobias Nipkow,
10.1007/978-3-540-74591-4_5

At the time of writing, Lean is able to find the lexicographic order
just fine, but only if the tactic is powerful enough. In partiuclar,
the default `decreasing_tactic` can only handle lexicographic descend when either
the left gets smaller, or the left stays equal and the right gets smaller.
But here we need to allow the general form, where the left is ≤ and the right
gets smaller. This needs a backtracking proof search, it seems, which we build here
(`search_lex`).
-/

set_option showInferredTerminationBy true

macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.le_refl)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.succ_lt_succ; decreasing_trivial)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.sub_le)
macro_rules | `(tactic| decreasing_trivial) =>
              `(tactic| apply Nat.div_le_self)

syntax "search_lex " tacticSeq : tactic

macro_rules | `(tactic|search_lex $ts:tacticSeq) => `(tactic| (
    solve
    | apply Prod.Lex.right'
      · $ts
      · search_lex $ts
    | apply Prod.Lex.left
      · $ts
    | $ts
    ))

-- set_option trace.Elab.definition.wf true in
mutual
def prod (x y z : Nat) : Nat :=
  if y % 2 = 0 then eprod x y z else oprod x y z
def oprod (x y z : Nat) := eprod x (y - 1) (z + x)
def eprod (x y z : Nat) := if y = 0 then z else prod (2 * x) (y / 2) z
end
-- termination_by
--   prod x y z => (y, 2)
--   oprod x y z => (y, 1)
--   eprod x y z => (y, 0)
decreasing_by
  simp_wf
  search_lex solve
    | decreasing_trivial
    | apply Nat.bitwise_rec_lemma; assumption
