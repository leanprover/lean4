-- This example demonstrates how to specify a proof skeleton that contains
-- "holes" that must be filled using user-defined tactics.

(*
-- import useful macros for creating tactics
import("tactic.lua")

-- Define a simple tactic using Lua
auto = Repeat(OrElse(assumption_tac(), conj_tac(), conj_hyp_tac()))

conj_hyp = conj_hyp_tac()
conj     = conj_tac()
*)

-- The (by [tactic]) expression is essentially creating a "hole" and associating a "hint" to it.
-- The "hint" is a tactic that should be used to fill the "hole".
-- In the following example, we use the tactic "auto" defined by the Lua code above.
--
-- The (have [expr] by [tactic]) expression is also creating a "hole" and associating a "hint" to it.
-- The expression [expr] after the shows is fixing the type of the "hole"
theorem T1 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := (by auto),
              lemma2     : B      := (by auto)
          in (have B /\ A by auto)

print environment 1. -- print proof for the previous theorem

-- When hints are not provided, the user must fill the (remaining) holes using tactic command sequences.
-- Each hole must be filled with a tactic command sequence that terminates with the command 'done' and
-- successfully produces a proof term for filling the hole. Here is the same example without hints
-- This style is more convenient for interactive proofs
theorem T2 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,  -- first hole
              lemma2     : B      := _   -- second hole
          in _. -- third hole
   auto. done. -- tactic command sequence for the first hole
   auto. done. -- tactic command sequence for the second hole
   auto. done. -- tactic command sequence for the third hole

-- In the following example, instead of using the "auto" tactic, we apply a sequence of even simpler tactics.
theorem T3 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,  -- first hole
              lemma2     : B      := _   -- second hole
          in _. -- third hole
   conj_hyp. exact. done.  -- tactic command sequence for the first hole
   conj_hyp. exact. done.  -- tactic command sequence for the second hole
   conj. exact. done.  -- tactic command sequence for the third hole

-- We can also mix the two styles (hints and command sequences)
theorem T4 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,  -- first hole
              lemma2     : B      := _   -- second hole
          in (have B /\ A by auto).
   auto. done.  -- tactic command sequence for the first hole
   auto. done.  -- tactic command sequence for the second hole
