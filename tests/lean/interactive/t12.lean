(**
-- Define a simple tactic using Lua
auto = REPEAT(ORELSE(assumption_tac, conj_tac, conj_hyp_tac))
**)

(*
The (by [tactic]) expression is essentially creating a "hole" and associating a "hint" to it.
The "hint" is a tactic that should be used to fill the "hole".
In the following example, we use the tactic "auto" defined by the Lua code above.

The (show [expr] by [tactic]) expression is also creating a "hole" and associating a "hint" to it.
The expression [expr] after the shows is fixing the type of the "hole"
*)
Theorem T1 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := (by auto),
              lemma2     : B      := (by auto)
          in (show B /\ A by auto)

Show Environment 1. (* Show proof for the previous theorem *)

(*
When hints are not provided, the user must fill the (remaining) holes using tactic command sequences.
Each hole must be filled with a tactic command sequence that terminates with the command 'done' and
successfully produces a proof term for filling the hole. Here is the same example without hints
This style is more convenient for interactive proofs
*)
Theorem T2 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,  (* first hole *)
              lemma2     : B      := _   (* second hole *)
          in _. (* third hole *)
   apply auto. done. (* tactic command sequence for the first hole *)
   apply auto. done. (* tactic command sequence for the second hole *)
   apply auto. done. (* tactic command sequence for the third hole *)

(*
In the following example, instead of using the "auto" tactic, we apply a sequence of even simpler tactics.
*)
Theorem T3 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,  (* first hole *)
              lemma2     : B      := _   (* second hole *)
          in _. (* third hole *)
   apply conj_hyp_tac. apply assumption_tac. done.  (* tactic command sequence for the first hole *)
   apply conj_hyp_tac. apply assumption_tac. done.  (* tactic command sequence for the second hole *)
   apply conj_tac. apply assumption_tac. done.      (* tactic command sequence for the third hole *)

(*
We can also mix the two styles (hints and command sequences)
*)
Theorem T4 (A B : Bool) : A /\ B -> B /\ A :=
     fun assumption : A /\ B,
          let lemma1     : A      := _,  (* first hole *)
              lemma2     : B      := _   (* second hole *)
          in (show B /\ A by auto).
   apply conj_hyp_tac. apply assumption_tac. done.  (* tactic command sequence for the first hole *)
   apply conj_hyp_tac. apply assumption_tac. done.  (* tactic command sequence for the second hole *)


