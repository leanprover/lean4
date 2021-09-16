import Lean



open Lean.Elab.Term
open Lean.Elab.Command

elab "∃'" b:term "," P:term : term => do
 let ex ← `(Exists (fun $b => $P));
 elabTerm ex none

elab "#check2" b:term : command => do
  let cmd ← `(#check $b #check $b);
  elabCommand cmd

#check ∃' x, x > 0

#check ∃' (x : UInt32), x > 0

#check2 10

elab "try" t:tactic : tactic => do
  let t' ← `(tactic| first | $t | skip);
  Lean.Elab.Tactic.evalTactic t'

theorem tst (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intro h1; intro h2; intro h3;
  apply @Eq.trans;
  try exact h1; -- `exact h1` fails
  trace_state;
  try exact h3;
  trace_state;
  try exact h1;
}
