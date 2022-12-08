/- ANCHOR: doc -/
open Lean in
macro "begin " ts:tactic,*,? i:"end" : term => do
  -- preserve position of the last token, which is used
  -- as the error position in case of an unfinished proof
  `(by { $[$ts:tactic]* }%$i)

theorem ex1 (x : Nat) : x + 0 = 0 + x :=
  begin
    rw [Nat.zero_add],
    rw [Nat.add_zero],
  end
/- ANCHOR_END: doc -/

theorem ex2 (x : Nat) : x + 0 = 0 + x :=
  begin
    rw [Nat.zero_add]
  end  -- error should be shown here
