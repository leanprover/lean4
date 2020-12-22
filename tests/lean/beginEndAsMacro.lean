/- ANCHOR: doc -/
open Lean in
macro "begin " ts:tactic,*,? "end"%i : term => do
  -- preserve position of the last token, which is used
  -- as the error position in case of an unfinished proof
  `(by { $[$ts:tactic]* }%$i)

theorem ex1 (x : Nat) : x + 0 = 0 + x :=
  begin
    rw Nat.zeroAdd,
    rw Nat.addZero,
  end
/- ANCHOR_END: doc -/

theorem ex2 (x : Nat) : x + 0 = 0 + x :=
  begin
    rw Nat.zeroAdd
  end  -- error should be shown here
