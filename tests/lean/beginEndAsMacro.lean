/- ANCHOR: doc -/
open Lean in
macro "begin " ts:tactic,*,? "end" : term => do
  let stx  ← getRef
  let ts   := ts.getElems.map (mkNullNode #[·, mkNullNode])
  let tseq := mkNode `Lean.Parser.Tactic.tacticSeqBracketed #[
     mkAtomFrom stx "{", mkNullNode ts, mkAtomFrom stx[2] "}"
  ]
  `(by $tseq:tacticSeqBracketed)

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
