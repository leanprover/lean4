syntax[beginEndKind] "begin " sepByT(tactic, ", ") "end" : term

open Lean in
@[macro beginEndKind] def expandBeginEnd : Lean.Macro := fun stx =>
  match_syntax stx with
  | `(begin $ts* end) => do
     let ts   := ts.getSepElems.map fun t => mkNullNode #[t, mkNullNode]
     let tseq := mkNode `Lean.Parser.Tactic.tacticSeqBracketed #[mkAtomFrom stx "{", mkNullNode ts, mkAtomFrom stx[2] "}"]
     `(by $tseq:tacticSeqBracketed)
  | _ => Macro.throwUnsupported

theorem ex1 (x : Nat) : x + 0 = 0 + x :=
  begin
    rw Nat.zeroAdd,
    rw Nat.addZero,
  end
