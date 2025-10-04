/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Tactics
public section
namespace Lean.Parser.Tactic.Grind

/-- `grind` is the syntax category for a "grind interactive tactic".
A `grind` tactic is a program which receives a `grind` goal. -/
declare_syntax_cat grind (behavior := both)

syntax grindSeq1Indented := sepBy1IndentSemicolon(grind)
syntax grindSeqBracketed := "{" withoutPosition(sepByIndentSemicolon(grind)) "}"
syntax grindSeq := grindSeqBracketed <|> grindSeq1Indented

/-- `skip` does nothing. -/
syntax (name := skip) "skip" : grind
/-- `lia` linear integer arithmetic. -/
syntax (name := lia) "lia" : grind
/-- `ring` (commutative) rings and fields. -/
syntax (name := ring) "ring" : grind
/-- `finish` tries to close the current goal using `grind`'s default strategy -/
syntax (name := finish) "finish" : grind

syntax (name := «have») "have" letDecl : grind

/-- Executes the given tactic block to close the current goal. -/
syntax (name := nestedTacticCore) "tactic" " => " tacticSeq : grind

end Lean.Parser.Tactic.Grind
