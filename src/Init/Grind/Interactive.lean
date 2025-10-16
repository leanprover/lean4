/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Attr
public section
namespace Lean.Parser.Tactic

syntax grindLemma    := ppGroup((Attr.grindMod ppSpace)? ident)
/--
The `!` modifier instructs `grind` to consider only minimal indexable subexpressions
when selecting patterns.
-/
syntax grindLemmaMin := ppGroup("!" (Attr.grindMod ppSpace)? ident)

namespace Grind

/-- `grind` is the syntax category for a "grind interactive tactic".
A `grind` tactic is a program which receives a `grind` goal. -/
declare_syntax_cat grind (behavior := both)

syntax grindSeq1Indented := sepBy1IndentSemicolon(grind)
syntax grindSeqBracketed := "{" withoutPosition(sepByIndentSemicolon(grind)) "}"
syntax grindSeq := grindSeqBracketed <|> grindSeq1Indented

/-- `(grindSeq)` runs the `grindSeq` in sequence on the current list of targets.
This is pure grouping with no added effects. -/
syntax (name := paren) "(" withoutPosition(grindSeq) ")" : grind

/-- `skip` does nothing. -/
syntax (name := skip) "skip" : grind
/-- `lia` linear integer arithmetic. -/
syntax (name := lia) "lia" : grind
/-- `ring` (commutative) rings and fields. -/
syntax (name := ring) "ring" : grind
/-- `ac` associativity and commutativity procedure. -/
syntax (name := ac) "ac" : grind
/-- `linarith` linear arithmetic. -/
syntax (name := linarith) "linarith" : grind

/-- The `sorry` tactic is a temporary placeholder for an incomplete tactic proof. -/
syntax (name := «sorry») "sorry" : grind

syntax anchor := "#" noWs hexnum
syntax thm := anchor <|> grindLemma <|> grindLemmaMin

/-- Instantiates theorems using E-matching. -/
syntax (name := instantiate) "instantiate" (colGt thm),* : grind

declare_syntax_cat show_filter (behavior := both)

syntax:max ident : show_filter
syntax:max &"gen" " < "  num  : show_filter
syntax:max &"gen" " = "  num  : show_filter
syntax:max &"gen" " != " num  : show_filter
syntax:max &"gen" " ≤ "  num  : show_filter
syntax:max &"gen" " <= " num  : show_filter
syntax:max &"gen" " > "  num  : show_filter
syntax:max &"gen" " ≥ "  num  : show_filter
syntax:max &"gen" " >= " num  : show_filter
syntax:max "(" show_filter ")" : show_filter
syntax:35 show_filter:35 " && " show_filter:36 : show_filter
syntax:35 show_filter:35 " || " show_filter:36 : show_filter
syntax:max "!" show_filter:40 : show_filter

syntax showFilter := (colGt show_filter)?

-- **Note**: Should we rename the following tactics to `trace_`?
/-- Shows asserted facts. -/
syntax (name := showAsserted) "show_asserted" ppSpace showFilter : grind
/-- Shows propositions known to be `True`. -/
syntax (name := showTrue) "show_true" ppSpace showFilter : grind
/-- Shows propositions known to be `False`. -/
syntax (name := showFalse) "show_false" ppSpace showFilter : grind
/-- Shows equivalence classes of terms. -/
syntax (name := showEqcs) "show_eqcs" ppSpace showFilter : grind
/-- Show case-split candidates. -/
syntax (name := showSplits) "show_splits" ppSpace showFilter : grind
/-- Show `grind` state. -/
syntax (name := «showState») "show_state" ppSpace showFilter : grind
/-- Show active local theorems and their anchors for heuristic instantiation. -/
syntax (name := showThms) "show_thms" : grind

declare_syntax_cat grind_ref (behavior := both)

syntax:max anchor : grind_ref
syntax term : grind_ref

syntax (name := cases) "cases " grind_ref (" with " (colGt ident)+)? : grind

/-- `done` succeeds iff there are no remaining goals. -/
syntax (name := done) "done" : grind

/-- `finish` tries to close the current goal using `grind`'s default strategy -/
syntax (name := finish) "finish" : grind

syntax (name := «have») "have" letDecl : grind

/-- Executes the given tactic block to close the current goal. -/
syntax (name := nestedTacticCore) "tactic" " => " tacticSeq : grind

/--
`all_goals tac` runs `tac` on each goal, concatenating the resulting goals.
If the tactic fails on any goal, the entire `all_goals` tactic fails.
-/
syntax (name := allGoals) "all_goals " grindSeq : grind

/--
`focus tac` focuses on the main goal, suppressing all other goals, and runs `tac` on it.
Usually `· tac`, which enforces that the goal is closed by `tac`, should be preferred.
-/
syntax (name := focus) "focus " grindSeq : grind

syntax (name := next) "next " binderIdent* " => " grindSeq : grind

/--
`any_goals tac` applies the tactic `tac` to every goal,
concatenating the resulting goals for successful tactic applications.
If the tactic fails on all of the goals, the entire `any_goals` tactic fails.

This tactic is like `all_goals try tac` except that it fails if none of the applications of `tac` succeeds.
-/
syntax (name := anyGoals) "any_goals " grindSeq : grind

/--
`with_annotate_state stx t` annotates the lexical range of `stx : Syntax` with
the initial and final state of running tactic `t`.
-/
scoped syntax (name := withAnnotateState)
  "with_annotate_state " rawStx ppSpace grind : grind

/--
`tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal,
concatenating all goals produced by `tac'`.
-/
macro:1 x:grind tk:" <;> " y:grind:2 : grind => `(grind|
  focus
    $x:grind
    with_annotate_state $tk skip
    all_goals $y:grind)

/-- `first | tac | ...` runs each `tac` until one succeeds, or else fails. -/
syntax (name := first) "first " withPosition((ppDedent(ppLine) colGe "| " grindSeq)+) : grind

/-- `try tac` runs `tac` and succeeds even if `tac` failed. -/
macro "try " t:grindSeq : grind => `(grind| first | $t | skip)

/-- `fail_if_success t` fails if the tactic `t` succeeds. -/
syntax (name := failIfSuccess) "fail_if_success " grindSeq : grind

/-- `admit` is a synonym for `sorry`. -/
macro "admit" : grind => `(grind| sorry)

/-- `fail msg` is a tactic that always fails, and produces an error using the given message. -/
syntax (name := fail) "fail" (ppSpace str)? : grind

/--
`repeat tac` repeatedly applies `tac` so long as it succeeds.
The tactic `tac` may be a tactic sequence, and if `tac` fails at any point in its execution,
`repeat` will revert any partial changes that `tac` made to the tactic state.
The tactic `tac` should eventually fail, otherwise `repeat tac` will run indefinitely.
-/
syntax "repeat " grindSeq : grind

macro_rules
  | `(grind| repeat $seq) => `(grind| first | ($seq); repeat $seq | skip)

/-- `rename_i x_1 ... x_n` renames the last `n` inaccessible names using the given names. -/
syntax (name := renameI) "rename_i" (ppSpace colGt binderIdent)+ : grind

/--
`expose_names` renames all inaccessible variables with accessible names, making them available
for reference in generated tactics. However, this renaming introduces machine-generated names
that are not fully under user control. `expose_names` is primarily intended as a preamble for
generated `grind` tactic scripts.
-/
syntax (name := exposeNames) "expose_names" : grind

end Grind
end Lean.Parser.Tactic
