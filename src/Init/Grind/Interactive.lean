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

syntax anchor := "#" noWs hexnum

syntax grindLemma    := ppGroup((Attr.grindMod ppSpace)? term)
/--
The `!` modifier instructs `grind` to consider only minimal indexable subexpressions
when selecting patterns.
-/
syntax grindLemmaMin := ppGroup("!" (Attr.grindMod ppSpace)? term)

syntax grindErase    := "-" ident
/--
The `!` modifier instructs `grind` to consider only minimal indexable subexpressions
when selecting patterns.
-/
syntax grindParam    := grindErase <|> grindLemmaMin <|> grindLemma <|> anchor

namespace Grind
declare_syntax_cat grind_filter (behavior := both)

syntax:max ident : grind_filter
syntax:max &"gen" " < "  num  : grind_filter
syntax:max &"gen" " = "  num  : grind_filter
syntax:max &"gen" " != " num  : grind_filter
syntax:max &"gen" " ≤ "  num  : grind_filter
syntax:max &"gen" " <= " num  : grind_filter
syntax:max &"gen" " > "  num  : grind_filter
syntax:max &"gen" " ≥ "  num  : grind_filter
syntax:max &"gen" " >= " num  : grind_filter
syntax:max "(" grind_filter ")" : grind_filter
syntax:35 grind_filter:35 " && " grind_filter:36 : grind_filter
syntax:35 grind_filter:35 " || " grind_filter:36 : grind_filter
syntax:max "!" grind_filter:40 : grind_filter

syntax grindFilter := (colGt grind_filter)?

/-- `grind` is the syntax category for a "grind interactive tactic".
A `grind` tactic is a program which receives a `grind` goal. -/
declare_syntax_cat grind (behavior := both)

syntax grindStep := grind ("|" (colGt ppSpace grind_filter)?)?

syntax grindSeq1Indented := sepBy1IndentSemicolon(grindStep)
syntax grindSeqBracketed := "{" withoutPosition(sepByIndentSemicolon(grindStep)) "}"
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

syntax thmNs := &"namespace" ident

syntax thm := anchor <|> thmNs <|> grindLemmaMin <|> grindLemma

/--
Instantiates theorems using E-matching.
The `approx` modifier is just a marker for users to easily identify automatically generated `instantiate` tactics
that may have redundant arguments.
-/
syntax (name := instantiate) "instantiate" (&" only")? (&" approx")? (" [" withoutPosition(thm,*,?) "]")? : grind

/-- Shorthand for `instantiate only` -/
syntax (name := use) "use" " [" withoutPosition(thm,*,?) "]" : grind
macro_rules | `(grind| use%$u [$ts:thm,*]) => `(grind| instantiate%$u only [$ts,*])

-- **Note**: Should we rename the following tactics to `trace_`?
/-- Shows asserted facts. -/
syntax (name := showAsserted) "show_asserted" ppSpace grindFilter : grind
/-- Shows propositions known to be `True`. -/
syntax (name := showTrue) "show_true" ppSpace grindFilter : grind
/-- Shows propositions known to be `False`. -/
syntax (name := showFalse) "show_false" ppSpace grindFilter : grind
/-- Shows equivalence classes of terms. -/
syntax (name := showEqcs) "show_eqcs" ppSpace grindFilter : grind
/-- Show case-split candidates. -/
syntax (name := showCases) "show_cases" ppSpace grindFilter : grind
/-- Show `grind` state. -/
syntax (name := «showState») "show_state" ppSpace grindFilter : grind
/-- Show active local theorems and their anchors for heuristic instantiation. -/
syntax (name := showLocalThms) "show_local_thms" : grind
/--
`show_term tac` runs `tac`, then displays the generated proof in the InfoView.
-/
syntax (name := showTerm) "show_term " grindSeq : grind

declare_syntax_cat grind_ref (behavior := both)

syntax:max anchor : grind_ref
syntax term : grind_ref

/--
Performs a case-split on a logical connective, `match`-expression, `if-then-else`-expression,
or inductive predicate. The argument is an anchor referencing one of the case-split candidates
in the `grind` state. You can use `cases?` to select a specific candidate using a code action.
-/
syntax (name := cases) "cases " grind_ref : grind

/--
A variant of `cases` that provides a code-action for selecting one of the candidate case-splits
available in the `grind` state.
-/
syntax (name := casesTrace) "cases?" grindFilter : grind

/--
Performs the next case-split. The case-split is selected using the same heuristic used by `finish`.
-/
syntax (name := casesNext) "cases_next" : grind

/-- `done` succeeds iff there are no remaining goals. -/
syntax (name := done) "done" : grind

/-- `finish` tries to close the current goal using `grind`'s default strategy -/
syntax (name := finish) "finish" (ppSpace configItem)*
    (ppSpace &"only")? (" [" withoutPosition(grindParam,*) "]")? : grind

/-- `finish?` tries to close the current goal using `grind`'s default strategy and suggests a tactic script. -/
syntax (name := finishTrace) "finish?" (ppSpace configItem)*
    (ppSpace &"only")? (" [" withoutPosition(grindParam,*) "]")? : grind

/--
The `have` tactic is for adding opaque definitions and hypotheses to the local context of the main goal.
The definitions forget their associated value and cannot be unfolded.

* `have h : t := e` adds the hypothesis `h : t` if `e` is a term of type `t`.
* `have h := e` uses the type of `e` for `t`.
* `have : t := e` and `have := e` use `this` for the name of the hypothesis.
-/
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

/--
`next => tac` focuses on the next goal and solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with
inaccessible names to the given names.
-/
syntax (name := next) "next " binderIdent* " => " grindSeq : grind

/--
`· grindSeq` focuses on the main `grind` goal and tries to solve it using the given
sequence of `grind` tactics.
-/
macro dot:patternIgnore("· " <|> ". ") s:grindSeq : grind => `(grind| next%$dot =>%$dot $s:grindSeq )

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
syntax (name := first) "first " withPosition((ppDedent(ppLine) colGe "(" grindSeq ")")+) : grind

/-- `try tac` runs `tac` and succeeds even if `tac` failed. -/
macro "try " t:grindSeq : grind => `(grind| first ($t:grindSeq) (skip))

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
  | `(grind| repeat $seq:grindSeq) => `(grind| first (($seq); repeat $seq:grindSeq) (skip))

/-- `rename_i x_1 ... x_n` renames the last `n` inaccessible names using the given names. -/
syntax (name := renameI) "rename_i" (ppSpace colGt binderIdent)+ : grind

/--
`expose_names` renames all inaccessible variables with accessible names, making them available
for reference in generated tactics. However, this renaming introduces machine-generated names
that are not fully under user control. `expose_names` is primarily intended as a preamble for
generated `grind` tactic scripts.
-/
syntax (name := exposeNames) "expose_names" : grind

/--
`set_option opt val in tacs` (the tactic) acts like `set_option opt val` at the command level,
but it sets the option only within the tactics `tacs`. -/
syntax (name := setOption) "set_option " (ident (noWs "." noWs ident)?) ppSpace optionValue " in " grindSeq : grind

/--
`set_config configItem+ in tacs` executes `tacs` with the updated configuration options `configItem+`
-/
syntax (name := setConfig) "set_config " configItem+ " in " grindSeq : grind

/--
Proves `<term>` using the current `grind` state and default search strategy.
-/
syntax (name := haveSilent) "have" (ppSpace ident)? ppSpace ": " term : grind

/--
Adds new case-splits using model-based theory combination.
-/
syntax (name := mbtc) "mbtc" : grind

end Grind
end Lean.Parser.Tactic
