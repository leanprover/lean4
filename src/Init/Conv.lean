/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Tactics
import Init.Meta

namespace Lean.Parser.Tactic.Conv

/-- `conv` is the syntax category for a "conv tactic", where "conv" is short
for conversion. A conv tactic is a program which receives a target, printed as
`| a`, and is tasked with coming up with some term `b` and a proof of `a = b`.
It is mainly used for doing targeted term transformations, for example rewriting
only on the left side of an equality. -/
declare_syntax_cat conv (behavior := both)

syntax convSeq1Indented := sepBy1IndentSemicolon(conv)
syntax convSeqBracketed := "{" withoutPosition(sepByIndentSemicolon(conv)) "}"
-- Order is important: a missing `conv` proof should not be parsed as `{ <missing> }`,
-- automatically closing goals
syntax convSeq := convSeqBracketed <|> convSeq1Indented

/-- The `*` occurrence list means to apply to all occurrences of the pattern. -/
syntax occsWildcard := "*"

/--
A list `1 2 4` of occurrences means to apply to the first, second, and fourth
occurrence of the pattern.
-/
syntax occsIndexed := num+

/-- An occurrence specification, either `*` or a list of numbers. The default is `[1]`. -/
syntax occs := atomic("(" &"occs") " := " (occsWildcard <|> occsIndexed) ") "

/--
`with_annotate_state stx t` annotates the lexical range of `stx : Syntax` with
the initial and final state of running tactic `t`.
-/
scoped syntax (name := withAnnotateState)
  "with_annotate_state " rawStx ppSpace conv : conv


/-- `skip` does nothing. -/
syntax (name := skip) "skip" : conv

/--
Traverses into the left subterm of a binary operator.

In general, for an `n`-ary operator, it traverses into the second to last argument.
It is a synonym for `arg -2`.
-/
syntax (name := lhs) "lhs" : conv

/--
Traverses into the right subterm of a binary operator.

In general, for an `n`-ary operator, it traverses into the last argument.
It is a synonym for `arg -1`.
-/
syntax (name := rhs) "rhs" : conv

/-- Traverses into the function of a (unary) function application.
For example, `| f a b` turns into `| f a`. (Use `arg 0` to traverse into `f`.)  -/
syntax (name := «fun») "fun" : conv

/-- Reduces the target to Weak Head Normal Form. This reduces definitions
in "head position" until a constructor is exposed. For example, `List.map f [a, b, c]`
weak head normalizes to `f a :: List.map f [b, c]`. -/
syntax (name := whnf) "whnf" : conv

/-- Expands let-declarations and let-variables. -/
syntax (name := zeta) "zeta" : conv

/-- Puts term in normal form, this tactic is meant for debugging purposes only. -/
syntax (name := reduce) "reduce" : conv

/-- Performs one step of "congruence", which takes a term and produces
subgoals for all the function arguments. For example, if the target is `f x y` then
`congr` produces two subgoals, one for `x` and one for `y`. -/
syntax (name := congr) "congr" : conv

syntax argArg := "@"? "-"? num

/--
* `arg i` traverses into the `i`'th argument of the target. For example if the
  target is `f a b c d` then `arg 1` traverses to `a` and `arg 3` traverses to `c`.
  The index may be negative; `arg -1` traverses into the last argument,
  `arg -2` into the second-to-last argument, and so on.
* `arg @i` is the same as `arg i` but it counts all arguments instead of just the
  explicit arguments.
* `arg 0` traverses into the function. If the target is `f a b c d`, `arg 0` traverses into `f`. -/
syntax (name := arg) "arg " argArg : conv

/-- `ext x` traverses into a binder (a `fun x => e` or `∀ x, e` expression)
to target `e`, introducing name `x` in the process. -/
syntax (name := ext) "ext" (ppSpace colGt binderIdent)* : conv

/-- `change t'` replaces the target `t` with `t'`,
assuming `t` and `t'` are definitionally equal. -/
syntax (name := change) "change " term : conv

/-- `delta id1 id2 ...` unfolds all occurrences of `id1`, `id2`, ... in the target.
Like the `delta` tactic, this ignores any definitional equations and uses
primitive delta-reduction instead, which may result in leaking implementation details.
Users should prefer `unfold` for unfolding definitions. -/
syntax (name := delta) "delta" (ppSpace colGt ident)+ : conv

/--
* `unfold id` unfolds all occurrences of definition `id` in the target.
* `unfold id1 id2 ...` is equivalent to `unfold id1; unfold id2; ...`.

Definitions can be either global or local definitions.

For non-recursive global definitions, this tactic is identical to `delta`.
For recursive global definitions, it uses the "unfolding lemma" `id.eq_def`,
which is generated for each recursive definition, to unfold according to the recursive definition given by the user.
Only one level of unfolding is performed, in contrast to `simp only [id]`, which unfolds definition `id` recursively.

This is the `conv` version of the `unfold` tactic.
-/
syntax (name := unfold) "unfold" (ppSpace colGt ident)+ : conv

/--
* `pattern pat` traverses to the first subterm of the target that matches `pat`.
* `pattern (occs := *) pat` traverses to every subterm of the target that matches `pat`
  which is not contained in another match of `pat`. It generates one subgoal for each matching
  subterm.
* `pattern (occs := 1 2 4) pat` matches occurrences `1, 2, 4` of `pat` and produces three subgoals.
  Occurrences are numbered left to right from the outside in.

Note that skipping an occurrence of `pat` will traverse inside that subexpression, which means
it may find more matches and this can affect the numbering of subsequent pattern matches.
For example, if we are searching for `f _` in `f (f a) = f b`:
* `occs := 1 2` (and `occs := *`) returns `| f (f a)` and `| f b`
* `occs := 2` returns `| f a`
* `occs := 2 3` returns `| f a` and `| f b`
* `occs := 1 3` is an error, because after skipping `f b` there is no third match.
-/
syntax (name := pattern) "pattern " (occs)? term : conv

/-- `rw [thm]` rewrites the target using `thm`. See the `rw` tactic for more information. -/
syntax (name := rewrite) "rewrite" optConfig rwRuleSeq : conv

/-- `simp [thm]` performs simplification using `thm` and marked `@[simp]` lemmas.
See the `simp` tactic for more information. -/
syntax (name := simp) "simp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? : conv

/-- `simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. See the `simp?` tactic for more information. -/
syntax (name := simpTrace) "simp?" optConfig (discharger)? (&" only")? (simpArgs)? : conv

/--
`dsimp` is the definitional simplifier in `conv`-mode. It differs from `simp` in that it only
applies theorems that hold by reflexivity.

Examples:

```lean
example (a : Nat): (0 + 0) = a - a := by
  conv =>
    lhs
    dsimp
    rw [← Nat.sub_self a]
```
-/
syntax (name := dsimp) "dsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*) "]")? : conv

@[inherit_doc simpTrace]
syntax (name := dsimpTrace) "dsimp?" optConfig (&" only")? (dsimpArgs)? : conv

/-- `simp_match` simplifies match expressions. For example,
```
match [a, b] with
| [] => 0
| hd :: tl => hd
```
simplifies to `a`. -/
syntax (name := simpMatch) "simp_match" : conv

/-- Executes the given tactic block without converting `conv` goal into a regular goal. -/
syntax (name := nestedTacticCore) "tactic'" " => " tacticSeq : conv

/-- Focuses, converts the `conv` goal `⊢ lhs` into a regular goal `⊢ lhs = rhs`, and then executes the given tactic block. -/
syntax (name := nestedTactic) "tactic" " => " tacticSeq : conv

/-- Executes the given conv block without converting regular goal into a `conv` goal. -/
syntax (name := convTactic) "conv'" " => " convSeq : tactic

/-- `{ convs }` runs the list of `convs` on the current target, and any subgoals that
remain are trivially closed by `skip`. -/
syntax (name := nestedConv) convSeqBracketed : conv

/-- `(convs)` runs the `convs` in sequence on the current list of targets.
This is pure grouping with no added effects. -/
syntax (name := paren) "(" withoutPosition(convSeq) ")" : conv

/-- `rfl` closes one conv goal "trivially", by using reflexivity
(that is, no rewriting). -/
macro "rfl" : conv => `(conv| tactic => rfl)

/-- `done` succeeds iff there are no goals remaining. -/
macro "done" : conv => `(conv| tactic' => done)

/-- `trace_state` prints the current goal state. -/
macro "trace_state" : conv => `(conv| tactic' => trace_state)

/-- `all_goals tac` runs `tac` on each goal, concatenating the resulting goals, if any. -/
macro (name := allGoals) tk:"all_goals " s:convSeq : conv =>
  `(conv| tactic' => all_goals%$tk conv' => $s)

/--
`any_goals tac` applies the tactic `tac` to every goal, and succeeds if at
least one application succeeds.
-/
macro (name := anyGoals) tk:"any_goals " s:convSeq : conv =>
  `(conv| tactic' => any_goals%$tk conv' => $s)

/--
* `case tag => tac` focuses on the goal with case name `tag` and solves it using `tac`,
  or else fails.
* `case tag x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses
  with inaccessible names to the given names.
* `case tag₁ | tag₂ => tac` is equivalent to `(case tag₁ => tac); (case tag₂ => tac)`.
-/
macro (name := case) tk:"case " args:sepBy1(caseArg, "|") arr:" => " s:convSeq : conv =>
  `(conv| tactic' => case%$tk $args|* =>%$arr conv' => ($s); all_goals rfl)

/--
`case'` is similar to the `case tag => tac` tactic, but does not ensure the goal
has been solved after applying `tac`, nor admits the goal if `tac` failed.
Recall that `case` closes the goal using `sorry` when `tac` fails, and
the tactic execution is not interrupted.
-/
macro (name := case') tk:"case' " args:sepBy1(caseArg, "|") arr:" => " s:convSeq : conv =>
  `(conv| tactic' => case'%$tk $args|* =>%$arr conv' => $s)

/--
`next => tac` focuses on the next goal and solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with
inaccessible names to the given names.
-/
macro "next" args:(ppSpace binderIdent)* " => " tac:convSeq : conv => `(conv| case _ $args* => $tac)

/--
`focus tac` focuses on the main goal, suppressing all other goals, and runs `tac` on it.
Usually `· tac`, which enforces that the goal is closed by `tac`, should be preferred.
-/
macro (name := focus) tk:"focus " s:convSeq : conv => `(conv| tactic' => focus%$tk conv' => $s)

/-- `conv => cs` runs `cs` in sequence on the target `t`,
resulting in `t'`, which becomes the new target subgoal. -/
syntax (name := convConvSeq) "conv" " => " convSeq : conv

/-- `· conv` focuses on the main conv goal and tries to solve it using `s`. -/
macro dot:patternIgnore("·" <|> ".") s:convSeq : conv => `(conv| {%$dot ($s) })


/-- `fail_if_success t` fails if the tactic `t` succeeds. -/
macro (name := failIfSuccess) tk:"fail_if_success " s:convSeq : conv =>
  `(conv| tactic' => fail_if_success%$tk conv' => $s)

/-- `rw [rules]` applies the given list of rewrite rules to the target.
See the `rw` tactic for more information. -/
macro "rw" c:optConfig s:rwRuleSeq : conv => `(conv| rewrite $c:optConfig $s)

/-- `erw [rules]` is a shorthand for `rw (transparency := .default) [rules]`.
This does rewriting up to unfolding of regular definitions (by comparison to regular `rw`
which only unfolds `@[reducible]` definitions). -/
macro "erw" c:optConfig s:rwRuleSeq : conv => `(conv| rw $[$(getConfigItems c)]* (transparency := .default) $s:rwRuleSeq)

/-- `args` traverses into all arguments. Synonym for `congr`. -/
macro "args" : conv => `(conv| congr)
/-- `left` traverses into the left argument. Synonym for `lhs`. -/
macro "left" : conv => `(conv| lhs)
/-- `right` traverses into the right argument. Synonym for `rhs`. -/
macro "right" : conv => `(conv| rhs)
/-- `intro` traverses into binders. Synonym for `ext`. -/
macro "intro" xs:(ppSpace colGt binderIdent)* : conv => `(conv| ext $xs*)

syntax enterArg := binderIdent <|> argArg

/-- `enter [arg, ...]` is a compact way to describe a path to a subterm.
It is a shorthand for other conv tactics as follows:
* `enter [i]` is equivalent to `arg i`.
* `enter [@i]` is equivalent to `arg @i`.
* `enter [x]` (where `x` is an identifier) is equivalent to `ext x`.
For example, given the target `f (g a (fun x => x b))`, `enter [1, 2, x, 1]`
will traverse to the subterm `b`. -/
syntax (name := enter) "enter" " [" withoutPosition(enterArg,+) "]" : conv

/-- The `apply thm` conv tactic is the same as `apply thm` the tactic.
There are no restrictions on `thm`, but strange results may occur if `thm`
cannot be reasonably interpreted as proving one equality from a list of others. -/
-- TODO: error if non-conv subgoals?
macro "apply " e:term : conv => `(conv| tactic => apply $e)

/-- `first | conv | ...` runs each `conv` until one succeeds, or else fails. -/
syntax (name := first) "first " withPosition((ppDedent(ppLine) colGe "| " convSeq)+) : conv

/-- `try tac` runs `tac` and succeeds even if `tac` failed. -/
macro "try " t:convSeq : conv => `(conv| first | $t | skip)

/--
`tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal, concatenating all goals
produced by `tac'`.
-/
macro:1 x:conv tk:" <;> " y:conv:0 : conv =>
  `(conv| tactic' => (conv' => $x:conv) <;>%$tk (conv' => $y:conv))

/-- `repeat convs` runs the sequence `convs` repeatedly until it fails to apply. -/
syntax "repeat " convSeq : conv
macro_rules
  | `(conv| repeat $seq) => `(conv| first | ($seq); repeat $seq | skip)

/--
`conv => ...` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://lean-lang.org/theorem_proving_in_lean4/conv.html> for more details.

Basic forms:
* `conv => cs` will rewrite the goal with conv tactics `cs`.
* `conv at h => cs` will rewrite hypothesis `h`.
* `conv in pat => cs` will rewrite the first subexpression matching `pat` (see `pattern`).
-/
-- HACK: put this at the end so that references to `conv` above
-- refer to the syntax category instead of this syntax
syntax (name := conv) "conv" (" at " ident)? (" in " (occs)? term)? " => " convSeq : tactic

/-- `norm_cast` tactic in `conv` mode. -/
syntax (name := normCast) "norm_cast" : conv

end Lean.Parser.Tactic.Conv
