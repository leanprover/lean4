/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.NotationExtra

namespace Lean.Parser.Tactic.Conv

declare_syntax_cat conv (behavior := both)

syntax convSeq1Indented := withPosition((colGe conv ";"?)+)
syntax convSeqBracketed := "{" (conv ";"?)* "}"
-- Order is important: a missing `conv` proof should not be parsed as `{ <missing> }`,
-- automatically closing goals
syntax convSeq := convSeqBracketed <|> convSeq1Indented

/--
`conv => ...` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://leanprover.github.io/theorem_proving_in_lean4/conv.html> for more details.

Basic forms:
* `conv => cs` will rewrite the goal with conv tactics `cs`.
* `conv at h => cs` will rewrite hypothesis `h`.
* `conv in pat => cs` will rewrite the first subexpression matching `pat`.
-/
syntax (name := conv) "conv " (" at " ident)? (" in " term)? " => " convSeq : tactic

/-- `skip` does nothing. -/
syntax (name := skip) "skip" : conv

/-- Traverses into the left subterm of a binary operator.
(In general, for an `n`-ary operator, it traverses into the second to last argument.) -/
syntax (name := lhs) "lhs" : conv

/-- Traverses into the right subterm of a binary operator.
(In general, for an `n`-ary operator, it traverses into the last argument.) -/
syntax (name := rhs) "rhs" : conv

/-- Reduces the target to Weak Head Normal Form. This reduces definitions
in "head position" until a constructor is exposed. For example, `List.map f [a, b, c]`
weak head normalizes to `f a :: List.map f [b, c]`. -/
syntax (name := whnf) "whnf" : conv

/-- Expand let-declarations and let-variables. -/
syntax (name := zeta) "zeta" : conv

/-- Put term in normal form, this tactic is ment for debugging purposes only -/
syntax (name := reduce) "reduce" : conv

/-- Performs one step of "congruence", which takes a term and produces
subgoals for all the function arguments. For example, if the target is `f x y` then
`congr` produces two subgoals, one for `x` and one for `y`. -/
syntax (name := congr) "congr" : conv

/--
* `arg i` traverses into the `i`'th argument of the target. For example if the
  target is `f a b c d` then `arg 1` traverses to `a` and `arg 3` traverses to `c`.
* `arg @i` is the same as `arg i` but it counts all arguments instead of just the
  explicit arguments. -/
syntax (name := arg) "arg " "@"? num : conv

/-- `ext x` traverses into a binder (a `fun x => e` or `∀ x, e` expression)
to target `e`, introducing name `x` in the process. -/
syntax (name := ext) "ext " (colGt ident)* : conv

/-- `change t'` replaces the target `t` with `t'`,
assuming `t` and `t'` are definitionally equal. -/
syntax (name := change) "change " term : conv

/-- `delta foo` unfolds all occurrences of `foo` in the target.
Like the `delta` tactic, this ignores any definitional equations and uses
primitive delta-reduction instead, which may result in leaking implementation details.
Users should prefer `unfold` for unfolding definitions. -/
syntax (name := delta) "delta " ident : conv

/-- `unfold foo` unfolds all occurrences of `foo` in the target.
Like the `unfold` tactic, this uses equational lemmas for the chosen definition
to rewrite the target. For recursive definitions,
only one layer of unfolding is performed. -/
syntax (name := unfold) "unfold " ident : conv

/-- `pattern pat` traverses to the first subterm of the target that matches `pat`. -/
syntax (name := pattern) "pattern " term : conv

/-- `rw [thm]` rewrites the target using `thm`. See the `rw` tactic for more information. -/
syntax (name := rewrite) "rewrite " (config)? rwRuleSeq : conv

/-- `simp [thm]` performs simplification using `thm` and marked `@[simp]` lemmas.
See the `simp` tactic for more information. -/
syntax (name := simp) "simp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? : conv

/-- `simp_match` simplifies match expressions. For example,
```
match [a, b] with
| [] => 0
| hd :: tl => hd
```
simplifies to `a`. -/
syntax (name := simpMatch) "simp_match" : conv


/-- Execute the given tactic block without converting `conv` goal into a regular goal -/
syntax (name := nestedTacticCore) "tactic'" " => " tacticSeq : conv

/-- Focus, convert the `conv` goal `⊢ lhs` into a regular goal `⊢ lhs = rhs`, and then execute the given tactic block. -/
syntax (name := nestedTactic) "tactic" " => " tacticSeq : conv

/-- `{ convs }` runs the list of `convs` on the current target, and any subgoals that
remain are trivially closed by `skip`. -/
syntax (name := nestedConv) convSeqBracketed : conv

/-- `(convs)` runs the `convs` in sequence on the current list of targets.
This is pure grouping with no added effects. -/
syntax (name := paren) "(" convSeq ")" : conv

/-- `conv => cs` runs `cs` in sequence on the target `t`,
resulting in `t'`, which becomes the new target subgoal. -/
syntax (name := convConvSeq) "conv " " => " convSeq : conv

/-- `· conv` focuses on the main conv goal and tries to solve it using `s` -/
macro dot:("·" <|> ".") s:convSeq : conv => `({%$dot ($s) })

/-- `rw [rules]` applies the given list of rewrite rules to the target.
See the `rw` tactic for more information. -/
macro "rw " c:(config)? s:rwRuleSeq : conv => `(rewrite $[$c]? $s)

/-- `erw [rules]` is a shorthand for `rw (config := { transparency := .default }) [rules]`.
This does rewriting up to unfolding of regular definitions (by comparison to regular `rw`
which only unfolds `@[reducible]` definitions). -/
macro "erw " s:rwRuleSeq : conv => `(rw (config := { transparency := .default }) $s)

/-- `args` traverses into all arguments. Synonym for `congr`. -/
macro "args" : conv => `(congr)
/-- `left` traverses into the left argument. Synonym for `lhs`. -/
macro "left" : conv => `(lhs)
/-- `right` traverses into the right argument. Synonym for `rhs`. -/
macro "right" : conv => `(rhs)
/-- `intro` traverses into binders. Synonym for `ext`. -/
macro "intro " xs:(colGt ident)* : conv => `(conv| ext $xs*)

syntax enterArg := ident <|> ("@"? num)

/-- `enter [arg, ...]` is a compact way to describe a path to a subterm.
It is a shorthand for other conv tactics as follows:
* `enter [i]` is equivalent to `arg i`.
* `enter [@i]` is equivalent to `arg @i`.
* `enter [x]` (where `x` is an identifier) is equivalent to `ext x`.
For example, given the target `f (g a (fun x => x b))`, `enter [1, 2, x, 1]`
will traverse to the subterm `b`. -/
syntax "enter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:num]) => `(conv| arg $i)
  | `(conv| enter [@$i]) => `(conv| arg @$i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))

/-- `rfl` closes one conv goal "trivially", by using reflexivity
(that is, no rewriting). -/
macro "rfl" : conv => `(tactic => rfl)

/-- `done` succeeds iff there are no goals remaining. -/
macro "done" : conv => `(tactic' => done)

/-- `trace_state` prints the current goal state. -/
macro "trace_state" : conv => `(tactic' => trace_state)

/-- The `apply thm` conv tactic is the same as `apply thm` the tactic.
There are no restrictions on `thm`, but strange results may occur if `thm`
cannot be reasonably interpreted as proving one equality from a list of others. -/
-- TODO: error if non-conv subgoals?
macro "apply " e:term : conv => `(tactic => apply $e)

/-- `first | conv | ...` runs each `conv` until one succeeds, or else fails. -/
syntax (name := first) "first " withPosition((colGe "|" convSeq)+) : conv

/-- `repeat convs` runs the sequence `convs` repeatedly until it fails to apply. -/
syntax "repeat " convSeq : conv
macro_rules
  | `(conv| repeat $seq) => `(conv| first | ($seq); repeat $seq | rfl)

end Lean.Parser.Tactic.Conv
