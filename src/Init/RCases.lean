/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jacob von Raumer
-/
prelude
import Init.Tactics
import Init.Meta


/-!
# Recursive cases (`rcases`) tactic and related tactics

`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* A `@` before a tuple pattern as in `@⟨p1, p2, p3⟩` will bind all arguments in the constructor,
  while leaving the `@` off will only use the patterns on the explicit arguments.
* An alternation pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

The patterns are fairly liberal about the exact shape of the constructors, and will insert
additional alternation branches and tuple arguments if there are not enough arguments provided, and
reuse the tail for further matches if there are too many arguments provided to alternation and
tuple patterns.

This file also contains the `obtain` and `rintro` tactics, which use the same syntax of `rcases`
patterns but with a slightly different use case:

* `rintro` (or `rintros`) is used like `rintro x ⟨y, z⟩` and is the same as `intros` followed by
  `rcases` on the newly introduced arguments.
* `obtain` is the same as `rcases` but with a syntax styled after `have` rather than `cases`.
  `obtain ⟨hx, hy⟩ | hz := foo` is equivalent to `rcases foo with ⟨hx, hy⟩ | hz`. Unlike `rcases`,
  `obtain` also allows one to omit `:= foo`, although a type must be provided in this case,
  as in `obtain ⟨hx, hy⟩ | hz : a ∧ b ∨ c`, in which case it produces a subgoal for proving
  `a ∧ b ∨ c` in addition to the subgoals `hx : a, hy : b |- goal` and `hz : c |- goal`.

## Tags

rcases, rintro, obtain, destructuring, cases, pattern matching, match
-/
namespace Lean.Parser.Tactic

/-- The syntax category of `rcases` patterns. -/
declare_syntax_cat rcasesPat
/-- A medium precedence `rcases` pattern is a list of `rcasesPat` separated by `|` -/
syntax rcasesPatMed := sepBy1(rcasesPat, " | ")
/-- A low precedence `rcases` pattern is a `rcasesPatMed` optionally followed by `: ty` -/
syntax rcasesPatLo := rcasesPatMed (" : " term)?
/-- `x` is a pattern which binds `x` -/
syntax (name := rcasesPat.one) ident : rcasesPat
/-- `_` is a pattern which ignores the value and gives it an inaccessible name -/
syntax (name := rcasesPat.ignore) "_" : rcasesPat
/-- `-` is a pattern which removes the value from the context -/
syntax (name := rcasesPat.clear) "-" : rcasesPat
/--
A `@` before a tuple pattern as in `@⟨p1, p2, p3⟩` will bind all arguments in the constructor,
while leaving the `@` off will only use the patterns on the explicit arguments.
-/
syntax (name := rcasesPat.explicit) "@" noWs rcasesPat : rcasesPat
/--
`⟨pat, ...⟩` is a pattern which matches on a tuple-like constructor
or multi-argument inductive constructor
-/
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
/-- `(pat)` is a pattern which resets the precedence to low -/
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat

/-- The syntax category of `rintro` patterns. -/
declare_syntax_cat rintroPat
/-- An `rcases` pattern is an `rintro` pattern -/
syntax (name := rintroPat.one) rcasesPat : rintroPat
/--
A multi argument binder `(pat1 pat2 : ty)` binds a list of patterns and gives them all type `ty`.
-/
syntax (name := rintroPat.binder) (priority := default+1) -- to override rcasesPat.paren
  "(" rintroPat+ (" : " term)? ")" : rintroPat

/- TODO
/--
`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.
-/
syntax (name := rcases?) "rcases?" elimTarget,* (" : " num)? : tactic
-/

/--
`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* A `@` before a tuple pattern as in `@⟨p1, p2, p3⟩` will bind all arguments in the constructor,
  while leaving the `@` off will only use the patterns on the explicit arguments.
* An alternation pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
assumption `h : e = PAT` will be added to the context.
-/
syntax (name := rcases) "rcases" elimTarget,* (" with " rcasesPatLo)? : tactic

/--
The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
obtain ⟨patt⟩ : type := proof
```
is equivalent to
```lean
have h : type := proof
rcases h with ⟨patt⟩
```

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.
-/
syntax (name := obtain) "obtain" (ppSpace rcasesPatMed)? (" : " term)? (" := " term,+)? : tactic

/- TODO
/--
`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.
-/
syntax (name := rintro?) "rintro?" (" : " num)? : tactic
-/

/--
The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.
-/
syntax (name := rintro) "rintro" (ppSpace colGt rintroPat)+ (" : " term)? : tactic

end Lean.Parser.Tactic
