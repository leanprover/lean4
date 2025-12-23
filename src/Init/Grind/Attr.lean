/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Tactics

public section

namespace Lean.Grind
/--
Gadget for representing generalization steps `h : x = val` in patterns
This gadget is used to represent patterns in theorems that have been generalized to reduce the
number of casts introduced during E-matching based instantiation.

For example, consider the theorem
```
Option.pbind_some {α1 : Type u_1} {a : α1} {α2 : Type u_2}
    {f : (a_1 : α1) → some a = some a_1 → Option α2}
    : (some a).pbind f = f a rfl
```
Now, suppose we have a goal containing the term `c.pbind g` and the equivalence class
`{c, some b}`. The E-matching module generates the instance
```
(some b).pbind (cast ⋯ g)
```
The `cast` is necessary because `g`'s type contains `c` instead of `some b.
This `cast` problematic because we don't have a systematic way of pushing casts over functions
to its arguments. Moreover, heterogeneous equality is not effective because the following theorem
is not provable in DTT:
```
theorem hcongr (h₁ : f ≍ g) (h₂ : a ≍ b)  : f a ≍ g b := ...
```
The standard solution is to generalize the theorem above and write it as
```
theorem Option.pbind_some'
        {α1 : Type u_1} {a : α1} {α2 : Type u_2}
        {x : Option α1}
        {f : (a_1 : α1) → x = some a_1 → Option α2}
        (h : x = some a)
        : x.pbind f = f a h := by
  subst h
  apply Option.pbind_some
```
Internally, we use this gadget to mark the E-matching pattern as
```
(genPattern h x (some a)).pbind f
```
This pattern is matched in the same way we match `(some a).pbind f`, but it saves the proof
for the actual term to the `some`-application in `f`, and the actual term in `x`.

In the example above, `c.pbind g` also matches the pattern `(genPattern h x (some a)).pbind f`,
and stores `c` in `x`, `b` in `a`, and the proof that `c = some b` in `h`.
-/
def genPattern {α : Sort u} (_h : Prop) (x : α) (_val : α) : α := x

/-- Similar to `genPattern` but for the heterogeneous case -/
def genHEqPattern {α β : Sort u} (_h : Prop) (x : α) (_val : β) : α := x
end Lean.Grind

namespace Lean.Parser
/--
Reset all `grind` attributes. This command is intended for testing purposes only and should not be used in applications.
-/
syntax (name := resetGrindAttrs) "reset_grind_attrs%" : command

namespace Attr
syntax grindGen    := ppSpace &"gen"
/--
The `=` modifier instructs `grind` to check that the conclusion of the theorem is an equality,
and then uses the left-hand side of the equality as a pattern. This may fail if not all of the arguments appear
in the left-hand side.
-/
syntax grindEq     := "=" (grindGen)?
/--
The `=_` modifier instructs `grind` to check that the conclusion of the theorem is an equality,
and then uses the right-hand side of the equality as a pattern. This may fail if not all of the arguments appear
in the right-hand side.
-/
syntax grindEqRhs  := atomic("=" "_") (grindGen)?
/--
The `_=_` modifier acts like a macro which expands to `=` and `=_`.  It adds two patterns,
allowing the equality theorem to trigger in either direction.
-/
syntax grindEqBoth := atomic("_" "=" "_") (grindGen)?
/--
The `←=` modifier is unlike the other `grind` modifiers, and it used specifically for
backwards reasoning on equality. When a theorem's conclusion is an equality proposition and it
is annotated with `@[grind ←=]`, grind `will` instantiate it whenever the corresponding disequality
is assumed—this is a consequence of the fact that grind performs all proofs by contradiction.
Ordinarily, the grind attribute does not consider the `=` symbol when generating patterns.
-/
syntax grindEqBwd  := patternIgnore(atomic("←" "=") <|> atomic("<-" "="))
/--
The `←` modifier instructs `grind` to select a multi-pattern from the conclusion of theorem.
In other words, `grind` will use the theorem for backwards reasoning.
This may fail if not all of the arguments to the theorem appear in the conclusion.
Each time it encounters a subexpression which covers an argument which was not
previously covered, it adds that subexpression as a pattern, until all arguments have been covered.
If `grind!` is used, then only minimal indexable subexpressions are considered.
-/
syntax grindBwd    := patternIgnore("←" <|> "<-") (grindGen)?
/--
The `→` modifier instructs `grind` to select a multi-pattern from the hypotheses of the theorem.
In other words, `grind` will use the theorem for forwards reasoning.
To generate a pattern, it traverses the hypotheses of the theorem from left to right.
Each time it encounters a subexpression which covers an argument which was not
previously covered, it adds that subexpression as a pattern, until all arguments have been covered.
If `grind!` is used, then only minimal indexable subexpressions are considered.
-/
syntax grindFwd    := patternIgnore("→" <|> "->")
/--
The `⇐` modifier instructs `grind` to select a multi-pattern by traversing the conclusion, and then
all the hypotheses from right to left.
Each time it encounters a subexpression which covers an argument which was not
previously covered, it adds that subexpression as a pattern, until all arguments have been covered.
If `grind!` is used, then only minimal indexable subexpressions are considered.
-/
syntax grindRL     := patternIgnore("⇐" <|> "<=")
/--
The `⇒` modifier instructs `grind` to select a multi-pattern by traversing all the hypotheses from
left to right, followed by the conclusion.
Each time it encounters a subexpression which covers an argument which was not
previously covered, it adds that subexpression as a pattern, until all arguments have been covered.
If `grind!` is used, then only minimal indexable subexpressions are considered.
-/
syntax grindLR     := patternIgnore("⇒" <|> "=>")
/--
The `.` modifier instructs `grind` to select a multi-pattern by traversing the conclusion of the
theorem, and then the hypotheses from left to right. We say this is the default modifier.
Each time it encounters a subexpression which covers an argument which was not
previously covered, it adds that subexpression as a pattern, until all arguments have been covered.
If `grind!` is used, then only minimal indexable subexpressions are considered.
-/
syntax grindDef    := patternIgnore("." <|> "·") (grindGen)?
/--
The `usr` modifier indicates that this theorem was applied using a
**user-defined instantiation pattern**. Such patterns are declared with
the `grind_pattern` command, which lets you specify how `grind` should
match and use particular theorems.

Example:
- `grind [usr myThm]` means `grind` is using `myThm`, but with
  the custom pattern you defined with `grind_pattern`.
-/
syntax grindUsr    := &"usr"
/--
The `cases` modifier marks inductively-defined predicates as suitable for case splitting.
-/
syntax grindCases  := &"cases"
/--
The `cases eager` modifier marks inductively-defined predicates as suitable for case splitting,
and instructs `grind` to perform it eagerly while preprocessing hypotheses.
-/
syntax grindCasesEager := atomic(&"cases" &"eager")
/--
The `intro` modifier instructs `grind` to use the constructors (introduction rules)
of an inductive predicate as E-matching theorems.Example:
```
inductive Even : Nat → Prop where
| zero : Even 0
| add2 : Even x → Even (x + 2)

attribute [grind intro] Even
example (h : Even x) : Even (x + 6) := by grind
example : Even 0 := by grind
```
Here `attribute [grind intro] Even` acts like a macro that expands to
`attribute [grind] Even.zero` and `attribute [grind] Even.add2`.
This is especially convenient for inductive predicates with many constructors.
-/
syntax grindIntro  := &"intro"
/--
The `ext` modifier marks extensionality theorems for use by `grind`.
For example, the standard library marks `funext` with this attribute.

Whenever `grind` encounters a disequality `a ≠ b`, it attempts to apply any
available extensionality theorems whose matches the type of `a` and `b`.
-/
syntax grindExt    := &"ext"
/--
The `inj` modifier marks injectivity theorems for use by `grind`.
The conclusion of the theorem must be of the form `Function.Injective f`
where the term `f` contains at least one constant symbol.
-/
syntax grindInj    := &"inj"
/--
The `funCC` modifier marks global functions that support **function-valued congruence closure**.
Given an application `f a₁ a₂ … aₙ`, when `funCC := true`,
`grind` generates and tracks equalities for all partial applications:
- `f a₁`
- `f a₁ a₂`
- `…`
- `f a₁ a₂ … aₙ`
-/
syntax grindFunCC  := &"funCC"
/--
The `norm` modifier instructs `grind` to use a theorem as a normalization rule. That is,
the theorem is applied during the preprocessing step.
This feature is meant for advanced users who understand how the preprocessor and `grind`'s search
procedure interact with each other.
New users can still benefit from this feature by restricting its use to theorems that completely
eliminate a symbol from the goal. Example:
```
theorem max_def : max n m = if n ≤ m then m else n
```
For a negative example, consider:
```
opaque f : Int → Int → Int → Int
theorem fax1 : f x 0 1 = 1 := sorry
theorem fax2 : f 1 x 1 = 1 := sorry
attribute [grind norm] fax1
attribute [grind =] fax2

example (h : c = 1) : f c 0 c = 1 := by
  grind -- fails
```
In this example, `fax1` is a normalization rule, but it is not applicable to the input goal since
`f c 0 c` is not an instance of `f x 0 1`. However, `f c 0 c` matches the pattern `f 1 x 1` modulo
the equality `c = 1`. Thus, `grind` instantiates `fax2` with `x := 0`, producing the equality
`f 1 0 1 = 1`, which the normalizer simplifies to `True`. As a result, nothing useful is learned.
In the future, we plan to include linters to automatically detect issues like these.
Example:
```
opaque f : Nat → Nat
opaque g : Nat → Nat

@[grind norm] axiom fax : f x = x + 2
@[grind norm ←] axiom fg : f x = g x

example : f x ≥ 2 := by grind
example : f x ≥ g x := by grind
example : f x + g x ≥ 4 := by grind
```
-/
syntax grindNorm  := &"norm" (Tactic.simpPre <|> Tactic.simpPost)? patternIgnore("← " <|> "<- ")?
/--
The `unfold` modifier instructs `grind` to unfold the given definition during the preprocessing step.
Example:
```
@[grind unfold] def h (x : Nat) := 2 * x
example : 6 ∣ 3*h x := by grind
```
-/
syntax grindUnfold := &"unfold"
/--
`symbol <prio>` sets the priority of a constant for `grind`’s pattern-selection
procedure. `grind` prefers patterns that contain higher-priority symbols.
Example:
```
opaque p : Nat → Nat → Prop
opaque q : Nat → Nat → Prop
opaque r : Nat → Nat → Prop

attribute [grind symbol low] p
attribute [grind symbol high] q

axiom bar {x y} : p x y → q x x → r x y → r y x
attribute [grind →] bar
```
Here `p` is low priority, `q` is high priority, and `r` is default. `grind` first
tries to find a multi-pattern covering `x` and `y` using only high-priority
symbols while scanning hypotheses left to right. This fails because `q x x` does
not cover `y`. It then allows both high and default symbols and succeeds with
the multi-pattern `q x x, r x y`. The term `p x y` is ignored due to `p`’s low
priority. Symbols with priority `0` are never used in patterns.
-/
syntax grindSym    := &"symbol" ppSpace prio
syntax grindMod :=
    grindEqBoth <|> grindEqRhs <|> grindEq <|> grindEqBwd <|> grindBwd
    <|> grindFwd <|> grindRL <|> grindLR <|> grindUsr <|> grindCasesEager
    <|> grindCases <|> grindIntro <|> grindExt <|> grindGen <|> grindSym <|> grindInj
    <|> grindFunCC <|> grindNorm <|> grindUnfold <|> grindDef

/--
Marks a theorem or definition for use by the `grind` tactic.

An optional modifier (e.g. `=`, `→`, `←`, `cases`, `intro`, `ext`, `inj`, etc.)
controls how `grind` uses the declaration:
* whether it is applied forwards, backwards, or both,
* whether equalities are used on the left, right, or both sides,
* whether case-splits, constructors, extensionality, or injectivity are applied,
* or whether custom instantiation patterns are used.

See the individual modifier docstrings for details.
-/
syntax (name := grind) "grind" (ppSpace grindMod)? : attr
/--
Like `@[grind]`, but enforces the **minimal indexable subexpression condition**:
when several subterms cover the same free variables, `grind!` chooses the smallest one.

This influences E-matching pattern selection.

### Example
```lean
theorem fg_eq (h : x > 0) : f (g x) = x

@[grind <-] theorem fg_eq (h : x > 0) : f (g x) = x
-- Pattern selected: `f (g x)`

-- With minimal subexpression:
@[grind! <-] theorem fg_eq (h : x > 0) : f (g x) = x
-- Pattern selected: `g x`
```
-/
syntax (name := grind!) "grind!" (ppSpace grindMod)? : attr
/--
Like `@[grind]`, but also prints the pattern(s) selected by `grind`
as info messages. Useful for debugging annotations and modifiers.
-/
syntax (name := grind?) "grind?" (ppSpace grindMod)? : attr
/--
Like `@[grind!]`, but also prints the pattern(s) selected by `grind`
as info messages. Combines minimal subexpression selection with debugging output.
-/
syntax (name := grind!?) "grind!?" (ppSpace grindMod)? : attr
end Attr
end Lean.Parser
