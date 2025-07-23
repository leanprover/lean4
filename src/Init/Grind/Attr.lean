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
syntax grindEq     := "=" (grindGen)?
syntax grindEqBoth := atomic("_" "=" "_") (grindGen)?
syntax grindEqRhs  := atomic("=" "_") (grindGen)?
syntax grindEqBwd  := patternIgnore(atomic("←" "=") <|> atomic("<-" "="))
syntax grindBwd    := patternIgnore("←" <|> "<-") (grindGen)?
syntax grindFwd    := patternIgnore("→" <|> "->")
syntax grindRL     := patternIgnore("⇐" <|> "<=")
syntax grindLR     := patternIgnore("⇒" <|> "=>")
syntax grindUsr    := &"usr"
syntax grindCases  := &"cases"
syntax grindCasesEager := atomic(&"cases" &"eager")
syntax grindIntro  := &"intro"
syntax grindExt    := &"ext"
syntax grindSym    := &"symbol" ppSpace prio
syntax grindMod :=
    grindEqBoth <|> grindEqRhs <|> grindEq <|> grindEqBwd <|> grindBwd
    <|> grindFwd <|> grindRL <|> grindLR <|> grindUsr <|> grindCasesEager
    <|> grindCases <|> grindIntro <|> grindExt <|> grindGen <|> grindSym
syntax (name := grind) "grind" (ppSpace grindMod)? : attr
syntax (name := grind?) "grind?" (ppSpace grindMod)? : attr
end Attr
end Lean.Parser
