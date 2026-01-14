/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Parser.Command
public section
namespace Lean.Parser.Command

namespace GrindCnstr

def isValue := leading_parser nonReservedSymbol "is_value " >> ident >> optional ";"
def isStrictValue := leading_parser nonReservedSymbol "is_strict_value " >> ident >> optional ";"
def notValue := leading_parser nonReservedSymbol "not_value " >> ident >> optional ";"
def notStrictValue := leading_parser nonReservedSymbol "not_strict_value " >> ident >> optional ";"
def isGround := leading_parser nonReservedSymbol "is_ground " >> ident >> optional ";"
def sizeLt := leading_parser nonReservedSymbol "size " >> ident >> " < " >> numLit >> optional ";"
def depthLt := leading_parser nonReservedSymbol "depth " >> ident >> " < " >> numLit >> optional ";"
def genLt := leading_parser nonReservedSymbol "gen" >> " < " >> numLit >> optional ";"
def maxInsts := leading_parser nonReservedSymbol "max_insts" >> " < " >> numLit >> optional ";"
def guard := leading_parser nonReservedSymbol "guard " >> checkColGe "irrelevant" >> termParser >> optional ";"
def check := leading_parser nonReservedSymbol "check " >> checkColGe "irrelevant" >> termParser >> optional ";"
def notDefEq := leading_parser atomic (ident >> " =/= ") >> checkColGe "irrelevant" >> termParser >> optional ";"
def defEq := leading_parser atomic (ident >> " =?= ") >> checkColGe "irrelevant" >> termParser >> optional ";"

end GrindCnstr

open GrindCnstr in
def grindPatternCnstr : Parser :=
  isValue <|> isStrictValue <|> notValue <|> notStrictValue <|> isGround <|> sizeLt <|> depthLt <|> genLt <|> maxInsts
  <|> guard <|> GrindCnstr.check <|> notDefEq <|> defEq

def grindPatternCnstrs : Parser := leading_parser "where " >> many1Indent (ppLine >> grindPatternCnstr)

/-!
Builtin parsers for `grind` related commands
-/

/--
The `grind_pattern` command can be used to manually select a pattern for theorem instantiation.
Enabling the option `trace.grind.ematch.instance` causes `grind` to print a trace message for each
theorem instance it generates, which can be helpful when determining patterns.

When multiple patterns are specified together, all of them must match in the current context before
`grind` attempts to instantiate the theorem. This is referred to as a *multi-pattern*.
This is useful for theorems such as transitivity rules, where multiple premises must be simultaneously
present for the rule to apply.

In the following example, `R` is a transitive binary relation over `Int`.
```
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z
```
To use the fact that `R` is transitive, `grind` must already be able to satisfy both premises.
This is represented using a multi-pattern:
```
grind_pattern Rtrans => R x y, R y z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```
The multi-pattern `R x y`, `R y z` instructs `grind` to instantiate `Rtrans` only when both `R x y`
and `R y z` are available in the context. In the example, `grind` applies `Rtrans` to derive `R a c`
from `R a b` and `R b c`, and can then repeat the same reasoning to deduce `R a d` from `R a c` and
`R c d`.

You can add constraints to restrict theorem instantiation. For example:
```
grind_pattern extract_extract => (as.extract i j).extract k l where
  as =/= #[]
```
The constraint instructs `grind` to instantiate the theorem only if `as` is **not** definitionally equal
to `#[]`.

## Constraints

- `x =/= term`: The term bound to `x` (one of the theorem parameters) is **not** definitionally equal to `term`.
  The term may contain holes (i.e., `_`).

- `x =?= term`: The term bound to `x` is definitionally equal to `term`.
  The term may contain holes (i.e., `_`).

- `size x < n`: The term bound to `x` has size less than `n`. Implicit arguments
and binder types are ignored when computing the size.

- `depth x < n`: The term bound to `x` has depth less than `n`.

- `is_ground x`: The term bound to `x` does not contain local variables or meta-variables.

- `is_value x`: The term bound to `x` is a value. That is, it is a constructor fully applied to value arguments,
a literal (`Nat`, `Int`, `String`, etc.), or a lambda `fun x => t`.

- `is_strict_value x`: Similar to `is_value`, but without lambdas.

- `not_value x`: The term bound to `x` is a **not** value (see `is_value`).

- `not_strict_value x`: Similar to `not_value`, but without lambdas.

- `gen < n`: The theorem instance has generation less than `n`. Recall that each term is assigned a
generation, and terms produced by theorem instantiation have a generation that is one greater than
the maximal generation of all the terms used to instantiate the theorem. This constraint complements
the `gen` option available in `grind`.

- `max_insts < n`: A new instance is generated only if less than `n` instances have been generated so far.

- `guard e`: The instantiation is delayed until `grind` learns that `e` is `true` in this state.

- `check e`: Similar to `guard e`, but `grind` checks whether `e` is implied by its current state by
assuming `¬ e` and trying to deduce an inconsistency.

## Example

Consider the following example where `f` is a monotonic function
```
opaque f : Nat → Nat
axiom fMono : x ≤ y → f x ≤ f y
```
and you want to instruct `grind` to instantiate `fMono` for every pair of terms `f x` and `f y` when
`x ≤ y` and `x` is **not** definitionally equal to `y`. You can use
```
grind_pattern fMono => f x, f y where
  guard x ≤ y
  x =/= y
```
Then, in the following example, only three instances are generated.
```
/--
trace: [grind.ematch.instance] fMono: a ≤ f a → f a ≤ f (f a)
[grind.ematch.instance] fMono: f a ≤ f (f a) → f (f a) ≤ f (f (f a))
[grind.ematch.instance] fMono: a ≤ f (f a) → f a ≤ f (f (f a))
-/
#guard_msgs in
example : f b = f c → a ≤ f a → f (f a) ≤ f (f (f a)) := by
  set_option trace.grind.ematch.instance true in
  grind
```
-/
@[builtin_command_parser] def grindPattern := leading_parser
  Term.attrKind >> "grind_pattern " >>  optional ("[" >> ident >> "]") >> ident >> darrow >> sepBy1 termParser "," >> optional grindPatternCnstrs

@[builtin_command_parser] def initGrindNorm := leading_parser
  "init_grind_norm " >> many ident >> "| " >> many ident

end Lean.Parser.Command
