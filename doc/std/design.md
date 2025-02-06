# Standard library API design principles and best practices

This document collects loosely organized notes on how to design APIs for the Lean standard library. It supplements the [style guide](./style.md) and [naming scheme](./naming.md).
It will also serve as a place for the standard library team to record decisions for future reference and to promote consistency across the library.

## Binder types

### Heuristics for selecting implicit variables

*TODO*

### Binder types for data-carrying typeclasses

Users will occasionally attempt constructions such as

```lean
import Std.Data.HashMap

open Std (HashMap)

structure A (α) extends BEq α, Hashable α where
  foo : HashMap α Nat

variable [BEq α]

def A.add (xs : A α) (x : α) : A α := { xs with foo := xs.foo.insert x 5 }
```

For this to work, the `HashMap.insert` function needs to resolve `BEq α` via unification rather than typeclass synthesis.

So we formulate the following principle:

> **If a data type `α` depends on a `Type`-valued type class, then all functions and theorems which have a parameter of type
> `α` should take the type class as an implicit argument.**

## Nested inductive types

Nested inductive datatypes are indispensible in many applications, so we formulate the following principle:

> **Data types which cannot be used in nested inductive types must come with variants which can.**

## Executable definitions must be fast or marked as not intended for execution

It is not unusual to write definitions in Lean that are purely for verification puporses and not intended to be executed, even though they are perfectly executable from the
compiler's perspective. To avoid unwelcome surprised, the have the following guideline:

> **All public definitions must be efficient when used in compiled code (potentially via `@[csimp]`), unless
> explicitly marked as not indended for execution in a documentation string (or, even better, through a suggestive name and a documentation string).**

## Orphan rule for instances and attributes

We adopt the following orphan rule for instances and attributes:

> **If `S` is a set of standard library modules such that importing `S` imports both a type `α` and a typeclass `T`, then importing `S` must also import all instances of `T α` that are available in the standard library. Similarly, if `S` is a set of standard library modules such that importing `S` imports both a type `α` and an attribute `a`, then `S` must also import all occurrences of `attribute [a] α` in the standard library.**

This is slightly weaker than "every instance for a type must be provided in the file that defines the type or in the file that defines the class" because it allows developing a concept internally before exposing everything at once in a public file.

The purpose of this rule is to eliminate instances where the answer to the question "why does this not work?" is "you forgot to import a certain file", and also to eliminate cases where just importing additional modules breaks downstream code ("spooky action at a distance").

## Converting between types

### Conventions for `X.toY` and `Y.ofX` functions

*TODO*

### When to introduce coercions

*TODO*

## Proofs in theorem statements

If a function with a proof argument (like `Option.get`) appears on the RHS of a lemma, then rewriting with that lemma may introduce the proof to the goal state without the user
having easy access to it. Since further tactic manipulation can lead to the user having to reprove the claim thus introduced, we introduce the following guideline:

> **Proofs that appear in theorem statements should be a hypothesis, single lemma application, single tactic application or very short term proof.**

If a more complex proof is required, it should be factored out into a reusable lemma that is available to users.

## Order of equality statements

Whenever `=` or `==` appears in a statement, there is a choice as to how to order the arguments. We adopt the following convention:

> **Put the "more constant" variable on the right-hand side of a comparison statement.**

The idea behind this convention is to be consistent with intuitive usage (for example, most people are more likely to write `l.find? (· == 1)` than `l.find? (1 == ·))`).

This extends to the case where both arguments are variables, by deciding that a search key is "more constant" than the thing being searched, as in the following example:

```lean
theorem getElem?_insert [EquivBEq α] [LawfulHashable α] {m : HashMap α β} {k a : α} {v : β} :
    (m.insert k v)[a]? = if k == a then some v else m[a]?
```
