/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
module

prelude
public import Lean.ErrorExplanation

public section

/--
This error indicates that dotted identifier notation was used in an invalid or unsupported context.
Dotted identifier notation allows an identifier's namespace to be omitted, provided that it can be
inferred by Lean based on type information. Details about this notation can be found in the manual
section on [identifiers](lean-manual://section/identifiers-and-resolution).

This notation can only be used in a term whose type Lean is able to infer. If there is insufficient
type information for Lean to do so, this error will be raised. The inferred type must not be a type
universe (e.g., `Prop` or `Type`), as dotted-identifier notation is not supported on these types.

# Examples

## Insufficient type information

```lean broken
def reverseDuplicate (xs : List α) :=
  .reverse (xs ++ xs)
```
```output
Invalid dotted identifier notation: The expected type of `.reverse` could not be determined
```
```lean fixed
def reverseDuplicate (xs : List α) : List α :=
  .reverse (xs ++ xs)
```
Because the return type of `reverseDuplicate` is not specified, the expected type of `.reverse`
cannot be determined. Lean will not use the type of the argument `xs ++ xs` to infer the omitted
namespace. Adding the return type `List α` allows Lean to infer the type of `.reverse` and thus the
appropriate namespace (`List`) in which to resolve this identifier.

Note that this means that changing the return type of `reverseDuplicate` changes how `.reverse`
resolves: if the return type is  `T`, then Lean will (attempt to) resolve `.reverse` to a function
`T.reverse` whose return type is `T`—even if `T.reverse` does not take an argument of type
`List α`.

## Dotted identifier where type universe expected

```lean broken
example (n : Nat) :=
  match n > 42 with
  | .true  => n - 1
  | .false => n + 1
```
```output
Invalid dotted identifier notation: Not supported on type universe
  Prop
```
```lean fixed
example (n : Nat) :=
  match decide (n > 42) with
  | .true  => n - 1
  | .false => n + 1
```

The proposition `n > 42` has type `Prop`, which, being a type universe, does not support
dotted-identifier notation. As this example demonstrates, attempting to use this notation in such a
context is almost always an error. The intent in this example was for `.true` and `.false` to be
Booleans, not propositions; however, `match` expressions do not automatically perform this coercion
for decidable propositions. Explicitly adding `decide` makes the discriminant a `Bool` and allows
the dotted-identifier resolution to succeed.
-/
register_error_explanation lean.invalidDottedIdent {
  summary := "Dotted identifier notation used with invalid or uninferrable expected type."
  sinceVersion := "4.22.0"
}
