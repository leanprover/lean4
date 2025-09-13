/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
module

prelude
public import Lean.ErrorExplanation
meta import Lean.ErrorExplanation

public section

/--
This error occurs when the type of a definition is not fully specified and Lean is unable to infer
its type from the available information. If the definition has parameters, this error refers only to
the resulting type after the colon (the error
[`lean.inferBinderTypeFailed`](lean-manual://errorExplanation/lean.inferBinderTypeFailed) indicates
that a parameter type could not be inferred).

To resolve this error, provide additional type information in the definition. This can be done
straightforwardly by providing an explicit resulting type after the colon in the definition
header. Alternatively, if an explicit resulting type is not provided, adding further type
information to the definition's body—such as by specifying implicit type arguments or giving
explicit types to `let` binders—may allow Lean to infer the type of the definition. Look for type
inference or implicit argument synthesis errors that arise alongside this one to identify
ambiguities that may be contributing to this error.

Note that when an explicit resulting type is provided—even if that type contains holes—Lean will not
use information from the definition body to help infer the type of the definition or its parameters.
Thus, adding an explicit resulting type may also necessitate adding type annotations to parameters
whose types were previously inferrable. Additionally, it is always necessary to provide an explicit
type in a `theorem` declaration: the `theorem` syntax requires a type annotation, and the elaborator
will never attempt to use the theorem body to infer the proposition being proved.

# Examples

## Implicit argument cannot be inferred

```lean broken
def emptyNats :=
  []
```
```output
Failed to infer type of definition `emptyNats`
```

```lean fixed (title := "Fixed (type annotation)")
def emptyNats : List Nat :=
  []
```
```lean fixed (title := "Fixed (implicit argument)")
def emptyNats :=
  List.nil (α := Nat)
```

Here, Lean is unable to infer the value of the parameter `α` of the `List` type constructor, which
in turn prevents it from inferring the type of the definition. Two fixes are possible: specifying
the expected type of the definition allows Lean to infer the appropriate implicit argument to the
`List.nil` constructor; alternatively, making this implicit argument explicit in the function body
provides sufficient information for Lean to infer the definition's type.

## Definition type uninferrable due to unknown parameter type

```lean broken
def identity x :=
  x
```
```output
Failed to infer type of definition `identity`
```
```lean fixed
def identity (x : α) :=
  x
```

In this example, the type of `identity` is determined by the type of `x`, which cannot be inferred.
Both the indicated error and
[lean.inferBinderTypeFailed](lean-manual://errorExplanation/lean.inferBinderTypeFailed) therefore
appear (see that explanation for additional discussion of this example). Resolving the latter—by
explicitly specifying the type of `x`—provides Lean with sufficient information to infer the
definition type.
-/
register_error_explanation lean.inferDefTypeFailed {
  summary := "The type of a definition could not be inferred."
  sinceVersion := "4.23.0"
}
