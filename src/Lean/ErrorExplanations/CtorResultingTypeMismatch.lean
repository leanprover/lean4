/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
prelude
import Lean.ErrorExplanation

/--
In an inductive declaration, the resulting type of each constructor must match the type being
declared; if it does not, this error is raised. That is, every constructor of an inductive type must
return a value of that type. See the [Inductive Types](lean-manual://section/inductive-types) manual
section for additional details. Note that it is possible to omit the resulting type for a
constructor if the inductive type being defined has no indices.

# Examples

## Typo in resulting type
```lean broken
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Treee α
```
```output
Unexpected resulting type for constructor 'Tree.node': Expected an application of
  Tree
but found
  ?m.22
```
```lean fixed
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α
```

## Missing resulting type after constructor parameter

```lean broken
inductive Credential where
  | pin      : Nat
  | password : String
```
```output
Unexpected resulting type for constructor 'Credential.pin': Expected
  Credential
but found
  Nat
```
```lean fixed (title := "Fixed (resulting type)")
inductive Credential where
  | pin      : Nat → Credential
  | password : String → Credential
```
```lean fixed (title := "Fixed (named parameter)")
inductive Credential where
  | pin (num : Nat)
  | password (str : String)
```

If the type of a constructor is annotated, the full type—including the resulting type—must be
provided. Alternatively, constructor parameters can be written using named binders; this allows the
omission of the constructor's resulting type because it contains no indices.
-/
register_error_explanation lean.ctorResultingTypeMismatch {
  summary := "Resulting type of constructor was not the inductive type being declared."
  sinceVersion := "4.22.0"
}
