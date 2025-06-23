/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
prelude
import Lean.ErrorExplanation

/--
This error occurs when a parameter of an inductive type is not uniform in an inductive
declaration. The parameters of an inductive type (i.e., those that appear before the colon following
the `inductive` keyword) must be identical in all occurrences of the type being defined in its
constructors' types. If a parameter of an inductive type must vary between constructors, make the
parameter an index by moving it to the right of the colon. See the manual section on
[Inductive Types](lean-manual://section/inductive-types) for additional details.

Note that auto-implicit inlay hints always appear left of the colon in an inductive declaration
(i.e., as parameters), even when they are actually indices. This means that double-clicking on an
inlay hint to insert such parameters may result in this error. If it does, change the inserted
parameters to indices.

# Examples

## Vector length index as a parameter

```lean broken
inductive Vec (α : Type) (n : Nat) : Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```
```output broken
Mismatched inductive type parameter in
  Vec α 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter 'n' must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
```lean fixed
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```

The length argument `n` of the `Vec` type constructor is declared as a parameter, but other values
for this argument appear in the `nil` and `cons` constructors (namely, `0` and `n + 1`). An error
therefore appears at the first occurrence of such an argument. To correct this, `n` cannot be a
parameter of the inductive declaration and must instead be an index, as in the corrected example. On
the other hand, `α` remains unchanged throughout all occurrences of `Vec` in the declaration and so
is a valid parameter.
-/
register_error_explanation lean.inductiveParamMismatch {
  summary := "Invalid parameter in an occurrence of an inductive type in one of its constructors."
  sinceVersion := "4.22.0"
}
