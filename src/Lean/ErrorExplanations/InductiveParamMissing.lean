/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
prelude
import Lean.ErrorExplanation

/--
This error occurs when an inductive type constructor is partially applied in the type of one of its
constructors such that one or more parameters of the type are omitted. The elaborator requires that
all parameters of an inductive type be specified everywhere that type is referenced in its
definition, including in the types of its constructors.

If it is necessary to allow the type constructor to be partially applied, without specifying a given
type parameter, that parameter must be converted to an index. See the manual section on
[Inductive Types](lean-manual://section/inductive-types) for further explanation of the difference
between indices and parameters.

# Examples

## Omitting parameter in argument to higher-order predicate

```lean broken
inductive List.All {α : Type u} (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

structure RoseTree (α : Type u) where
  val : α
  children : List (RoseTree α)

inductive RoseTree.All {α : Type u} (P : α → Prop) (t : RoseTree α) : Prop
  | intro : P t.val → List.All (All P) t.children → All P t
```
```output
Missing parameter(s) in occurrence of inductive type: In the expression
  List.All (All P) t.children
found
  All P
but expected all parameters to be specified:
  All P t

Note: All occurrences of an inductive type in the types of its constructors must specify its fixed parameters. Only indices can be omitted in a partial application of the type constructor.
```
```lean fixed
inductive List.All {α : Type u} (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

structure RoseTree (α : Type u) where
  val : α
  children : List (RoseTree α)

inductive RoseTree.All {α : Type u} (P : α → Prop) : RoseTree α → Prop
  | intro : P t.val → List.All (All P) t.children → All P t
```
Because the `RoseTree.All` type constructor must be partially applied in the argument to `List.All`,
the unspecified argument (`t`) must not be a parameter of the `RoseTree.All` predicate. Making it an
index to the right of the colon in the header of `RoseTree.All` allows this partial application to
succeed.
-/
register_error_explanation lean.inductiveParamMissing {
  summary := "Parameter not present in an occurrence of an inductive type in one of its constructors."
  sinceVersion := "4.22.0"
}
