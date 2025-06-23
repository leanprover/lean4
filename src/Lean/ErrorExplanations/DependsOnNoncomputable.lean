/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
prelude
import Lean.ErrorExplanation

/--
This error indicates that the specified definition depends on one or more definitions that do not
contain executable code and is therefore required to be marked as `noncomputable`. Such definitions
can be type-checked but do not contain code that can be executed by Lean.

If you intended for the definition named in the error message to be noncomputable, marking it as
`noncomputable` will resolve this error. If you did not, inspect the noncomputable definitions on
which it depends: they may be noncomputable because they failed to compile, are `axiom`s, or were
themselves marked as `noncomputable`. Making all of your definition's noncomputable dependencies
computable will also resolve this error. See the manual section on
[Modifiers](lean-manual://section/declaration-modifiers) for more information about noncomputable
definitions.

# Examples

## Necessarily noncomputable function not appropriately marked

```lean broken
axiom transform : Nat → Nat

def transformIfZero : Nat → Nat
  | 0 => transform 0
  | n => n
```
```output
axiom 'transform' not supported by code generator; consider marking definition as 'noncomputable'
```
```lean fixed
axiom transform : Nat → Nat

noncomputable def transformIfZero : Nat → Nat
  | 0 => transform 0
  | n => n
```
In this example, `transformIfZero` depends on the axiom `transform`. Because `transform` is an
axiom, it does not contain any executable code; although the value `transform 0` has type `Nat`,
there is no way to compute its value. Thus, `transformIfZero` must be marked `noncomputable` because
its execution would depend on this axiom.

## Noncomputable dependency can be made computable

```lean broken
noncomputable def getOrDefault [Nonempty α] : Option α → α
  | some x => x
  | none => Classical.ofNonempty

def endsOrDefault (ns : List Nat) : Nat × Nat :=
  let head := getOrDefault ns.head?
  let tail := getOrDefault ns.getLast?
  (head, tail)
```
```output
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'getOrDefault', which is 'noncomputable'
```
```lean fixed (title := "Fixed (computable)")
def getOrDefault [Inhabited α] : Option α → α
  | some x => x
  | none => default

def endsOrDefault (ns : List Nat) : Nat × Nat :=
  let head := getOrDefault ns.head?
  let tail := getOrDefault ns.getLast?
  (head, tail)
```
The original definition of `getOrDefault` is noncomputable due to its use of `Classical.choice`.
Unlike in the preceding example, however, it is possible to implement a similar but computable
version of `getOrDefault` (using the `Inhabited` type class), allowing `endsOrDefault` to be
computable. (The differences between `Inhabited` and `Nonempty` are described in the documentation
of inhabited types in the manual section on [Basic Classes](lean-manual://section/basic-classes).)

## Noncomputable instance in namespace

```lean broken
open Classical in
/--
Returns `y` if it is in the image of `f`,
or an element of the image of `f` otherwise.
-/
def fromImage (f : Nat → Nat) (y : Nat) :=
  if ∃ x, f x = y then
    y
  else
    f 0
```
```output
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Classical.propDecidable', which is 'noncomputable'
```
```lean fixed
open Classical in
/--
Returns `y` if it is in the image of `f`,
or an element of the image of `f` otherwise.
-/
noncomputable def fromImage (f : Nat → Nat) (y : Nat) :=
  if ∃ x, f x = y then
    y
  else
    f 0
```
The `Classical` namespace contains `Decidable` instances that are not computable. These are a common
source of noncomputable dependencies that do not explicitly appear in the source code of a
definition. In the above example, for instance, a `Decidable` instance for the proposition
`∃ x, f x = y` is synthesized using a `Classical` decidability instance; therefore, `fromImage` must
be marked `noncomputable`.
-/
register_error_explanation lean.dependsOnNoncomputable {
  summary := "Declaration depends on noncomputable definitions but is not marked as noncomputable"
  sinceVersion := "4.22.0"
}
