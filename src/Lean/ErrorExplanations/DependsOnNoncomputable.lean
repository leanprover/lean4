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
def getWitness {P : α → Prop} (h : ∃ x, P x) :
    {x : α // P x} :=
  ⟨Classical.choose h, Classical.choose_spec h⟩
```
```output
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Classical.choose', which is 'noncomputable'
```
```lean fixed
noncomputable def getWitness {P : α → Prop} (h : ∃ x, P x) :
    {x : α // P x} :=
  ⟨Classical.choose h, Classical.choose_spec h⟩
```
In this example, `getWitness` depends on the noncomputable function `Classical.choose`. Because
`Classical.choose` is necessarily noncomputable, the only way to define `getWitness` is to make it
noncomputable as well.

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
register_error_explanation Lean.DependsOnNoncomputable {
  summary := "Declaration depends on noncomputable definitions but is not marked as noncomputable"
  sinceVersion := "4.21.0"
}
