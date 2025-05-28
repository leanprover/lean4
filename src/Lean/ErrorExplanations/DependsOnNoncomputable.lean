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

## Necessarily noncomputable function not appropriately tagged

```lean broken
def inhabitant [Inhabited α] : α :=
  Classical.choice inferInstance
```
```output
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Classical.choice', and it does not have executable code
```
```lean fixed
noncomputable def inhabitant [Inhabited α] : α :=
  Classical.choice inferInstance
```
In this example, `inhabitant` depends on the noncomputable function `Classical.choice`. Because
`Classical.choice` is necessarily noncomputable, the only way to define `inhabitant` is to make it
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
```lean fixed
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
-/
register_error_explanation Lean.DependsOnNoncomputable {
  summary := "Declaration depends on noncomputable definitions but is not marked as noncomputable"
  sinceVersion := "4.21.0"
}
