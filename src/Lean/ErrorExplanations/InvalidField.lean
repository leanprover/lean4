/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Simmons
-/
module

prelude
public import Lean.ErrorExplanation
meta import Lean.ErrorExplanation

/--
This error indicates that an expression containing a dot followed by an identifier was encountered,
and that it wasn't possible to understand the identifier as a field.

Lean's field notation is very powerful, but this can also make it confusing: the expression
`color.value` can either be a single [identifier](lean-manual://section/identifiers-and-resolution),
it can be a reference to the [field of a structure](lean-manual://section/structure-fields), and it
and be a calling a function on the value `color` with
[generalized field notation](lean-manual://section/generalized-field-notation).

# Examples

## Incorrect Field Name

```lean broken
#eval (4 + 2).suc
```
```output
Invalid field `suc`: The environment does not contain `Nat.suc`, so it is not possible to project the field `suc` from an expression
  4 + 2
of type `Nat`
```
```lean fixed
#eval (4 + 1).succ
```

The simplest reason for an invalid field error is that the function being sought, like `Nat.suc`,
does not exist.

## Projecting from the Wrong Expression

```lean broken
#eval '>'.leftpad 10 ['a', 'b', 'c']
```
```output
Invalid field `leftpad`: The environment does not contain `Char.leftpad`, so it is not possible to project the field `leftpad` from an expression
  '>'
of type `Char`
```
```lean fixed
#eval ['a', 'b', 'c'].leftpad 10 '>'
```

The type of the expression before the dot entirely determines the function being called by the field
projection. There is no `Char.leftpad`, and the only way to invoke `List.leftpad` with generalized
field notation is to have the list come before the dot.

## Type is Not Specific

```lean broken
def double_plus_one {α} [Add α] (x : α) :=
   (x + x).succ
```
```output
Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  x + x
has type `α` which does not have the necessary form.
```
```lean fixed
def double_plus_one (x : Nat) :=
   (x + x).succ
```

The `Add` typeclass is sufficient for performing the addition `x + x`, but the `.succ` field notation
cannot operate without knowing more about the actual type from which `succ` is being projected.

## Insufficient Type Information

```lean broken
example := fun (n) => n.succ.succ
```
```output
Invalid field notation: Type of
  n
is not known; cannot resolve field `succ`
```
```lean fixed
example := fun (n : Nat) => n.succ.succ
```

Generalized field notation can only be used when it is possible to determine the type that is being
projected. Type annotations may need to be added to make generalized field notation work.

-/
register_error_explanation lean.invalidField {
  summary := "Dotted identifier notation used without ."
  sinceVersion := "4.22.0"
}
