/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Simmons
-/
module

prelude
public import Lean.ErrorExplanation
meta import Lean.ErrorExplanation

public section

/--
[Type classes](lean-manual://section/type-class) are the mechanism that Lean and many other
programming languages use to handle overloaded operations. When Lean encounters an expression
`x + y`, where `x` and `y` both have type `Int`, it needs to look up how it should add two
integers and also look up what the resulting type will be. Lean describes this as a process of
_synthesizing an instance_ of the type class `HAdd Int Int t` for some type `t`. When Lean concludes
that it is not possible to synthesize a certain type class instance, it reports a failure.

It's possible to [inspect Lean's instance synthesis](lean-manual://section/instance-search), and
this can be helpful for diagnosing tricky type class resolution failures.

Many simple type class resolution errors are the result of using the wrong binary operation.

# Examples

## Using the Wrong Binary Operation

```lean broken
#eval "A" + "3"
```
```output
failed to synthesize instance of type class
  HAdd String String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```lean fixed
#eval "A" ++ "3"
```

The binary operation `+` is associated with the `HAdd` type class, and there's no way to add two
strings. The binary operation `++`, associated with the `HAppend` type class, is the correct way to
append strings.

## Modifying the Type of an Argument

```lean broken
def x : Int := 3
#eval x ++ "meters"
```
```output
failed to synthesize instance of type class
  HAppend Int String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```lean fixed
def x : Int := 3
#eval ToString.toString x ++ "meters"
```

Lean does not allow integers and strings to be added directly. The function `ToString.toString` uses
type class overloading to convert values to strings; by successfully searching for an instance of
`ToString Int`, the second example will succeed.
-/
register_error_explanation lean.failedToSynthesizeTypeclassInstance {
  summary := "Failed to synthesize instance of type class"
  sinceVersion := "4.26.0"
}
