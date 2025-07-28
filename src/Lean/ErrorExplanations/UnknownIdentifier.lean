/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
module

prelude
public import Lean.ErrorExplanation

/--
This error means that Lean was unable to find a variable or constant matching the given name. More
precisely, this means that the name could not be *resolved*, as described in the manual section on
[Identifiers](lean-manual://section/identifiers-and-resolution): no interpretation of the input as
the name of a local or section variable (if applicable), a previously declared global constant, or a
projection of either of the preceding was valid. ("If applicable" refers to the fact that in some
cases—e.g., the `#print` command's argument—names are resolved only to global constants.)

Note that this error message will display only one possible resolution of the identifier, but the
presence of this error indicates failures for *all* possible names to which it might refer. For
example, if the identifier `x` is entered with the namespaces `A` and `B` are open, the error
message "Unknown identifier \`x\`" indicates that none of `x`, `A.x`, or `B.x` could be found (or
that `A.x` or `B.x`, if either exists, is a protected declaration).

Common causes of this error include forgetting to import the module in which a constant is defined,
omitting a constant's namespace when that namespace is not open, or attempting to refer to a local
variable that is not in scope.

To help resolve some of these common issues, this error message is accompanied by a code action that
suggests constant names similar to the one provided. These include constants in the environment as
well as those that can be imported from other modules. Note that these suggestions are available
only through supported code editors' built-in code action mechanisms and not as a hint in the error
message itself.

# Examples

## Missing import

```lean broken
def inventory :=
  Std.HashSet.ofList [("apples", 3), ("bananas", 4)]
```
```output
Unknown constant `Std.HashSet.ofList`
```
```lean fixed
public import Std.Data.HashSet.Basic

public section

def inventory :=
  Std.HashSet.ofList [("apples", 3), ("bananas", 4)]
```
The constant `Std.HashSet.ofList` is defined in the `Std.Data.HashSet.Basic` module, which has not
been imported in the original example. This import is suggested by the unknown identifier code
action; once it is added, this example compiles.

## Variable not in scope

```lean broken
example (s : IO.FS.Stream) := do
  IO.withStdout s do
    let text := "Hello"
    IO.println text
  IO.println s!"Wrote '{text}' to stream"
```
```output
Unknown identifier `text`
```
```lean fixed
example (s : IO.FS.Stream) := do
  let text := "Hello"
  IO.withStdout s do
    IO.println text
  IO.println s!"Wrote '{text}' to stream"
```
An unknown identifier error occurs on the last line of this example because the variable `text` is
not in scope. The `let`-binding on the third line is scoped to the inner `do` block and cannot be
accessed in the outer `do` block. Moving this binding to the outer `do` block—from which it remains
in scope in the inner block as well—resolves the issue.

## Missing namespace

```lean broken
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

def red : Color :=
  rgb 255 0 0
```
```output
Unknown identifier `rgb`
```
```lean fixed (title := "Fixed (qualified name)")
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

def red : Color :=
  Color.rgb 255 0 0
```
```lean fixed (title := "Fixed (open namespace)")
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

open Color in
def red : Color :=
  rgb 255 0 0
```

In this example, the identifier `rgb` on the last line does not resolve to the `Color` constructor
of that name. This is because the constructor's name is actually `Color.rgb`: all constructors of an
inductive type have names in that type's namespace. Because the `Color` namespace is not open, the
identifier `rgb` cannot be used without its namespace prefix.

One way to resolve this error is to provide the fully qualified constructor name `Color.rgb`; the
dotted-identifier notation `.rgb` can also be used, since the expected type of `.rgb 255 0 0` is
`Color`. Alternatively, one can open the `Color` namespace and continue to omit the `Color` prefix
from the identifier.

## Protected constant name without namespace prefix

```lean broken
protected def A.x := ()

open A

example := x
```
```output
Unknown identifier `x`
```
```lean fixed (title := "Fixed (qualified name)")
protected def A.x := ()

open A

example := A.x
```
```lean fixed (title := "Fixed (restricted open)")
protected def A.x := ()

open A (x)

example := x
```

In this example, because the constant `A.x` is `protected`, it cannot be referred to by the suffix
`x` even with the namespace `A` open. Therefore, the identifier `x` fails to resolve. Instead, to
refer to a `protected` constant, it is necessary to include at least its innermost namespace—in this
case, `A`. Alternatively, the *restricted opening* syntax—demonstrated in the second corrected
example—allows a `protected` constant to be referred to by its unqualified name, without opening the
remainder of the namespace in which it occurs (see the manual section on
[Namespaces and Sections](lean-manual://section/namespaces-sections) for details).

## Unresolvable name inferred by dotted-identifier notation

```lean broken
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  .toNat (b₁ || b₂)
```
```output
Unknown identifier `Nat.toNat`

Note: Inferred this name from the expected resulting type of `.toNat`:
  Nat
```
```lean fixed (title := "Fixed (generalized field notation)")
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  (b₁ || b₂).toNat
```
```lean fixed (title := "Fixed (qualified name)")
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  Bool.toNat (b₁ || b₂)
```

In this example, the dotted-identifier notation `.toNat` causes Lean to infer an unresolvable
name (`Nat.toNat`). The namespace used by dotted-identifier notation is always inferred from
the expected type of the expression in which it occurs, which—due to the type annotation on
`disjoinToNat`—is `Nat` in this example. To use the namespace of an argument's type—as the author of
this code seemingly intended—use *generalized field notation* as shown in the first corrected
example. Alternatively, the correct namespace can be explicitly specified by writing the fully
qualified function name.
-/
register_error_explanation lean.unknownIdentifier {
  summary := "Failed to resolve identifier to variable or constant."
  sinceVersion := "4.23.0"
}
