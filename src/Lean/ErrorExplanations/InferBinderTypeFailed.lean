prelude
import Lean.ErrorExplanation

/--
This error occurs when the type of a binder in a declaration or local binding is not fully
specified and cannot be inferred by Lean. Generally, this can be resolved by providing more
information to help Lean determine the type of the binder, either by explicitly annotating its type
or by providing additional type information at sites where it is used.

Note that if an explicit resulting type is specified—even if it contains holes—Lean will not use
information from the definition body to infer parameter types. Thus, it may be necessary to
explicitly annotate the types of variables whose types are otherwise inferable—and whose inferred
types may even be correctly displayed in the Infoview—without the resulting-type annotation. In
`theorem` declarations, the definition body is never used to infer the types of binders, so any
binders whose types cannot be inferred from the resulting type of the theorem must include a type
annotation.

This error may also arise when identifiers that were intended to be definition names are
inadvertently written in binder position instead. In these cases, the excess identifiers are instead
elaborated as binders with unspecified type. This frequently occurs when attempting to define
multiple constants of the same type at the same time using a syntactic construction that does not
support this. Situations where this may happen include:
* Attempting to name an example by writing an identifier after the `example` keyword;
* Attempting to define multiple constants with the same type and (if applicable) value by listing
  them sequentially after `def`, `opaque`, or another declaration keyword;
* Attempting to define multiple fields of a structure of the same type by sequentially listing their
  names on the same line of a structure declaration; and
* Omitting vertical bars between inductive constructor names.

The first three cases are demonstrated in examples below.

# Examples

## Binder type requires new type variable

```lean broken
def identity x :=
  x
```
```output
failed to infer binder type
```
```lean fixed
def identity (x : α) :=
  x
```

Unlike some other programming languages, Lean will not automatically generate fresh type variables
to replace metavariables arising during type inference. Instead, the type `α` of `x` must be
specified. Note that if automatic implicit parameter insertion is enabled (as it is by default), the
binder for `α` itself need not be provided; Lean will insert an implicit binder for this parameter
automatically.

## Uninferred binder type due to resulting type annotation

```lean broken
def plusTwo x : Nat :=
  x + 2
```
```output
failed to infer binder type
when the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
```
```lean fixed
def plusTwo (x : Nat) : Nat :=
  x + 2
```

Even though `x` is inferred to have type `Nat` in the body of `plusTwo`, this information is not
available when elaborating the type of the definition because the resulting type `Nat` has been
explicitly specified. Using only the information in the header, the type of `x` cannot be
determined, resulting in the shown error.


## Attempting to name an example declaration
```lean broken
example trivial_proof : True :=
  trivial
```
```output
failed to infer binder type
when the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
```
```lean fixed
example : True :=
  trivial
```
Examples cannot be named, and an identifier written where a name would appear in other declaration
forms is instead elaborated as a binder, whose type cannot be inferred. If a declaration must be
named, it should be defined using a declaration form that support naming, such as  `def` or
`theorem`.

## Attempting to define multiple constants in one declaration

```lean broken
opaque m n : Nat
```
```output
failed to infer binder type
recall that you cannot declare multiple constants in a single declaration. The identifier(s) `n` are being interpreted as parameters `(n : _)`
```
```lean fixed
opaque m : Nat
opaque n : Nat
```

A constant declaration defines only one constant: it is not possible to list identifiers after
`opaque` or `def` to define them all to have the same type (and, in the latter case, value). Such a
declaration is instead elaborated as defining a single constant with parameters given by the
subsequent identifiers, whose types are unspecified and cannot be inferred. The only way to define
multiple global constants using these constructs is to declare each separately.

## Attempting to define multiple structure fields on the same line

```lean broken
structure Person where
  givenName familyName : String
  age : Nat
```
```output
failed to infer binder type
```
```lean fixed (title := "Fixed (separate lines)")
structure Person where
  givenName : String
  familyName : String
  age : Nat
```
```lean fixed (title := "Fixed (parenthesized)")
structure Person where
  (givenName familyName : String)
  age : Nat
```

If multiple identifiers are listed on the same line of a structure declaration without enclosing
parentheses, the first is taken to be the name of the field and all subsequent ones are elaborated
as binders. To prevent this behavior, either list each field on a separate line, or enclose the line
specifying multiple field names in parentheses.
-/
register_error_explanation Lean.ErrorExplanation {
  summary := "The type of a binder could not be inferred."
  sinceVersion := "4.21.0"
}
