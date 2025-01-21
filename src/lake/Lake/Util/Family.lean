/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Parser.Command

/-!
# Open Type Families in Lean

This module contains utilities for defining **open type families** in Lean.

The concept of type families originated in Haskell with the paper
[*Type checking with open type functions*][1] by Schrijvers *et al.* and
is essentially just a fancy name for a function from an input *index* to an
output type. However, it tends to imply some additional restrictions on syntax
or functionality as opposed to a proper type function.The design here has some
such limitations so the name was similarly adopted.

Type families come in two forms: open and closed.
A *closed* type family is an ordinary total function.
An *open* type family, on the other hand, is a partial function that allows
additional input to output mappings to be defined as needed.

Lean does not (currently) directly support open type families.
However, it does support type class *functional dependencies* (via `outParam`),
and simple open type families can be modeled through functional dependencies,
which is what we do here.

[1]: https://doi.org/10.1145/1411204.1411215

## Defining Families

In this approach, to define an open type family, one first defines an `opaque`
type function with a single argument that serves as the key:

```lean
opaque FooFam (key : Name) : Type
```

Note that, unlike Haskell, the key need not be a type. Lean's dependent type
theory does not have Haskell's strict separation of types and data and thus
we can use data as an index as well.

Then, to add a mapping to this family, one defines an axioms:

```lean
axiom FooFam.bar : FooFam `bar = Nat
```

To finish, one also defines an instance of the `FamilyDef` type class
defined in this module using the axiom like so:

```lean
instance : FamilyDef FooFam `bar Nat := ⟨FooFam.bar⟩
```

This module provides a `family_def` macro to define both the axiom and the
instance in one go like so:

```lean
family_def bar : FooFam `bar := Nat
```

## Type Inference

The signature of the type class `FamilyDef` is

```
FamilyDef {α : Type u} (Fam : α → Type v) (a : α) (β : outParam $ Type v) : Prop
```

The key part being that `β` is an `outParam` so Lean's type class synthesis will
smartly infer the defined type `Nat` when given the key of `` `bar``. Thus, if
we have a function define like so:

```
def foo (key : α) [FamilyDef FooFam key β] : β := ...
```

Lean will smartly infer that the type of ``foo `bar`` is `Nat`.

However, filling in the right hand side of `foo` is not quite so easy.
``FooFam `bar = Nat`` is only true propositionally, so we have to manually
`cast` a `Nat` to ``FooFam `bar``and provide the proof (and the same is true
vice versa). Thus, this module provides two definitions, `toFamily : β → Fam a`
and `ofFamily : Fam a → β`, to help with this conversion.

## Full Example

Putting this all together, one can do something like the following:

```lean
opaque FooFam (key : Name) : Type

abbrev FooMap := DRBMap Name FooFam Name.quickCmp
def FooMap.insert (self : FooMap) (key : Name) [FamilyDef FooFam key α] (a : α) : FooMap :=
  DRBMap.insert self key (toFamily a)
def FooMap.find? (self : FooMap) (key : Name) [FamilyDef FooFam key α] : Option α :=
  ofFamily <$> DRBMap.find? self key

family_def bar : FooFam `bar := Nat
family_def baz : FooFam `baz := String
def foo := Id.run do
  let mut map : FooMap := {}
  map := map.insert `bar 5
  map := map.insert `baz "str"
  return map.find? `bar

#eval foo -- 5
```

## Type Safety

In order to maintain type safety, `a = b → Fam a = Fam b` must actually hold.
That is, one must not define mappings to two different types with equivalent
keys. Since mappings are defined through axioms, Lean WILL NOT catch violations
of this rule itself, so extra care must be taken when defining mappings.

In Lake, this is solved by having its open type families be indexed by a
`Lean.Name` and defining each mapping using a name literal `name` and the
declaration ``axiom Fam.name : Fam `name = α``. This causes a name clash
if two keys overlap and thereby produces an error.
-/

open Lean

namespace Lake

/-! ## API -/

/--
Defines a single mapping of the **open type family** `Fam`, namely `Fam a = β`.
See the module documentation of `Lake.Util.Family` for details on what an open
type family is in Lake.
-/
class FamilyDef {α : Type u} (Fam : α → Type v) (a : α) (β : semiOutParam $ Type v) : Prop where
  family_key_eq_type : Fam a = β

/-- Like `FamilyDef`, but `β` is an `outParam`. -/
class FamilyOut {α : Type u} (Fam : α → Type v) (a : α) (β : outParam $ Type v) : Prop where
  family_key_eq_type : Fam a = β

-- Simplifies proofs involving open type families
attribute [simp] FamilyOut.family_key_eq_type

instance [FamilyDef Fam a β] : FamilyOut Fam a β where
  family_key_eq_type := FamilyDef.family_key_eq_type

/-- The constant type family -/
instance : FamilyDef (fun _ => β) a β where
  family_key_eq_type := rfl

/-- Cast a datum from its individual type to its general family. -/
@[macro_inline] def toFamily [FamilyOut Fam a β] (b : β) : Fam a :=
  cast FamilyOut.family_key_eq_type.symm b

/-- Cast a datum from its general family to its individual type. -/
@[macro_inline] def ofFamily [FamilyOut Fam a β] (b : Fam a) : β :=
  cast FamilyOut.family_key_eq_type b

/--
The syntax:

```lean
family_def foo : Fam 0 := Nat
```

Declares a new mapping for the open type family `Fam` type via the
production of an axiom `Fam.foo : Data 0 = Nat` and an instance of `FamilyDef`
that uses this axiom for key `0`.
-/
scoped macro (name := familyDef) doc?:optional(Parser.Command.docComment)
"family_def " id:ident " : " fam:ident key:term " := " ty:term : command => do
  let tid := extractMacroScopes fam.getId |>.name
  if let (tid, _) :: _ ← Macro.resolveGlobalName tid then
    let app := Syntax.mkApp fam #[key]
    let axm := mkIdentFrom id (canonical := true) <| `_root_ ++ tid ++ id.getId
    `($[$doc?]? @[simp] axiom $axm : $app = $ty
    instance : FamilyDef $fam $key $ty := ⟨$axm⟩)
  else
    Macro.throwErrorAt fam s!"unknown family '{tid}'"
