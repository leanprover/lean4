/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Parser.Command

/-!
# Open Type Families in Lean

This module contains utilities for defining **open families** in Lean.

The concept of families originated in Haskell with the paper
[*Type checking with open type functions*][1] by Schrijvers *et al.* and
is essentially just a fancy name for a function from an input *index* to an
output type. However, the concept implies some additional restrictions on
the syntax and/or functionality versus a proper function. The design here has
similar limitations, hence the adaption of the name.

Families come in two forms: open and closed.
A *closed* family is an ordinary total function.
An *open* family is a partial function that allows
additional input to output mappings to be defined as needed.

Lean does not (currently) directly support open families.
However, it does support type class *functional dependencies* (via `outParam`),
and simple open families can be modeled through functional dependencies,
which is what we do here.

[1]: https://doi.org/10.1145/1411204.1411215

## Defining Families

In this approach, to define an open family, one first defines an `opaque`
function with a single argument that serves as the index:

```lean
opaque FooFam (idx : Name) : Type
```

Note that, unlike Haskell, the index need not be a type. Lean's dependent type
theory does not have Haskell's strict separation of types and data, enabling
this generalization.

Similarly, the output of a family need not be a type. In such a case, though,
the family must be marked `noncomputable`:

```lean
noncomputable opaque fooFam (idx : Name) : Name
```

To add a mapping to a family, one first defines an axiom:

```lean
axiom FooFam.bar : FooFam `bar = Nat
```

Then defines an instance of the `FamilyDef` type class using the axiom:

```lean
instance : FamilyDef FooFam `bar Nat := ⟨FooFam.bar⟩
```

This module also provides a `family_def` macro to define both the axiom
and the instance in one go:

```lean
family_def bar : FooFam `bar := Nat
```

## Type Inference

The signature of the type class `FamilyDef` is

```
FamilyDef {α : Type u} (Fam : α → Type v) (a : α) (β : outParam $ Type v) : Prop
```

The index part being that `β` is an `outParam` so Lean's type class synthesis
will smartly infer the defined type `Nat` when given the index of `` `bar``.
Thus, if we have a function define like so:

```
def foo (idx : α) [FamilyDef FooFam idx β] : β := ...
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
opaque FooFam (idx : Name) : Type

abbrev FooMap := DRBMap Name FooFam Name.quickCmp
def FooMap.insert (self : FooMap) (idx : Name) [FamilyOut FooFam idx α] (a : α) : FooMap :=
  DRBMap.insert self idx (toFamily a)
def FooMap.find? (self : FooMap) (idx : Name) [FamilyOut FooFam idx α] : Option α :=
  ofFamily <$> DRBMap.find? self idx

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
indices. Since mappings are defined through axioms, Lean WILL NOT catch
violations of this rule itself, so extra care must be taken when defining
mappings.

In Lake, this is solved by having its open type families be indexed by a
`Lean.Name` and defining each mapping using a name literal `name` and the
declaration ``axiom Fam.name : Fam `name = α``. This causes a name clash
if two indices overlap and thereby produces an error.
-/

namespace Lake

/-! ## API -/

/--
Defines a single mapping of the **open family** `f`, namely `f a = b`.
See the module documentation of `Lake.Util.Family` for details on what an open
family is in Lake.
-/
class FamilyDef {α : Type u} {β : Type v} (f : α → β) (a : α) (b : semiOutParam β) : Prop where
  fam_eq : f a = b

@[deprecated fam_eq (since := "2025-02-22")] abbrev FamilyDef.family_key_eq_type := @FamilyDef.fam_eq

/-- Like `FamilyDef`, but `b` is an `outParam`. -/
class FamilyOut {α : Type u} {β : Type v} (f : α → β) (a : α) (b : outParam β) : Prop where
  fam_eq : f a = b

@[deprecated fam_eq (since := "2025-02-22")] abbrev FamilyOut.family_key_eq_type := @FamilyOut.fam_eq

-- Simplifies proofs involving open type families
attribute [simp] FamilyOut.fam_eq

instance [FamilyDef f a b] : FamilyOut f a b where
  fam_eq := FamilyDef.fam_eq

/-- The identity relation. -/
@[default_instance 0] instance (priority := 0) : FamilyDef f a (f a) where
  fam_eq := rfl

/-- The constant type family. -/
instance : FamilyDef (fun _ => b) a b where
  fam_eq := rfl

/-- Cast a datum from its specific type to a general type family. -/
@[macro_inline] def toFamily [FamilyOut F a β] (b : β) : F a :=
  cast FamilyOut.fam_eq.symm b

/-- Cast a datum from a general type family to its specific type. -/
@[macro_inline] def ofFamily [FamilyOut F a β] (b : F a) : β :=
  cast FamilyOut.fam_eq b

open Lean in
/--
The syntax:

```lean
family_def foo : Fam 0 := Nat
```

Declares a new mapping for the open family `Fam` via the production
of an axiom `Fam.foo : Fam 0 = Nat` and an instance of `FamilyDef`
that uses this axiom for the index `0`.
-/
scoped macro (name := familyDef)
  doc?:optional(Lean.Parser.Command.docComment)
  "family_def " id:ident " : " fam:ident idx:term " := " val:term
: command => do
  let tid := extractMacroScopes fam.getId |>.name
  if let (tid, _) :: _ ← Macro.resolveGlobalName tid then
    let app := Syntax.mkApp fam #[idx]
    let axm := mkIdentFrom id (canonical := true) <| `_root_ ++ tid ++ id.getId
    `($[$doc?]? @[simp] axiom $axm : $app = $val
    instance : FamilyDef $fam $idx $val := ⟨$axm⟩)
  else
    Macro.throwErrorAt fam s!"unknown family '{tid}'"
