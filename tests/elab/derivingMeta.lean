module
public meta import Lean.Elab.Deriving.Meta

@[expose] public section

/-!
Test for using the `Lean.Meta.Deriving` framework
-/

open Lean Elab Meta Deriving

inductive Data where
  | nat (n : Nat)
  | int (n : Int)
  | string (s : String)
  | array (xs : Array Data)
  | ctor (idx : Nat) (l : List Data)
deriving Inhabited, Repr

class MyClass (α : Type u) where
  convert : α → Data

instance : MyClass Nat where
  convert := .nat

instance : MyClass Int where
  convert := .int

instance : MyClass String where
  convert := .string

instance : MyClass UInt8 where
  convert x := .nat x.toNat

instance : MyClass UInt16 where
  convert x := .nat x.toNat

instance : MyClass UInt32 where
  convert x := .nat x.toNat

instance : MyClass UInt64 where
  convert x := .nat x.toNat

instance : MyClass USize where
  convert x := .nat x.toNat

instance [MyClass α] : MyClass (Array α) where
  convert x := .array <| x.map MyClass.convert

/-!
Simple example of how you can write a deriving handler using the new framework
-/

meta def handler := mkInductiveDerivingHandler ``MyClass do
  deriveTransformationInstPerConstructor fun ival cval fields _ => do
    let mut encodings : Array Expr := #[]
    for field in fields do
      let ty ← inferType field
      let some lvl ← getDecLevel? ty | continue
      let inst ← synthInstanceDeriving (.app (.const ``MyClass [lvl]) ty)
      let val := mkApp3 (.const ``MyClass.convert [lvl]) ty inst field
      encodings := encodings.push val
    if ival.ctors.length = 1 && encodings.size = 1 then
      return encodings[0]!
    let mut list : Expr := .app (.const ``List.nil [0]) (.const ``Data [])
    for e in encodings.reverse do
      list := mkApp3 (.const ``List.cons [0]) (.const ``Data []) e list
    return mkApp2 (.const ``Data.ctor []) (toExpr cval.cidx) list

/-!
The deriving handler can derive instances for inductives without trouble, including nested
inductives like `Syntax`.

We can't register the deriving handler here so we'll just use it directly.
-/

run_cmd
  handler #[``List, ``Data, ``String.Pos.Raw, ``Bool, ``Substring.Raw, ``SourceInfo, ``Name,
    ``Syntax.Preresolved, ``Syntax, ``FVarId, ``MVarId, ``LevelMVarId, ``BinderInfo, ``Literal,
    ``Prod, ``DataValue, ``KVMap, ``Level, ``Expr, ``ConstantVal, ``AxiomVal, ``ReducibilityHints,
    ``DefinitionSafety, ``DefinitionVal, ``TheoremVal, ``OpaqueVal, ``QuotKind, ``QuotVal,
    ``InductiveVal, ``ConstructorVal, ``RecursorRule, ``RecursorVal, ``ConstantInfo,
    ``Constructor, ``InductiveType, ``Declaration]

/--
info: @[instance_reducible, expose] def instMyClassDeclaration : MyClass Declaration :=
{ convert := instMyClassDeclaration.convert }
-/
#guard_msgs in
#print instMyClassDeclaration

/--
info: @[expose] def instMyClassDeclaration.convert : Declaration → Data :=
fun t =>
  Declaration.casesOn t (fun val => Data.ctor 0 [MyClass.convert val]) (fun val => Data.ctor 1 [MyClass.convert val])
    (fun val => Data.ctor 2 [MyClass.convert val]) (fun val => Data.ctor 3 [MyClass.convert val]) (Data.ctor 4 [])
    (fun defns => Data.ctor 5 [MyClass.convert defns]) fun lparams nparams types isUnsafe =>
    Data.ctor 6 [MyClass.convert lparams, MyClass.convert nparams, MyClass.convert types, MyClass.convert isUnsafe]
-/
#guard_msgs in
#print instMyClassDeclaration.convert

/-- info: Data.ctor 4 [Data.ctor 1 [Data.ctor 0 [], Data.string "u"]] -/
#guard_msgs in
#eval MyClass.convert (Level.param `u)

/-!
The deriving handler also works on mutual inductives
-/

mutual

inductive Mutual1 (α : Type) where
  | base (a : α)
  | other (x : Mutual2 α)

inductive Mutual2 (α : Type) where
  | base (a : Nat)
  | other (x : Mutual1 α)

end

run_cmd handler #[``Mutual1, ``Mutual2]

/--
info: @[instance_reducible, expose] def instMyClassMutual1 : {α : Type} → [MyClass α] → MyClass (Mutual1 α)
-/
#guard_msgs in
#print sig instMyClassMutual1

/--
info: @[instance_reducible, expose] def instMyClassMutual2 : {α : Type} → [MyClass α] → MyClass (Mutual2 α)
-/
#guard_msgs in
#print sig instMyClassMutual2

/-!
... even if you derive the instances separately
-/

mutual

inductive OtherMutual1 (α : Type) where
  | base (a : α)
  | other (x : OtherMutual2 α)

inductive OtherMutual2 (α : Type) where
  | base (a : Nat)
  | other (x : OtherMutual1 α)

end

run_cmd handler #[``OtherMutual1]
run_cmd handler #[``OtherMutual2]

/--
info: @[instance_reducible, expose] def instMyClassOtherMutual1 : {α : Type} → [MyClass α] → MyClass (OtherMutual1 α)
-/
#guard_msgs in
#print sig instMyClassOtherMutual1

/--
info: @[instance_reducible, expose] def instMyClassOtherMutual2 : {α : Type} → [MyClass α] → MyClass (OtherMutual2 α)
-/
#guard_msgs in
#print sig instMyClassOtherMutual2

/-!
... and on inductives with indices
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

run_cmd handler #[``Vec]

/-- info: Data.ctor 1 [Data.nat 0, Data.nat 1, Data.ctor 0 []] -/
#guard_msgs in
#eval MyClass.convert (Vec.cons 1 Vec.nil)

/-!
... and complex dependent types
-/

structure SigmaField (γ : Bool → Type) where
  val : (b : Bool) × List (γ b)

run_cmd handler #[``Sigma, ``SigmaField]

/-- info: Data.ctor 0 [Data.ctor 0 [], Data.ctor 1 [Data.nat 3, Data.ctor 0 []]] -/
#guard_msgs in
#eval MyClass.convert { val := ⟨false, [3]⟩ : SigmaField fun _ => Nat }

/-!
`deriving.bindersVerbatim` disables instance synthesis but still deduplicates instance hypotheses
-/

structure TestVerbatim (α : Type) where
  val : Nat
  dup : Nat
  list : List α

set_option deriving.bindersVerbatim true in
run_cmd handler #[``TestVerbatim]

/--
info: @[instance_reducible, expose] def instMyClassTestVerbatimOfNatOfList : {α : Type} →
  [MyClass Nat] → [MyClass (List α)] → MyClass (TestVerbatim α)
-/
#guard_msgs in
#print sig instMyClassTestVerbatimOfNatOfList

/-!
`deriving.reduceInstances false` only prevents splitting `MyClass (List α)` into `MyClass α`,
the `MyClass Nat` instance hypothesis is still synthesized.
-/

structure TestNoReduction (α : Type) where
  val : Nat
  dup : Nat
  list : List α

set_option deriving.reduceInstances false in
run_cmd handler #[``TestNoReduction]

/--
info: @[instance_reducible, expose] def instMyClassTestNoReductionOfList : {α : Type} →
  [MyClass (List α)] → MyClass (TestNoReduction α)
-/
#guard_msgs in
#print sig instMyClassTestNoReductionOfList

/-!
With `deriving.strict` enabled (default), we get errors for missing instances
-/

opaque Missing : Type

structure UsesMissing where
  fine : Nat
  missing : Missing

/--
error: While deriving an instance for MyClass, the following complex instance requirements were encountered that could not be synthesized:
  MyClass Missing, reason:
    No matching instances

Hint: You may be able to derive the missing instance using the syntax `deriving instance ClassName for TypeName`.

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
run_cmd handler #[``UsesMissing]

/-!
... or unsuitable instances
-/

class MyClassExtender (α : Type u) extends MyClass α

/--
error: While deriving an instance for MyClass, the following complex instance requirements were encountered that could not be synthesized:
  MyClass Missing, reason:
    The instance @MyClassExtender.toMyClass matched but did not have the right shape to be considered

Hint: You may be able to derive the missing instance using the syntax `deriving instance ClassName for TypeName`.

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
run_cmd handler #[``UsesMissing]

/-!
... or unification failures
-/

structure Any.{u} where
  α : Sort u
  val : α

instance : MyClass Any.{0} where convert _ := .nat 0

structure UsesAny1 where
  α : Any.{1}

/--
error: While deriving an instance for MyClass, the following complex instance requirements were encountered that could not be synthesized:
  MyClass Any, reason:
    Failed to unify with the conclusion of instMyClassAny

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
run_cmd handler #[``UsesAny1]

/-!
... or remaining metavariables
-/

inductive SomeType where
  | hi

abbrev Thing (_α : Type) := SomeType

instance : MyClass (Thing α) where convert _ := .nat 0

structure UsesSomeType where
  type : SomeType

/--
error: While deriving an instance for MyClass, the following complex instance requirements were encountered that could not be synthesized:
  MyClass SomeType, reason:
    After unifying with the conclusion of @instMyClassThing, the argument
      ?α
    still contained unexpected metavariables

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
run_cmd handler #[``UsesSomeType]

/-!
... or duplicate instances
-/

structure Duplicate (α : Type) where

instance [MyClass α] : MyClass (Duplicate α) where convert _ := .nat 0
instance [MyClass α] : MyClass (Duplicate α) where convert _ := .nat 1
instance (priority := low) [MyClass α] : MyClass (Duplicate α) where convert _ := .nat 2

structure UsesDuplicate (α : Type) where
  dup : Duplicate α

/--
error: While deriving an instance for MyClass, the following complex instance requirements were encountered that could not be synthesized:
  MyClass (Duplicate α), reason:
    There were multiple instance candidates: @instMyClassDuplicate, @instMyClassDuplicate_1, and @instMyClassDuplicate_2

Hint: Having multiple instance candidates usually indicates that one of the mentioned instances is redundant.
If this is intentional though, you can make the deriving handler choose an instance using `set_option deriving.chooseArbitraryInstance true`.

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
run_cmd handler #[``UsesDuplicate]

/-!
With `deriving.chooseArbitraryInstance`, the deriving handler chooses an instance, in particular,
the last one with the highest priority (similarly to instance synthesis itself).
-/

set_option deriving.chooseArbitraryInstance true in
run_cmd handler #[``UsesDuplicate]

/-- info: Data.nat 1 -/
#guard_msgs in
#eval MyClass.convert { dup := {} : UsesDuplicate Nat }

/-!
You can disable the errors using `deriving.strict false` to keep the complex hypotheses; but other
hypotheses that were successfully synthesized are not kept, like `MyClass Nat` here.
-/

set_option deriving.strict false in
run_cmd handler #[``UsesMissing]

/--
info: @[instance_reducible, expose] def instMyClassUsesMissingOfMissing : [MyClass Missing] → MyClass UsesMissing
-/
#guard_msgs in
#print sig instMyClassUsesMissingOfMissing

/-!
Even with `deriving.strict false`, missing instances for nested occurrences are still reported.
-/

structure Nestable (α : Type) where
  val : α

inductive Nested where
  | none
  | nest (x : Nestable Nested)

/--
error: Error while processing constructor Nested.nest:
  Got stuck at instance requirement for nested type while deriving an instance for MyClass:
    MyClass (Nestable Nested)
  Reason: The instance @MyClassExtender.toMyClass matched but did not have the right shape to be considered
-/
#guard_msgs in
set_option deriving.strict false in
run_cmd handler #[``Nested]

/-!
With `deriving.implicitBinders false`, the generated instances use explicit binders exactly if they
were explicit in the inductive (otherwise they are always implicit)
-/

inductive WithImplicit (α : Type) : Nat → Type where
  | thing (x : α) : WithImplicit α 0

set_option deriving.implicitBinders true in -- default
run_cmd handler #[``WithImplicit]

/--
info: @[instance_reducible, expose] def instMyClassWithImplicit : {α : Type} →
  [MyClass α] → {a : Nat} → MyClass (WithImplicit α a)
-/
#guard_msgs in
#print sig instMyClassWithImplicit

inductive WithExplicit (α : Type) : Nat → Type where
  | thing (x : α) : WithExplicit α 0

set_option deriving.implicitBinders false in
run_cmd handler #[``WithExplicit]

/--
info: @[instance_reducible, expose] def instMyClassWithExplicit : (α : Type) →
  [MyClass α] → (a : Nat) → MyClass (WithExplicit α a)
-/
#guard_msgs in
#print sig instMyClassWithExplicit

/-!
The deriving handler also handles types parameterized using structures
-/

structure Params where
  Type1 : Type
  Type2 : Type

structure TestParams (p : Params) where
  fst : p.Type1
  snd : p.Type2

run_cmd handler #[``TestParams]

/--
info: @[instance_reducible, expose] def instMyClassTestParamsOfType1OfType2 : {p : Params} →
  [MyClass p.Type1] → [MyClass p.Type2] → MyClass (TestParams p)
-/
#guard_msgs in
#print sig instMyClassTestParamsOfType1OfType2

/-!
Redundant instances are detected and omitted
-/

inductive TestRedundantForward (β : Bool → Type) where
  | veryGeneral (a : Bool) (x : β a)
  | verySpecific (x : β true) (y : List (β false))

run_cmd handler #[``TestRedundantForward]

-- would be `[∀ a, MyClass (β a)] [MyClass (β true)] [MyClass (List (β false))]`
-- without processing but with the redundancy check, we get:

/--
info: @[instance_reducible, expose] def instMyClassTestRedundantForward : {β : Bool → Type} →
  [(a : Bool) → MyClass (β a)] → MyClass (TestRedundantForward β)
-/
#guard_msgs in
#print sig instMyClassTestRedundantForward

/-!
... in both directions
-/

inductive TestRedundantBackward (β : Bool → Type) where
  | verySpecific (x : β true) (y : List (β false))
  | veryGeneral (a : Bool) (x : β a)

run_cmd handler #[``TestRedundantBackward]

-- would be `[MyClass (β true)] [MyClass (List (β false))] [∀ a, MyClass (β a)]`
-- without processing but with the redundancy check, we get:

/--
info: @[instance_reducible, expose] def instMyClassTestRedundantBackward : {β : Bool → Type} →
  [(a : Bool) → MyClass (β a)] → MyClass (TestRedundantBackward β)
-/
#guard_msgs in
#print sig instMyClassTestRedundantBackward

/-!
The deriving handler properly propagates `unsafe`
-/

unsafe instance [MyClass α] : MyClass (Squash α) where
  convert x := MyClass.convert (x.liftOn id lcProof)

structure UsesSquash where
  thing : Squash Nat

run_cmd handler #[``UsesSquash]

/-- info: @[instance_reducible, expose] unsafe def instMyClassUsesSquash : MyClass UsesSquash -/
#guard_msgs in
#print sig instMyClassUsesSquash

/-- info: Data.nat 1 -/
#guard_msgs in
#eval MyClass.convert { thing := .mk 1 : UsesSquash }

/-!
... and `private`
-/

private structure TestPrivate where
  thing : Nat

run_cmd handler #[``TestPrivate]

/-- info: @[instance_reducible] private def instMyClassTestPrivate : MyClass TestPrivate -/
#guard_msgs in
#print sig instMyClassTestPrivate

/-!
However, it will complain when used with `@[expose]` on a type with private constructors
(or a type that is mutual to one with private constructors)

Note: we are in an `@[expose] public section`
-/

mutual

inductive TestPrivateCtorMutual1 where
  | private foo (x : TestPrivateCtorMutual2)

inductive TestPrivateCtorMutual2 where
  | bar (x : TestPrivateCtorMutual1)

end

/--
error: Cannot use `deriving ... @[expose]` with `TestPrivateCtorMutual1`
(which is part of the same mutual block as `TestPrivateCtorMutual2`)
as it has one or more private constructors
-/
#guard_msgs in
run_cmd handler #[``TestPrivateCtorMutual2]

/-!
`deriveTransformationInstPerConstructor` also handles "weird" type classes containing the universe
on the right-hand side.
-/

class ToULift (α : Type u) where
  lift : α → ULift.{u} Nat

meta def toULiftHandler : DerivingHandler :=
  mkInductiveDerivingHandler ``ToULift do
    deriveTransformationInstPerConstructor fun _ _ _ _ =>
      return mkApp2 (.const ``ULift.up [(← read).indLevel.dec.get!, 0]) (mkConst ``Nat) (mkNatLit 0)

structure Flag : Type where
  on : Bool

run_cmd toULiftHandler #[``Flag]

/-!
The deriving handlers should also work reasonably quickly on large structures
-/

open Elab Command

/-- Declares `structure name where (f0 : Nat) … (f{n-1} : Nat)`. -/
meta def declareWide (name : Name) (n : Nat) : CommandElabM Unit := do
  let fields := (List.range n).toArray.map fun i => mkIdent (.mkSimple s!"f{i}")
  elabCommand <| ← `(structure $(mkIdent name):ident where $[($fields : Nat)]*)

run_cmd declareWide `Wide400 400
run_cmd handler #[``Wide400]
