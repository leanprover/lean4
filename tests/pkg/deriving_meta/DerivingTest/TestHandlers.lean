module

public import DerivingTest.Instances
meta import DerivingTest.Instances -- for the `#eval` tests
public import Lean.Declaration
import all DerivingTest.Handlers -- for the `Secret` type class

public section

/-!
# Tests for the deriving handlers declared in `DerivingTest.Handlers`
-/

open Lean

/-!
The deriving handlers can derive instances for inductives without trouble, including nested
inductives like `Syntax`.
-/

deriving instance AllGeneralClasses, OtherDataClasses for
  List, Data, String.Pos.Raw, Bool, Substring.Raw, SourceInfo, Name, Syntax.Preresolved, Syntax,
  FVarId, MVarId, LevelMVarId, BinderInfo, Literal, Prod, DataValue, KVMap, Level, Expr,
  ConstantVal, AxiomVal, ReducibilityHints, DefinitionSafety, DefinitionVal, TheoremVal, OpaqueVal,
  QuotKind, QuotVal, InductiveVal, ConstructorVal, RecursorRule, RecursorVal, ConstantInfo,
  Constructor, InductiveType, Declaration, Option, IO.Error, Sigma

/-!
... including the law type classes; although we have to exclude `Data` and `Syntax` because they
are nested and would fail
-/

-- can be derived even though the `ToData` instances were handwritten
deriving instance IsSmallToData for Nat, Int, String, UInt8, UInt16, UInt32, UInt64, USize, Fin

-- can't do much against this right now because `Syntax` is a nested inductive
-- and its instance is partial
set_option warn.sorry false in
instance : IsSmallToData Syntax := sorry

set_option warn.sorry false in
instance : IsInvolution Syntax := sorry

set_option warn.sorry false in
instance : LawfulFlatten Syntax := sorry

deriving instance OtherLawClasses for
  List, String.Pos.Raw, Bool, Substring.Raw, SourceInfo, Name, Syntax.Preresolved, FVarId, MVarId,
  LevelMVarId, BinderInfo, Literal, Prod, DataValue, KVMap, Level, Expr, ConstantVal, AxiomVal,
  ReducibilityHints, DefinitionSafety, DefinitionVal, TheoremVal, OpaqueVal, QuotKind, QuotVal,
  InductiveVal, ConstructorVal, RecursorRule, RecursorVal, ConstantInfo, Constructor, InductiveType,
  Declaration, Option, IO.Error, Sigma

/-!
Basic tests: the instances work properly
-/

/-- info: Data.ctor 4 [Data.ctor 1 [Data.ctor 0 [], Data.string "u"]] -/
#guard_msgs in
#eval ToData.convert (Level.param `u)

/--
info: some (DiffPath.ctor `Lean.Level.param 0 (DiffPath.ctor `Lean.Name.str 1 (DiffPath.differentValue)))
-/
#guard_msgs in
#eval firstDiff (Level.param `u) (Level.param `v)

-- reduction works too and yields the same result
/--
info: some (DiffPath.ctor `Lean.Level.param 0 (DiffPath.ctor `Lean.Name.str 1 DiffPath.differentValue))
-/
#guard_msgs in
#reduce firstDiff (Level.param `u) (Level.param `v)

/-- info: 6 -/
#guard_msgs in
#eval Bounds.lower (Expr.app default default)

/-- info: 8 -/
#guard_msgs in
#eval Bounds.upper (Expr.app default default)

/-- info: 27 -/
#guard_msgs in
#eval Bounds.maximum Expr

/-- info: `Prod -/
#guard_msgs in
#eval Secret.secret (Nat × Nat)

/-- info: ULift.up 1 -/
#guard_msgs in
#eval ULiftCtorIdx.idx [1]

/-- info: 6 -/
#guard_msgs in
#eval Const.const (3, 5)

/--
info: Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `taNfO.taNfo [Lean.Level.zero]) (Lean.Expr.const `taN []))
    (Lean.Expr.lit (Lean.Literal.natVal 1)))
  (Lean.Expr.app (Lean.Expr.const `taNtaNfOtsni []) (Lean.Expr.lit (Lean.Literal.natVal 1)))
-/
#guard_msgs in
#eval Transform.transform (toExpr 0)

/-- info: Lean.Expr.proj (Lean.Name.mkNum `«» 4) 0 (Lean.Expr.bvar 1) -/
#guard_msgs in
#eval show IO Expr from do
  IO.setRandSeed 523 -- make it deterministic
  repeat
    try
      let res ← GenRandom.random Expr
      return res
    catch _ =>
      pure ()

/-- info: Literal.natVal 0 -/
#guard_msgs in
#eval (Default.default : Literal)

/-- info: true -/
#guard_msgs in
#eval A.Similar.something (DataValue.ofString "hi")

/-- info: false -/
#guard_msgs in
#eval B.Similar.something (DataValue.ofString "hi")

/-- info: 407 -/
#guard_msgs in
#eval ActualClass.thing 100 "hi" (α := (Level, `foo)) (.param `u)

/-- info: [9, 1, 2, 104, 105] -/
#guard_msgs in
#eval Flatten.flatten (toExpr "hi") []

example (i : ConstantInfo) : Data.Small (ToData.convert i) := IsSmallToData.small i
example (i : ConstantInfo) : Bounds.upper i ≤ Bounds.maximum ConstantInfo :=
  LawfulBounds.upper_le_maximum i
example (i : ConstantInfo) : Transform.transform (Transform.transform i) = i :=
  IsInvolution.transform_transform i
example (i : ConstantInfo) : Flatten.flatten i l = Flatten.flatten i [] ++ l :=
  LawfulFlatten.flatten_append i [] l

/-!
The instances for the private type class is private
-/

/--
info: @[instance_reducible] private def instSecretBool : Secret Bool :=
{ secret := `Bool }
-/
#guard_msgs in
#print instSecretBool

/-!
The helpers for the law type classes are theorems
-/

/--
info: theorem instIsSmallToDataList.small.{u} : ∀ (α : Type u) [x : ToData α] [IsSmallToData α] (x_2 : List α),
  (ToData.convert x_2).Small
-/
#guard_msgs in
#print sig instIsSmallToDataList.small

/-!
The deriving handlers also work on mutual inductives
-/

mutual

inductive Mutual1 (α β : Type) where
  | base (a : α)
  | other (x : Mutual2 α β)
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

inductive Mutual2 (α β : Type) where
  | base (a : Nat) (b : β)
  | other (x : Mutual1 α β)
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

end

/-!
... even if the instances are derived separately for each inductive; at least for the non-law type
classes. The (recursive) law type classes instead fail.
-/

mutual

inductive OtherMutual1 (α : Type) where
  | base (a : α)
  | other (x : OtherMutual2 α)

inductive OtherMutual2 (α : Type) where
  | base (a : Nat)
  | other (x : OtherMutual1 α)

end

deriving instance AllGeneralClasses for OtherMutual1
deriving instance AllGeneralClasses for OtherMutual2

/--
error: Could not find helper declaration `instToDataOtherMutual2.convert` inside an instance.
This usually means that the instances were derived individually instead of all in a single
`deriving instance` command. If you can, use `deriving ...` directly at the declaration of
`OtherMutual1` instead of using `deriving instance ... for ...`.
Otherwise, join all `deriving instance ... for ...` into a single one by specifying the instances
in a comma-separated list
-/
#guard_msgs in
deriving instance IsSmallToData for OtherMutual1

/-!
For the non-recursive type classes (`nonRec := true`), here `Default`, the instance requirements
only come from each inductive individually, not both
-/

-- Note that there is no `[Default β]` here which `Default` on `Mutual2` needs
/--
info: @[instance_reducible, expose] def instDefaultMutual1 : {α β : Type} → [Default α] → Default (Mutual1 α β)
-/
#guard_msgs in
#print sig instDefaultMutual1

/--
info: @[instance_reducible, expose] def instDefaultMutual2 : {α β : Type} → [Default β] → Default (Mutual2 α β)
-/
#guard_msgs in
#print sig instDefaultMutual2

/-!
All helpers from `A.Similar` and `B.Similar` are distinct
-/

#eval do
  -- check that all these exist using double backticks
  -- each call generates instances for every inductive
  -- because we (intentionally) set `nonRec := false`
  let := [
    -- helpers for `A.Similar (OtherMutual1 α)`
    ``instSimilarOtherMutual1.something,
    ``instSimilarOtherMutual2.something,
    ``instSimilarOtherMutual1,

    -- helpers for `B.Similar (OtherMutual1 α)`
    ``instSimilarOtherMutual1_1.something,
    ``instSimilarOtherMutual2.something_1,
    ``instSimilarOtherMutual1_1,

    -- helpers for `A.Similar (OtherMutual2 α)`
    ``instSimilarOtherMutual1_2.something,
    ``instSimilarOtherMutual2.something_2,
    ``instSimilarOtherMutual2,

    -- helpers for `B.Similar (OtherMutual2 α)`
    ``instSimilarOtherMutual1_2.something_1,
    ``instSimilarOtherMutual2_1.something,
    ``instSimilarOtherMutual2_1
  ]
  assert! this.Nodup

/-!
The deriving handlers also work on indexed inductives
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
deriving AllGeneralClasses, OtherLawClasses

instance : LawfulFirstDiff Bool where
  of_firstDiff_eq_none := by decide

inductive Two : Bool → Type where
  | a : Two true
  | b (x : Two true) : Two false
deriving AllGeneralClasses, OtherLawClasses

inductive Flip : Bool → Type where
  | a : Flip true
  | b (y : Bool) (x : Flip y) : Flip false
deriving AllGeneralClasses, OtherLawClasses

/-!
The deriving handlers also work on complex dependent types
-/

structure SigmaField (γ : Bool → Type) where
  val : (b : Bool) × List (γ b)
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

/-!
The deriving handlers also work on types parameterized using structures
-/

structure Params where
  Type1 : Type
  Type2 : Type

structure TestParams (p : Params) where
  fst : p.Type1
  snd : p.Type2
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

/--
info: @[instance_reducible, expose] def instToDataTestParamsOfType1OfType2 : {p : Params} →
  [ToData p.Type1] → [ToData p.Type2] → ToData (TestParams p)
-/
#guard_msgs in
#print sig instToDataTestParamsOfType1OfType2

/-!
More complex parameterization
-/

structure InnerParams where
  Type1 : Type
  Type2 : Nat → Type

structure OuterParams extends InnerParams where
  Other : Nat → InnerParams

structure TestMoreParams (p : OuterParams) (β : Nat → Type) where
  val1 : p.Type1
  val2 : p.Type2 3
  val3 : (p.Other 20).Type2 4
  val4 : β 3
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

/-!
The deriving handlers also work on reflexive inductives
-/

instance [ToData α] : ToData (Bool → α) where
  convert f := ToData.convert (f false, f true)

instance [FirstDiff α] : FirstDiff (Bool → α) where
  firstDiff a b := FirstDiff.firstDiff (a false, a true) (b false, b true)

instance {α β : Type _} [Transform α] : Transform (β → α) where
  transform f := fun x => Transform.transform (f x)

instance [GenRandom α] : GenRandom (Bool → α) where
  random := do
    let a ← GenRandom.random α
    let b ← GenRandom.random α
    return fun
      | false => a
      | true => b

instance [Flatten α] : Flatten (Bool → α) where
  flatten f := Flatten.flatten (f false, f true)

inductive ReflexiveTest where
  | base
  | branch (f : Bool → ReflexiveTest)
deriving AllGeneralClasses, OtherDataClasses

/-!
The deriving handlers also work on types with complex levels
-/

structure Test (α : Type u) (β : Type v) : Type (imax u v) where
  val : β
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

/-!
Redundant instances are detected and omitted
-/

inductive TestRedundantForward (β : Bool → Type) where
  | veryGeneral (a : Bool) (x : β a)
  | verySpecific (x : β true) (y : List (β false))
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

-- would be `[∀ a, ToData (β a)] [ToData (β true)] [ToData (List (β false))]`
-- without processing but with the redundancy check, we get:

/--
info: @[instance_reducible, expose] def instToDataTestRedundantForward : {β : Bool → Type} →
  [(a : Bool) → ToData (β a)] → ToData (TestRedundantForward β)
-/
#guard_msgs in
#print sig instToDataTestRedundantForward

/-!
... in both directions
-/

inductive TestRedundantBackward (β : Bool → Type) where
  | verySpecific (x : β true) (y : List (β false))
  | veryGeneral (a : Bool) (x : β a)
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

-- would be `[ToData (β true)] [ToData (List (β false))] [∀ a, ToData (β a)]`
-- without processing but with the redundancy check, we get:

/--
info: @[instance_reducible, expose] def instToDataTestRedundantBackward : {β : Bool → Type} →
  [(a : Bool) → ToData (β a)] → ToData (TestRedundantBackward β)
-/
#guard_msgs in
#print sig instToDataTestRedundantBackward

/-!
The redundancy check doesn't get confused by instance cycles
-/

class CA (α : Type) where
  a : α → Data

class CB (α : Type) where
  b : α → Data

class CC (α : Type) where
  c : α → Data

instance [CB α] : CA α := ⟨CB.b⟩
instance [CC α] : CB α := ⟨CC.c⟩
instance [CA α] : CC α := ⟨CA.a⟩

structure Box (α : Type) where
  val : α

instance [CA α] [CB α] [CC α] : ToData (Box α) := ⟨fun b => CA.a b.val⟩

structure Wrapper (α : Type) where
  box : Box α
deriving ToData

/--
info: @[instance_reducible, expose] def instToDataWrapperOfCA : {α : Type} → [CA α] → ToData (Wrapper α)
-/
#guard_msgs in
#print sig instToDataWrapperOfCA

/-!
If needed, the instance requirements are reordered
-/

class Strong (α : Type) where
  [firstDiff : FirstDiff α]

instance (priority := low) [Strong α] : FirstDiff α := Strong.firstDiff

structure DepBox (α : Type) (x : α) where
  val : α

instance [Strong α] : FirstDiff (DepBox α x) where
  firstDiff a b := Strong.firstDiff.firstDiff a.val b.val

structure Pair (α : Type) where
  fst : α
  snd : DepBox α fst
deriving FirstDiff

/-
The `Strong α` comes from the `DepBox` requirement, which is generated after `FirstDiff α` and
`LawfulFirstDiff α`. But using the instance `Strong α → FirstDiff α` instance, the `FirstDiff α`
instance becomes redundant (and now depends on the later binder `Strong α`!).

This forces us to put `LawfulFirstDiff α` (which depends on `FirstDiff α`) after `Strong α`.
-/

/--
info: @[instance_reducible, expose] def instFirstDiffPairOfLawfulFirstDiff : {α : Type} →
  [x : Strong α] → [LawfulFirstDiff α] → FirstDiff (Pair α)
-/
#guard_msgs in
#print sig instFirstDiffPairOfLawfulFirstDiff

/-!
The deriving handler properly propagates `unsafe`
-/

unsafe instance [ToData α] : ToData (Squash α) where
  convert x := ToData.convert (x.liftOn id lcProof)

structure UsesSquash where
  thing : Squash Nat
deriving ToData

/-- info: @[instance_reducible, expose] unsafe def instToDataUsesSquash : ToData UsesSquash -/
#guard_msgs in
#print sig instToDataUsesSquash

/-- info: Data.nat 1 -/
#guard_msgs in
#eval ToData.convert { thing := .mk 1 : UsesSquash }

/-!
Even if the `unsafe` only gets introduced in the backward redundancy check
-/

-- keep `[ToData (Squash α)]` until the redundancy check
set_option deriving.reduceInstances false in
structure UsesSquash' (α : Type) where
  thing : Squash α
  other : α
deriving ToData

/-!
The deriving handler also properly propagates `private`
-/

private structure TestPrivate where
  thing : Nat
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

/-- info: @[instance_reducible] private def instToDataTestPrivate : ToData TestPrivate -/
#guard_msgs in
#print sig instToDataTestPrivate

/-!
However, it will complain when used with `@[expose]` on a type with private constructors
(or a type that is mutual to one with private constructors)
-/

/--
error: Cannot use `deriving ... @[expose]` with `TestPrivateCtorMutual1`
(which is part of the same mutual block as `TestPrivateCtorMutual2`)
as it has one or more private constructors
-/
#guard_msgs in
mutual

inductive TestPrivateCtorMutual1 where
  | private foo (x : TestPrivateCtorMutual2)

inductive TestPrivateCtorMutual2 where
  | bar (x : TestPrivateCtorMutual1)
deriving @[expose] ToData

end

/-!
The deriving handlers should also work reasonably quickly on large structures
-/

open Elab Command

/-- Declares `structure name where (f0 : Nat) … (f{n-1} : Nat)`. -/
meta def declareWide (name : Name) (n : Nat) : CommandElabM Unit := do
  let fields := (List.range n).toArray.map fun i => mkIdent (.mkSimple s!"f{i}")
  elabCommand <| ← `(structure $(mkIdent name):ident where $[($fields : Nat)]*)

run_cmd declareWide `Wide 200

-- `IsSmallToData` fails because 200 is not small :-)
deriving instance AllGeneralClasses, OtherDataClasses, ToDataDepLaw for Wide

/--
error: Error while processing constructor Wide.mk:
  Failed to derive `IsSmallToData`, field count 200 is not smaller than 32
-/
#guard_msgs in
deriving instance IsSmallToData for Wide

/-!
Tricky dependent inductives for the `.doubleCases` case (here `FirstDiff`)
-/

open Meta

set_option inductive.autoPromoteIndices false in
inductive Term : Nat → Type where
  | var (n : Nat) (i : Fin n) : Term n
  | app (n : Nat) (f : Term n) (x : Term n) : Term n
deriving AllGeneralClasses, OtherLawClasses

/--
We use `Eq.ndrec` calls to eliminate forward dependencies in the deriving handler, detect them here.
-/
meta def findEqNDRecs (nm : Name) : MetaM Unit := do
  let some eqn ← getUnfoldEqnFor? nm (nonRec := true)
    | failure
  let e := (← getConstVal eqn).type
  discard <| Meta.transform e (skipConstInApp := true) fun e => do
    unless e.isAppOf ``Eq.ndrec do
      return .continue
    let args := e.getAppArgs
    if args.size < 6 then
      return .continue
    logInfo m!"lhs = {args[1]!}, rhs = {args[4]!}, overArgs = {args.drop 6}"
    return .continue

-- There is just one `Eq.ndrec` call per branch and it is applied to `i` / `f` and `x`.
-- i.e. `i`, `f`, `n` transitively depend on `n` and there are no other dependencies
/--
info: lhs = n✝, rhs = n, overArgs = [i]
---
info: lhs = n✝, rhs = n, overArgs = [f, x]
-/
#guard_msgs in
#eval findEqNDRecs ``instFirstDiffTerm.firstDiff

structure ThreeFins where
  n : Nat
  a : Fin n
  b : Fin n
  c : Fin n
-- `ThreeFins` is not inhabited with `n = 0` so `Default` doesn't work
deriving AllGeneralClasses, GenRandom, OtherLawClasses

-- There is just one `Eq.ndrec` call and it is applied to `a`, `b` and `c`
-- i.e. `a`, `b`, `c` transitively depend on `n` and there are no other dependencies
/-- info: lhs = n✝, rhs = n, overArgs = [a, b, c] -/
#guard_msgs in
#eval findEqNDRecs ``instFirstDiffThreeFins.firstDiff

/-!
It's important to make dependencies transitive because dependencies can "hide"
-/

inductive Hide (n : Nat) where
  | mk (val : Nat)
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

instance : LawfulFirstDiff (Hide n) where
  of_firstDiff_eq_none := by
    intro ⟨a⟩ ⟨b⟩
    simp [firstDiff, instFirstDiffHide.firstDiff]

structure Chain where
  n : Nat
  b : Hide n
  c : Fin b.1 -- `c` sneakily depends on `n` here but this is not obvious in the term structure
-- like above, `Fin _` is preventing `Default` from working
deriving AllGeneralClasses, GenRandom, OtherLawClasses

-- i.e. `b` and `c` depend on `n`; `c` depends on `b`
/--
info: lhs = n✝, rhs = n, overArgs = [b, c]
---
info: lhs = b✝¹, rhs = b, overArgs = [c]
-/
#guard_msgs in
#eval findEqNDRecs ``instFirstDiffChain.firstDiff

/-!
We avoid repeating the same name even if we are deriving the instances at the same time
-/

mutual

inductive A.T where
  | mk
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

inductive B.T where
  | mk
deriving AllGeneralClasses, OtherDataClasses, OtherLawClasses

end

/-- info: @[instance_reducible, expose] def instToDataT : ToData A.T -/
#guard_msgs in
#print sig instToDataT

/-- info: @[instance_reducible, expose] def instToDataT_1 : ToData B.T -/
#guard_msgs in
#print sig instToDataT_1

/-!
We don't use disabled instances
-/

structure InstanceDisabled (α : Type) where
  val : α

instance disableMe [ToData α] : ToData (InstanceDisabled α) where
  convert x := ToData.convert x.val

attribute [-instance] disableMe

/--
error: While deriving an instance for ToData, the following complex instance requirements were encountered that could not be synthesized:
  ToData (InstanceDisabled α), reason:
    No matching instances

Hint: You may be able to derive the missing instance using the syntax `deriving instance ClassName for TypeName`.

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
structure WrapInstanceDisabled (α : Type) where
  thing : InstanceDisabled α
deriving ToData

/-!
... or private instances (with `@[expose]`)
-/

structure InstancePrivate (α : Type) where
  val : α

private instance [ToData α] : ToData (InstancePrivate α) where
  convert x := ToData.convert x.val

/--
error: While deriving an instance for ToData, the following complex instance requirements were encountered that could not be synthesized:
  ToData (InstancePrivate α), reason:
    No matching instances

Hint: You may be able to derive the missing instance using the syntax `deriving instance ClassName for TypeName`.

Hint: If you want to keep these hypotheses as-is, you can disable this error using `set_option deriving.strict false`
-/
#guard_msgs in
structure WrapInstancePrivate (α : Type) where
  thing : InstancePrivate α
deriving @[expose] ToData

/-!
Test for `mkFreshRevertedMVarAt` (which is a function frequently used by the framework) in the
presence of let declaration.
-/

run_meta
  let lctx ← getLCtx
  let linsts ← getLocalInstances
  withLetDecl `m (mkConst ``Nat) (mkNatLit 0) (nondep := false) fun m => do
    let eq ← mkEq m m
    let e ← mkFreshRevertedMVarAt lctx linsts eq
    guard (← isDefEq (← inferType e) eq)
    check e
  withLetDecl `m (mkConst ``Nat) (mkNatLit 0) (nondep := true) fun m => do
    let eq ← mkEq m m
    let e ← mkFreshRevertedMVarAt lctx linsts eq
    guard (← isDefEq (← inferType e) eq)
    check e
