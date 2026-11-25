module

public import DerivingTest.Instances
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

deriving instance ToData, FirstDiff, CompareCtorIdx, Bounds, Secret, ULiftCtorIdx, Const, GenRandom
  for List, Data, String.Pos.Raw, Bool, Substring.Raw, SourceInfo, Name, Syntax.Preresolved, Syntax,
    FVarId, MVarId, LevelMVarId, BinderInfo, Literal, Prod, DataValue, KVMap, Level, Expr,
    ConstantVal, AxiomVal, ReducibilityHints, DefinitionSafety, DefinitionVal, TheoremVal,
    OpaqueVal, QuotKind, QuotVal, InductiveVal, ConstructorVal, RecursorRule, RecursorVal,
    ConstantInfo, Constructor, InductiveType, Declaration, Option, IO.Error, Sigma

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

deriving instance IsSmallToData, LawfulBounds, ToDataDepLaw for
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

example (i : ConstantInfo) : Data.Small (ToData.convert i) := IsSmallToData.small i
example (i : ConstantInfo) : Bounds.upper i ≤ Bounds.maximum ConstantInfo :=
  LawfulBounds.upper_le_maximum i

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

inductive Mutual1 (α : Type) where
  | base (a : α)
  | other (x : Mutual2 α)
-- For here and later: You can't specify `Secret` here or it will complain
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, GenRandom, IsSmallToData,
  LawfulBounds, ToDataDepLaw

inductive Mutual2 (α : Type) where
  | base (a : Nat)
  | other (x : Mutual1 α)
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, GenRandom, IsSmallToData,
  LawfulBounds, ToDataDepLaw

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

-- Note: `LawfulBounds, ToDataDepLaw` works because it is non-recursive (`nonRec := true`)
deriving instance ToData, FirstDiff, CompareCtorIdx, Bounds, Secret, ULiftCtorIdx, Const, GenRandom,
    LawfulBounds
  for OtherMutual1
deriving instance ToData, FirstDiff, CompareCtorIdx, Bounds, Secret, ULiftCtorIdx, Const, GenRandom,
    LawfulBounds
  for OtherMutual2

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
The deriving handlers also work on indexed inductives
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
-- `GenRandom` specifically doesn't work with indices
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

/-!
The deriving handlers also work on complex dependent types
-/

instance : LawfulFirstDiff Bool where
  of_firstDiff_eq_none := by decide

structure SigmaField (γ : Bool → Type) where
  val : (b : Bool) × List (γ b)
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, GenRandom, IsSmallToData,
  LawfulBounds, ToDataDepLaw

/-!
The deriving handlers also work on types parameterized using structures
-/

structure Params where
  Type1 : Type
  Type2 : Type

structure TestParams (p : Params) where
  fst : p.Type1
  snd : p.Type2
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, GenRandom, IsSmallToData,
  LawfulBounds, ToDataDepLaw

/--
info: @[instance_reducible, expose] def instToDataTestParamsOfType1OfType2 : {p : Params} →
  [ToData p.Type1] → [ToData p.Type2] → ToData (TestParams p)
-/
#guard_msgs in
#print sig instToDataTestParamsOfType1OfType2

/-!
More examples for indexed inductives
-/

inductive Two : Bool → Type where
  | a : Two true
  | b (x : Two true) : Two false
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

inductive Flip : Bool → Type where
  | a : Flip true
  | b (y : Bool) (x : Flip y) : Flip false
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

/-!
Redundant instances are detected and omitted
-/

inductive TestRedundantForward (β : Bool → Type) where
  | veryGeneral (a : Bool) (x : β a)
  | verySpecific (x : β true) (y : List (β false))
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, GenRandom, IsSmallToData,
  LawfulBounds, ToDataDepLaw

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
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, GenRandom, IsSmallToData,
  LawfulBounds, ToDataDepLaw

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
... and `private`
-/

private structure TestPrivate where
  thing : Nat
deriving ToData

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

run_cmd declareWide `Wide 100

-- `IsSmallToData` fails because 400 is not small :-)
deriving instance ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, LawfulBounds,
    ToDataDepLaw
  for Wide

-- `GenRandom` seems to require a higher recursion depth
set_option maxRecDepth 0 in
deriving instance GenRandom for Wide

/--
error: Error while processing constructor Wide.mk:
  Failed to derive `IsSmallToData`, field count 100 is not smaller than 32
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
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

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
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

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
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

instance : LawfulFirstDiff (Hide n) where
  of_firstDiff_eq_none := by
    intro ⟨a⟩ ⟨b⟩
    simp [firstDiff, instFirstDiffHide.firstDiff]

structure Chain where
  n : Nat
  b : Hide n
  c : Fin b.1 -- `c` sneakily depends on `n` here but this is not obvious in the term structure
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

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
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

inductive B.T where
  | mk
deriving ToData, FirstDiff, CompareCtorIdx, Bounds, ULiftCtorIdx, Const, IsSmallToData,
  LawfulBounds, ToDataDepLaw

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
