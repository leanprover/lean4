/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.SynthInstance
import Init.Grind.Ring
import Init.Grind.Ordered.Ring
import Init.GrindInstances
import Init.Grind.Ordered.Int
import Init.Data.Int.Package
public section
namespace Lean.Meta.Sym
/--
Some modules in grind use builtin instances defined directly in core (e.g., `lia`),
while others synthesize them using `synthInstance` (e.g., `ring`).
This inconsistency is problematic, as it may introduce mismatches and result in
two different representations for the same term.

The following table is used to bypass synthInstance for the builtin cases.

Every builtin instance must be a fixpoint of `canon`. A builtin instance may be visited as a
plain term, for example as a ground pattern argument of an E-matching theorem, and its
instance-implicit arguments are then re-synthesized one by one. The table therefore also
covers the component classes (e.g., `Pow Int Nat` and `NatPow Int` for `HPow Int Nat Int`).
Otherwise a user instance with higher priority replaces the component, and the result is
cached as the canonical form of the builtin instance, while the same instance in an
instance-implicit position is still mapped to the builtin one.
-/
private def builtinInsts : Std.HashMap Expr Expr :=
  let nat := Nat.mkType
  let int := Int.mkType
  let us  := [Level.zero, Level.zero, Level.zero]
  Std.HashMap.ofList [
    (mkApp3 (mkConst ``HAdd us) nat nat nat, Nat.mkInstHAdd),
    (mkApp3 (mkConst ``HSub us) nat nat nat, Nat.mkInstHSub),
    (mkApp3 (mkConst ``HMul us) nat nat nat, Nat.mkInstHMul),
    (mkApp3 (mkConst ``HDiv us) nat nat nat, Nat.mkInstHDiv),
    (mkApp3 (mkConst ``HMod us) nat nat nat, Nat.mkInstHMod),
    (mkApp3 (mkConst ``HPow us) nat nat nat, Nat.mkInstHPow),
    (mkApp  (mkConst ``Add [0]) nat, Nat.mkInstAdd),
    (mkApp  (mkConst ``Sub [0]) nat, Nat.mkInstSub),
    (mkApp  (mkConst ``Mul [0]) nat, Nat.mkInstMul),
    (mkApp  (mkConst ``Div [0]) nat, Nat.mkInstDiv),
    (mkApp  (mkConst ``Mod [0]) nat, Nat.mkInstMod),
    (mkApp2 (mkConst ``Pow [0, 0]) nat nat, Nat.mkInstPow),
    (mkApp  (mkConst ``NatPow [0]) nat, Nat.mkInstNatPow),
    (mkApp  (mkConst ``LT [0]) nat, Nat.mkInstLT),
    (mkApp  (mkConst ``LE [0]) nat, Nat.mkInstLE),

    (mkApp3 (mkConst ``HAdd us) int int int, Int.mkInstHAdd),
    (mkApp3 (mkConst ``HSub us) int int int, Int.mkInstHSub),
    (mkApp3 (mkConst ``HMul us) int int int, Int.mkInstHMul),
    (mkApp3 (mkConst ``HDiv us) int int int, Int.mkInstHDiv),
    (mkApp3 (mkConst ``HMod us) int int int, Int.mkInstHMod),
    (mkApp3 (mkConst ``HPow us) int nat int, Int.mkInstHPow),
    (mkApp  (mkConst ``Add [0]) int, Int.mkInstAdd),
    (mkApp  (mkConst ``Sub [0]) int, Int.mkInstSub),
    (mkApp  (mkConst ``Mul [0]) int, Int.mkInstMul),
    (mkApp  (mkConst ``Div [0]) int, Int.mkInstDiv),
    (mkApp  (mkConst ``Mod [0]) int, Int.mkInstMod),
    (mkApp2 (mkConst ``Pow [0, 0]) int nat, Int.mkInstPowNat),
    (mkApp  (mkConst ``NatPow [0]) int, Int.mkInstPow),
    (mkApp  (mkConst ``Neg [0]) int, Int.mkInstNeg),
    (mkApp  (mkConst ``LT [0]) int, Int.mkInstLT),
    (mkApp  (mkConst ``LE [0]) int, Int.mkInstLE),
  ]

/--
Some modules in grind use builtin instances defined directly in core (e.g., `lia`).
Users may provide nonstandard instances that are definitionally equal to the ones in core.
Given a type, such as `HAdd Int Int Int`, this function returns the instance defined in
core.
-/
def getBuiltinInstance? (type : Expr) : Option Expr :=
  if let some inst := builtinInsts[type]? then some inst else
  -- Parametric instances: numerals and decidability of `Int`/`Nat` comparisons.
  match_expr type with
  | OfNat α n =>
    if α.isConstOf ``Int then some (mkApp (mkConst ``instOfNat) n)
    else if α.isConstOf ``Nat then some (mkApp (mkConst ``instOfNatNat) n)
    else none
  | Decidable p =>
    match_expr p with
    | LE.le α i a b =>
      if α.isConstOf ``Int && i.isConstOf ``Int.instLEInt then some (mkApp2 (mkConst ``Int.decLe) a b)
      else if α.isConstOf ``Nat && i.isConstOf ``instLENat then some (mkApp2 (mkConst ``Nat.decLe) a b)
      else none
    | LT.lt α i a b =>
      if α.isConstOf ``Int && i.isConstOf ``Int.instLTInt then some (mkApp2 (mkConst ``Int.decLt) a b)
      else if α.isConstOf ``Nat && i.isConstOf ``instLTNat then some (mkApp2 (mkConst ``Nat.decLt) a b)
      else none
    | Eq α a b =>
      if α.isConstOf ``Int then some (mkApp2 (mkConst ``Int.instDecidableEq) a b)
      else if α.isConstOf ``Nat then some (mkApp2 (mkConst ``instDecidableEqNat) a b)
      else none
    | _ => none
  | _ => none

/--
The algebraic structure instances of `Int` and `Nat` that `Sym.Arith` classification queries, as
synthesized from the core instances, together with the structures that `Prop` does not have. A
`none` entry is a query without instance. Each `grind` goal classifies the types again, and
resolving these queries dominated the classification cost.

The table ignores local and user-declared instances of these classes: with
`[Grind.CommSemiring Prop]` in the local context, `Sym` and `grind` still find no semiring
structure on `Prop`. Redeclaring the algebraic structures of `Int`, `Nat` or `Prop` is not
supported, as for the operator instances of `builtinInsts`.
-/
private def builtinAlgebraicInsts : Std.HashMap Expr (Option Expr) :=
  let nat := Nat.mkType
  let int := Int.mkType
  let prop := mkSort 0
  let z := [Level.zero]
  let app (n : Name) (args : Array Expr) := mkAppN (mkConst n z) args
  -- `Int`
  let crI := mkConst ``Grind.instCommRingInt
  let ringI := app ``Grind.CommRing.toRing #[int, crI]
  let srI := app ``Grind.Ring.toSemiring #[int, ringI]
  let csI := app ``Grind.CommRing.toCommSemiring #[int, crI]
  let nmI := app ``Grind.Semiring.toNatModule #[int, app ``Grind.CommSemiring.toSemiring #[int, csI]]
  let lopI := mkConst ``Int.instLinearOrderPackage
  let lppI := app ``Std.LinearOrderPackage.toLinearPreorderPackage #[int, lopI]
  let preI := app ``Std.PreorderPackage.toIsPreorder #[int, app ``Std.LinearPreorderPackage.toPreorderPackage #[int, lppI]]
  let leI := mkConst ``Int.instLEInt
  let ltI := mkConst ``Int.instLTInt
  -- `Nat`
  let csN := mkConst ``Grind.instCommSemiringNat
  let srN := app ``Grind.CommSemiring.toSemiring #[nat, csN]
  let nmN := app ``Grind.Semiring.toNatModule #[nat, srN]
  let leN := mkConst ``instLENat
  let ltN := mkConst ``instLTNat
  let preN := mkConst ``Grind.instIsPreorderNat
  let linN := mkConst ``Nat.instIsLinearOrder
  Std.HashMap.ofList [
    (app ``Grind.CommRing #[int], some crI),
    (app ``Grind.Ring #[int], some ringI),
    (app ``Grind.CommSemiring #[int], some csI),
    (app ``Grind.Semiring #[int], some (app ``Grind.CommSemiring.toSemiring #[int, csI])),
    (app ``Grind.Field #[int], none),
    (app ``Grind.NatModule #[int], some nmI),
    (app ``Grind.NoNatZeroDivisors #[int, nmI], some (mkConst ``Grind.instNoNatZeroDivisorsInt)),
    (app ``Std.IsPreorder #[int, leI], some preI),
    (app ``Std.IsPartialOrder #[int, leI], some (app ``Std.PartialOrderPackage.toIsPartialOrder
      #[int, app ``Std.LinearOrderPackage.toPartialOrderPackage #[int, lopI]])),
    (app ``Std.IsLinearPreorder #[int, leI], some (app ``Std.LinearPreorderPackage.toIsLinearPreorder #[int, lppI])),
    (app ``Std.IsLinearOrder #[int, leI], some (mkConst ``Grind.instIsLinearOrderInt)),
    (app ``Std.LawfulOrderLT #[int, ltI, leI], some (mkConst ``Grind.instLawfulOrderLTInt)),
    (app ``Grind.OrderedRing #[int, srI, leI, ltI, preI], some (mkConst ``Grind.instOrderedRingInt)),
    (app ``NatCast #[int], some (mkConst ``instNatCastInt)),
    (app ``Max #[int], some (mkConst ``Int.instMax)),
    (app ``Dvd #[int], some (mkConst ``Int.instDvd)),
    (app ``Grind.CommRing #[nat], none),
    (app ``Grind.Ring #[nat], none),
    (app ``Grind.Field #[nat], none),
    (app ``Grind.CommSemiring #[nat], some csN),
    (app ``Grind.Semiring #[nat], some srN),
    (app ``Grind.AddRightCancel #[nat, mkConst ``instAddNat], some (mkConst ``Grind.instAddRightCancelNat)),
    (app ``Grind.NatModule #[nat], some nmN),
    (app ``Grind.NoNatZeroDivisors #[nat, nmN], some (mkConst ``Grind.instNoNatZeroDivisorsNat)),
    (app ``Std.IsPreorder #[nat, leN], some preN),
    (app ``Std.IsPartialOrder #[nat, leN], some (app ``Std.IsLinearOrder.toIsPartialOrder #[nat, leN, linN])),
    (app ``Std.IsLinearPreorder #[nat, leN], some (app ``Std.IsLinearOrder.toIsLinearPreorder #[nat, leN, linN])),
    (app ``Std.IsLinearOrder #[nat, leN], some linN),
    (app ``Std.LawfulOrderLT #[nat, ltN, leN], some (mkConst ``Grind.instLawfulOrderLTNat)),
    (app ``Grind.OrderedRing #[nat, srN, leN, ltN, preN], some (mkConst ``Grind.instOrderedRingNat)),
    (app ``NatCast #[nat], some (mkConst ``instNatCastNat)),
    (app ``Max #[nat], some (mkConst ``Nat.instMax)),
    (app ``Dvd #[nat], some (mkConst ``Nat.instDvd)),
    (app ``Grind.CommRing #[prop], none),
    (app ``Grind.Ring #[prop], none),
    (app ``Grind.CommSemiring #[prop], none),
    (app ``Grind.Semiring #[prop], none),
  ]

/-- The semiring of `Int` that `Sym.Arith` classification derives from its commutative ring. -/
private def intSemiring : Expr :=
  mkApp2 (mkConst ``Grind.Ring.toSemiring [0]) Int.mkType
    (mkApp2 (mkConst ``Grind.CommRing.toRing [0]) Int.mkType (mkConst ``Grind.instCommRingInt))

/-- The semiring of `Nat` that `Sym.Arith` classification derives from its commutative semiring. -/
private def natSemiring : Expr :=
  mkApp2 (mkConst ``Grind.CommSemiring.toSemiring [0]) Nat.mkType (mkConst ``Grind.instCommSemiringNat)

/--
Whether the environment contains the constants of the builtin instance `inst`. `grind` also runs in
`Init` modules that do not import the modules declaring the instances, and resolution handles them.

Only constants and applications are visited, which is correct only because the builtin instances
are applications of constants, without binders, `let`s or projections. A shared subterm is visited
once per occurrence, which is cheap because the instances are small.
-/
private def isDeclared (env : Environment) : Expr → Bool
  | .const n _ => env.contains n
  | .app f a => isDeclared env f && isDeclared env a
  | _ => true

/--
Queries of `builtinAlgebraicInsts` with output parameters or a parameter: `IsCharP α s ?n` for the
semiring `s` of the classified `Int` and `Nat`, and `PowIdentity α ?s ?p`, which they do not have.
-/
private def builtinOutParamInst? (type : Expr) : MetaM (Option (Option Expr)) := do
  match_expr type with
  | Grind.IsCharP α s n =>
    let inst ← if α.isConstOf ``Int && s == intSemiring then pure (mkConst ``Grind.instIsCharPIntOfNatNat)
      else if α.isConstOf ``Nat && s == natSemiring then pure (mkConst ``Grind.instIsCharPNatOfNat)
      else return none
    unless isDeclared (← getEnv) inst do return none
    -- assigns the characteristic `0` of the instance's type, as resolution does
    if (← isDefEq n (← inferType inst).appArg!) then return some (some inst) else return none
  | Grind.PowIdentity α _ _ =>
    if α.isConstOf ``Int || α.isConstOf ``Nat then return some none else return none
  | _ => return none

def synthInstanceMeta? (type : Expr) : MetaM (Option Expr) := do profileitM Exception "sym typeclass inference" (← getOptions) (decl := type.getAppFn.constName?.getD .anonymous) do
  if let some inst := getBuiltinInstance? type then
    return inst
  if let some inst? := builtinAlgebraicInsts[type]? then
    let env ← getEnv
    if inst?.all (isDeclared env) then return inst?
  if let some inst? ← builtinOutParamInst? type then
    return inst?
  catchInternalId isDefEqStuckExceptionId
    (synthInstanceCore? type none)
    (fun _ => pure none)

/--
Registers `inst` as **the** instance for `type`. `synthInstance?` returns it without
running typeclass resolution, making `inst` the canonical representative for `type`.
Intended for satellite modules that construct instances for types they create themselves
(e.g., `grind linarith`'s envelope type `IntModule.OfNatModule.Q`).
-/
def registerInstance (type inst : Expr) : SymM Unit :=
  modify fun s => { s with instanceOverrides := s.instanceOverrides.insert type inst }

def synthInstance? (type : Expr) : SymM (Option Expr) := do
  if let some inst := (← get).instanceOverrides.find? type then
    return some inst
  synthInstanceMeta? type

def synthInstance (type : Expr) : SymM Expr := do
  let some inst ← synthInstance? type
    | throwError "`sym` failed to find instance{indentExpr type}"
  return inst

/--
Helper function for instantiating a type class `type`, and
then using the result to perform `isDefEq x val`.
-/
def synthInstanceAndAssign (x type : Expr) : SymM Bool := do
  let some val ← synthInstance? type | return false
  isDefEq x val

end Lean.Meta.Sym
