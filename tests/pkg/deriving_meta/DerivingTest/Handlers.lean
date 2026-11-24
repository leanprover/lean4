module

public meta import Lean.Elab.Deriving.Meta

public section

open Lean Elab Meta Deriving

inductive Data where
  | nat (n : Nat)
  | int (n : Int)
  | string (s : String)
  | array (xs : Array Data)
  | ctor (idx : Nat) (l : List Data)
deriving Inhabited, Repr

class ToData (α : Type u) where
  convert : α → Data

inductive Data.Small : Data → Prop
  | nat (n : Nat) : Small (.nat n)
  | int (n : Int) : Small (.int n)
  | string (s : String) : Small (.string s)
  | array (xs : Array Data) (h : ∀ x ∈ xs, Small x) : Small (.array xs)
  | ctor
    (idx : Nat) (l : List Data) (hcidx : idx < 16) (hfields : l.length < 16) (h : ∀ x ∈ l, Small x)
    : Small (.ctor idx l)

class IsSmallToData (α : Type u) [ToData α] where
  small : ∀ x : α, (ToData.convert x).Small

inductive DiffPath where
  | differentValue
  | differentCtors (leftCtor rightCtor : Name)
  | ctor (ctorName : Name) (fieldIdx : Nat) (more : DiffPath)
  | field (fieldName : Name) (more : DiffPath)
  | atIdx (idx : Nat) (more : DiffPath)
deriving Repr

class FirstDiff (α : Type u) [ToData α] where
  firstDiff : α → α → Option DiffPath

export FirstDiff (firstDiff)

/-!
Simple example of how you can write a deriving handler using the new framework
-/

meta def deriveToData :=
  mkInductiveDerivingHandler ``ToData do
    deriveTransformationInstPerConstructor fun ival cval fields _ => do
      let mut encodings : Array Expr := #[]
      for field in fields do
        let ty ← inferType field
        let some lvl ← getDecLevel? ty
          | continue
        let inst ← synthInstanceDeriving (.app (.const ``ToData [lvl]) ty)
        let val := mkApp3 (.const ``ToData.convert [lvl]) ty inst field
        encodings := encodings.push val
      if ival.ctors.length = 1 && encodings.size = 1 then
        return encodings[0]!
      let mut list : Expr := .app (.const ``List.nil [0]) (.const ``Data [])
      for e in encodings.reverse do
        list := mkApp3 (.const ``List.cons [0]) (.const ``Data []) e list
      return mkApp2 (.const ``Data.ctor []) (toExpr cval.cidx) list

meta partial def deriveIsSmallToData :=
  mkInductiveDerivingHandler ``IsSmallToData do
    deriveLawClassUsingCtor fun
      | ctx, ``IsSmallToData.small =>
        ctx.withUnfoldOnce <| .casesLaw fun ival cval fields ctorApp expectedType () => do
          let_expr Data.Small thing := expectedType
            | throwError "Unexpected goal for `IsSmallToData` deriving handler:\
                {indentExpr expectedType}"
          -- solve the goal recursively
          solveSmall thing
      | _, _ => .unhandled
    return true
where
  solveSmall (thing : Expr) : DerivingM Expr := do
    match_expr thing with
    | c@ToData.convert α inst x =>
      let lawInst ← synthInstanceDeriving (mkApp2 (.const ``IsSmallToData c.constLevels!) α inst)
      return mkApp4 (.const ``IsSmallToData.small c.constLevels!) α inst lawInst x
    | Data.nat x =>
      return .app (.const ``Data.Small.nat []) x
    | Data.int x =>
      return .app (.const ``Data.Small.int []) x
    | Data.string x =>
      return .app (.const ``Data.Small.string []) x
    | Data.ctor idx l =>
      let some lit ← getNatValue? idx
        | throwError "Unexpected `Data.ctor` application, expected literal constructor index\
            {indentExpr thing}"
      unless lit < 16 do
        throwError "Failed to derive `IsSmallToData`, constructor index {lit} is not \
          smaller than 16"
      let (listProof, fieldCount) ← solveForallSmall l
      unless fieldCount < 16 do
        throwError "Failed to derive `IsSmallToData`, field count {lit} is not \
          smaller than 16"
      let cidxProof :=
        mkApp3 (.const ``Nat.le_of_ble_eq_true []) (mkRawNatLit (lit + 1)) (mkRawNatLit 16)
          reflBoolTrue
      let fieldProof :=
        mkApp3 (.const ``Nat.le_of_ble_eq_true []) (mkRawNatLit (fieldCount + 1)) (mkRawNatLit 16)
          reflBoolTrue
      return mkApp5 (.const ``Data.Small.ctor []) idx l cidxProof fieldProof listProof
    | _ =>
      throwError "Unexpected goal for `IsSmallToData` deriving handler:\
        {indentExpr (mkSmallExpr thing)}"
  solveForallSmall (list : Expr) : DerivingM (Expr × Nat) := do
    match_expr list with
    | List.nil _ =>
      return
        (mkApp2 (.const ``List.forall_mem_nil [0]) (.const ``Data []) (.const ``Data.Small []), 0)
    | List.cons _ head tail =>
      let iff :=
        mkApp4 (.const ``List.forall_mem_cons [0]) (.const ``Data []) (.const ``Data.Small []) head
          tail
      let (tailProof, count) ← solveForallSmall tail
      let mpr := .proj ``Iff 1 iff
      let and :=
        mkApp4 (.const ``And.intro []) (mkSmallExpr head) (mkForallMemExpr tail) (← solveSmall head)
          tailProof
      return (.app mpr and, count + 1)
    | _ =>
      throwError "Unexpected goal for `IsSmallToData` deriving handler:\
        {indentExpr (mkForallMemExpr list)}"
  mkSmallExpr (e : Expr) : Expr := .app (.const ``Data.Small []) e
  mkForallMemExpr (e : Expr) : Expr :=
    -- you can tell this would be nicer with Qq
    let data := .const ``Data []
    let listData := .app (.const ``List [0]) data
    .forallE `x data
      (.forallE `hmem
        (mkApp5 (.const ``Membership.mem [0, 0]) data listData
          (.app (.const ``List.instMembership [0]) data) e (.bvar 0))
        (mkSmallExpr (.bvar 1)) .default)
      .default

meta def deriveFirstDiff : DerivingHandler :=
  mkInductiveDerivingHandler ``FirstDiff do
    makeInstancesUsingCtor fun
      | ``firstDiff => .doubleCases
        (differentCtor := fun input => do
          let leftName ← mkNondepCases input.lhs (mkConst ``Name) fun _ cval _ _ => do
            return toExpr cval.name
          let rightName ← mkNondepCases input.rhs (mkConst ``Name) fun _ cval _ _ => do
            return toExpr cval.name
          return mkApp2 (.const ``some [0]) (mkConst ``DiffPath)
            (mkApp2 (mkConst ``DiffPath.differentCtors) leftName rightName))
        fun alt => do
          -- TODO for later today
          return .app (.const ``none [0]) (mkConst ``DiffPath)
      | _ => .unhandled
    return true

meta initialize
  registerDerivingHandler ``ToData deriveToData
  registerDerivingHandler ``IsSmallToData deriveIsSmallToData
