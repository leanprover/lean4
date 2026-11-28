module

public meta import Lean.Elab.Deriving.Meta
import all Lean.Elab.Deriving.Meta.Util

public section

/-!
# Examples of well-written deriving handlers using the `Lean.Meta.Deriving` framework
-/

open Lean Elab Meta Deriving

inductive Data where
  | nat (n : Nat)
  | int (n : Int)
  | string (s : String)
  | array (xs : Array Data)
  | ctor (idx : Nat) (l : List Data)
deriving Inhabited, Repr

/-!
A simple transformation type class. These are the simplest kinds of type classes and have the best
support in the framework.
-/

class ToData (α : Type u) where
  convert : α → Data

inductive Data.Small : Data → Prop
  | nat (n : Nat) : Small (.nat n)
  | int (n : Int) : Small (.int n)
  | string (s : String) : Small (.string s)
  | array (xs : Array Data) (h : ∀ x ∈ xs, Small x) : Small (.array xs)
  | ctor
    (idx : Nat) (l : List Data) (hcidx : idx < 32) (hfields : l.length < 32) (h : ∀ x ∈ l, Small x)
    : Small (.ctor idx l)

/-!
An (arguably silly) example for a law type class of a transformation type class
-/

class IsSmallToData (α : Type u) [ToData α] where
  small : ∀ x : α, (ToData.convert x).Small

inductive DiffPath where
  | differentValue
  | differentCtors (leftCtor rightCtor : Name)
  | ctor (ctorName : Name) (fieldIdx : Nat) (more : DiffPath)
  | field (fieldName : Name) (more : DiffPath)
  | atIdx (idx : Nat) (more : DiffPath)
deriving Repr

/-!
A "comparison" type class, i.e. a type class where the operation takes two type arguments
-/

class FirstDiff (α : Type u) where
  firstDiff : α → α → Option DiffPath

export FirstDiff (firstDiff)

-- TODO: make this derivable
class LawfulFirstDiff (α : Type u) [FirstDiff α] where
  of_firstDiff_eq_none : (a b : α) → firstDiff a b = none → a = b

/-!
A comparison type class with a slow deriving handler
-/

class CompareCtorIdx (α : Type u) where
  compare : α → α → Ordering

/-!
A type class with multiple fields and corresponding law type classes
-/

class Bounds (α : Type u) where
  lower : α → Nat
  upper : α → Nat
  maximum : Nat

class LawfulBounds (α : Type u) [Bounds α] where
  lower_le_upper (a : α) : Bounds.lower a ≤ Bounds.upper a
  upper_le_maximum (a : α) : Bounds.upper a ≤ Bounds.maximum α

/-!
A private type class
-/

private class Secret (α : Type u) where
  secret : Name

/-!
A `Sort`-polymorphic type class whose field depends on the universe
-/

class ULiftCtorIdx (α : Sort u) where
  idx : α → ULift.{u} Nat

/-!
We'll derive this type class using tactic elaboration to test that that works
-/

class Const (α : Type u) where
  const : α → Nat

/-!
An especially complicated dependent law type class which has dependency in both binders and the goal
-/

def Holds {p : Prop} (_ : p) : Prop := True

class ToDataDepLaw (α : Type u) [ToData α] : Prop where
  law : ∀ x : α, (h : (ToData.convert x).Small) → Holds h

/-!
A type class that only operates on `Type`
-/

class GenRandom (α : Type) where
  random (α) : IO α

/-!
A non-recursive class like `Inhabited`
-/

class Default (α : Sort u) where
  default : α

/-!
Two similarly named but differently behaving type classes
-/

class A.Similar (α : Type u) where
  /-- We let this mean: the constructor index is even -/
  something : α → Bool

class B.Similar (α : Type u) where
  /-- We let this mean: the constructor index is odd -/
  something : α → Bool

/-!
We support dependent transformation type classes (here in the sense of the result type depending on
the type parameter).
-/

class Transform (α : Type u) where
  transform : α → α

class IsInvolution (α : Type u) [Transform α] where
  transform_transform (x : α) : Transform.transform (Transform.transform x) = x

/-!
A type class `abbrev`
-/

class ActualClass (n : Nat) (s : String) (α : Type u × Name) (i : outParam Nat) where
  thing : α.1 → Nat

abbrev AbbrevClass (α : Type u) [Bounds α] := ∀ n, ActualClass n "hi" (α, `foo) (Bounds.maximum α)

/-!
A transformation type class with more arguments
-/

class Flatten (α : Type u) where
  flatten : α → List Nat → List Nat

class LawfulFlatten (α : Type u) [Flatten α] where
  flatten_append (x : α) (l l' : List Nat) : Flatten.flatten x (l ++ l') = Flatten.flatten x l ++ l'

/-!
Convenience type class whose deriving handler calls the deriving handler of all classes that don't
have special assumptions about the type (i.e. work on almost every non-`Prop` inductive with
sufficient existing instances).

We don't include `Secret` in the list here because it is private but we still derive it
automatically.
-/

class AllGeneralClasses (α : Type u)
    extends FirstDiff α, CompareCtorIdx α, Bounds α, LawfulBounds α, ULiftCtorIdx α, Const α,
      toASimilar : A.Similar α, toBSimilar : B.Similar α, Transform α, Flatten α where
  -- we use `ToData` as the simplest class to test most error messages but with this as a parent,
  -- this is always an instance for `ToData α` so we'd never get the "missing instance" error
  -- message and only the "unsuitable instance" one
  toToData : ToData α
  -- this is not a structure
  toAbbrevClass : AbbrevClass α

/-!
Convenience type class for data classes not included in `AllGeneralClasses`, including `GenRandom`
which requires `Type` and no indices and `Default` which doesn't always behave well with indices
-/

class OtherDataClasses (α : Type) extends GenRandom α, Default α where

/-!
Convenience type class for law type classes that are not included in `AllGeneralClasses` because
they don't work for nested types.
-/

class OtherLawClasses (α : Type u)
  extends AllGeneralClasses α, ToDataDepLaw α, IsSmallToData α, IsInvolution α,
    LawfulFlatten α where

/-!
The deriving handlers
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
        ctx.withUnfoldOnce <| .casesLaw fun _ival _cval _fields _ctorApp expectedType () => do
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
      unless lit < 32 do
        throwError "Failed to derive `IsSmallToData`, constructor index {lit} is not \
          smaller than 32"
      let (listProof, fieldCount) ← solveForallSmall l
      unless fieldCount < 32 do
        throwError "Failed to derive `IsSmallToData`, field count {fieldCount} is not \
          smaller than 32"
      let cidxProof :=
        mkApp3 (.const ``Nat.le_of_ble_eq_true []) (mkRawNatLit (lit + 1)) (mkRawNatLit 32)
          reflBoolTrue
      let fieldProof :=
        mkApp3 (.const ``Nat.le_of_ble_eq_true []) (mkRawNatLit (fieldCount + 1)) (mkRawNatLit 32)
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

@[expose, macro_inline]
def Option.mapElim (x : Option α) (f : α → β) (d : Option β) : Option β :=
  match x with
  | none => d
  | some val => f val

@[expose, macro_inline]
def Option.mapElimDep (x : Option α) (f : α → β) (d : x = none → Option β) : Option β :=
  match x with
  | none => d rfl
  | some val => f val

meta def deriveFirstDiff : DerivingHandler :=
  mkInductiveDerivingHandler ``FirstDiff do
    makeInstancesUsingCtor fun
      | ``firstDiff =>
        .doubleCases
          (differentCtor := fun input => do
            let leftName ←
              mkNondepCases input.lhs (mkConst ``Name) fun _ cval _ _ => do return toExpr cval.name
            let rightName ←
              mkNondepCases input.rhs (mkConst ``Name) fun _ cval _ _ => do return toExpr cval.name
            -- Test that `cidxNeProof` has the right type
            let expectedType := mkNot (← mkEq (← mkCtorIdxApp input.lhs) (← mkCtorIdxApp input.rhs))
            let type ← inferType input.cidxNeProof
            unless ← isDefEq type expectedType do
              Term.throwTypeMismatchError
                m!"Unexpected type for `cidxNeProof`,{indentExpr input.cidxNeProof}" expectedType
                type input.cidxNeProof
            return mkApp2 (.const ``some [0]) (mkConst ``DiffPath)
              (mkApp2 (mkConst ``DiffPath.differentCtors) leftName rightName))
          fun alt => do
            let pathType := mkConst ``DiffPath
            let outType := .app (.const ``Option [0]) pathType
            let mut fields : Option (Array Name) := none
            if let some info := getStructureInfo? (← getEnv) alt.inductInfo.name then
              fields := info.fieldNames
            foldSimilarVarsParallel alt.leftFields alt.rightFields outType (init := 0)
              (ignoreDep := fun e _ => isProof e)
              (finish := fun _ => return .app (.const ``none [0]) pathType)
              fun pair idx cont => do
                if pair.lvl.isAlwaysZero then
                  return ← cont none (idx + 1)
                let some u ← decLevel? pair.lvl
                  | throwError "Failed to decrement level `{pair.lvl}` of{indentExpr pair.type}"
                let inst ← synthInstanceDeriving (.app (.const ``FirstDiff [u]) pair.type)
                let diff := mkApp4 (.const ``firstDiff [u]) pair.type inst pair.lhs pair.rhs
                let wrapper ←
                  withLocalDeclD `path pathType fun path => do
                    let e :=
                      if let some fieldName := fields.bind (·[idx]?) then
                        mkApp2 (.const ``DiffPath.field []) (toExpr fieldName) path
                      else
                        mkApp3 (.const ``DiffPath.ctor []) (toExpr alt.ctorInfo.name) (toExpr idx)
                          path
                    mkLambdaFVars #[path] e
                if pair.hasRelevantForwardDeps then
                  let lawful ←
                    synthInstanceDeriving (mkApp2 (.const ``LawfulFirstDiff [u]) pair.type inst)
                  let none := .app (.const ``none [0]) pathType
                  let eqNone := mkApp3 (.const ``Eq [1]) outType diff none
                  let more ←
                    withLocalDeclD `h eqNone fun h => do
                      let eqProof :=
                        mkApp6 (.const ``LawfulFirstDiff.of_firstDiff_eq_none [u]) pair.type inst
                          lawful pair.lhs pair.rhs h
                      mkLambdaFVars #[h] <| ← cont eqProof (idx + 1)
                  return mkApp5 (.const ``Option.mapElimDep [0, 0]) pathType pathType diff wrapper
                    more
                else
                  let more ← cont none (idx + 1)
                  if more.isAppOf ``none then
                    return mkApp4 (.const ``Option.map [0, 0]) pathType pathType wrapper diff
                  else
                    return mkApp5 (.const ``Option.mapElim [0, 0]) pathType pathType diff wrapper
                      more
      | _ => .unhandled
    return true

meta def deriveCompareCtorIdx : DerivingHandler :=
  mkInductiveDerivingHandler ``CompareCtorIdx do
    makeInstancesUsingCtor (nonRec := true) fun
      | ``CompareCtorIdx.compare =>
        .doubleCasesSlow
          (fun alt =>
            return
              if alt.leftCtor.cidx < alt.rightCtor.cidx then
                mkConst ``Ordering.lt
              else
                mkConst ``Ordering.gt)
          (fun _ => return mkConst ``Ordering.eq)
      | _ => .unhandled
    return true

meta def deriveBounds : DerivingHandler :=
  mkInductiveDerivingHandler ``Bounds do
    let mut ctorBounds : NameMap (Nat × Nat) := {}
    let mut inductBounds : NameMap Nat := {}
    for ind in (← read).indInfo.all do
      let inductInfo ← getConstInfoInduct ind
      let mut count := 0
      for ctor in inductInfo.ctors do
        let ctorInfo ← getConstInfoCtor ctor
        ctorBounds := ctorBounds.insert ctor (count, count + ctorInfo.numFields)
        count := count + ctorInfo.numFields
      inductBounds := inductBounds.insert ind count
    makeInstancesUsingCtor (nonRec := true) fun
      | ``Bounds.lower =>
        .cases fun _ival cval _fields _ _ => return toExpr (ctorBounds.get! cval.name).1
      | ``Bounds.upper =>
        .cases fun _ival cval _fields _ _ => return toExpr (ctorBounds.get! cval.name).2
      | ``Bounds.maximum => fun input => return .inline (toExpr (inductBounds.get! input.induct))
      | _ => .unhandled
    return true

meta def deriveLawfulBounds : DerivingHandler :=
  mkInductiveDerivingHandler ``LawfulBounds do
    deriveLawClassUsingCtor (nonRec := true) fun
      | ctx, ``LawfulBounds.lower_le_upper
      | ctx, ``LawfulBounds.upper_le_maximum =>
        ctx.withUnfoldOnce <| .casesLaw fun _ival _cval _fields _ctorApp expectedType () => do
          let_expr LE.le _ inst l r := expectedType
            | throwError
                "Unexpected goal in `LawfulBounds` deriving handler{indentExpr expectedType}"
          let some a ← getNatValue? l
            | throwError "Unexpected goal in `LawfulBounds` deriving handler: Left-hand side is \
                not a literal:{indentExpr expectedType}"
          let some b ← getNatValue? r
            | throwError "Unexpected goal in `LawfulBounds` deriving handler: Left-hand side is \
                not a literal:{indentExpr expectedType}"
          if b < a then
            throwError "Unexpected goal in `LawfulBounds` deriving handler: Inequality is not \
              true:{indentExpr expectedType}"
          let dec := mkApp2 (.const ``Nat.decLe []) l r
          return mkApp3 (.const ``of_decide_eq_true []) expectedType dec reflBoolTrue
      | _, _ => .unhandled
    return true

private meta def deriveSecret : DerivingHandler :=
  mkInductiveDerivingHandler ``Secret do
    makeInstancesUsingCtor (nonRec := true) fun
      | ``Secret.secret => fun input => return .inline <| toExpr input.induct
      | _ => .unhandled
    return true

meta def deriveULiftCtorIdx : DerivingHandler :=
  mkInductiveDerivingHandler ``ULiftCtorIdx do
    deriveTransformationInstPerConstructor (nonRec := true) fun _ival cval _ _ =>
      return mkApp2 (.const ``ULift.up [(← read).indLevel, 0]) Nat.mkType (toExpr cval.cidx)

meta def deriveConst : DerivingHandler :=
  mkInductiveDerivingHandler ``Const do
    deriveTransformationInstPerConstructor (nonRec := true) fun _ _ _ _ => do
      let e ← Term.elabTerm (← `(by let y : Nat := 5; exact y + 1)) (some Nat.mkType)
      Term.synthesizeSyntheticMVarsNoPostponing
      return e

meta def deriveToDataDepLaw : DerivingHandler :=
  mkInductiveDerivingHandler ``ToDataDepLaw do
    deriveLawClassUsingCtor fun
      | ctx, ``ToDataDepLaw.law =>
        ctx.withUnfoldOnce <| fun input => do
          forallTelescopeReducing (whnfType := true) input.expectedType fun vars body => do
            unless body == mkConst ``True do
              throwError "Unexpected goal in `ToDataDepLaw` deriving handler{indentExpr body}"
            return .inline <| ← mkLambdaFVars vars (mkConst ``trivial)
      | _, _ => .unhandled
    return true

meta partial def deriveGenRandom : DerivingHandler :=
  mkInductiveDerivingHandler ``GenRandom do
    -- this deriving handler doesn't work without `partial`
    -- because termination is probabilistic
    makeInstancesUsingCtor (supportsRec := false) fun
      | ``GenRandom.random => fun input =>
        return .usingHelper fun _ _ => do
          let io := mkConst ``IO
          let ioPureInst ← synthInstance (.app (.const ``Pure [0, 0]) io)
          let ioBindInst ← synthInstance (.app (.const ``Bind [0, 0]) io)
          let ioExceptInst ←
            synthInstance (mkApp2 (.const ``MonadExcept [0, 0, 0]) (.const ``IO.Error []) io)
          let ioLiftInst ←
            synthInstance (mkApp2 (.const ``MonadLiftT [0, 0, 0]) (.const ``BaseIO []) io)
          let ioPure := mkApp2 (.const ``Pure.pure [0, 0]) io ioPureInst
          let ioBind := mkApp2 (.const ``Bind.bind [0, 0]) io ioBindInst
          let ioThrow := mkApp3 (.const ``throw [0, 0, 0]) (.const ``IO.Error []) io ioExceptInst
          let ioLift := mkApp3 (.const ``liftM [0, 0, 0]) (.const ``BaseIO []) io ioLiftInst
          let info ← getConstInfoInduct input.induct
          if info.numIndices > 0 then
            throwError "Cannot derive `GenRandom` in the presence of indices but \
              `{.ofConstName input.induct}` has {info.numIndices} indices"
          if info.ctors.isEmpty then
            let ioExceptInst ←
              synthInstance (mkApp2 (.const ``MonadExcept [0, 0, 0]) (.const ``IO.Error []) io)
            return mkApp2 ioThrow input.typeApp
              (.app (.const ``IO.Error.userError [])
                (toExpr s!"Failed to generate random value for uninhabited type `{input.induct}`"))
          let rec mkFields (ctorType ctorApp : Expr) (ctorName : Name) := do
            let .forallE nm t b bi := ctorType
              | return mkApp2 ioPure input.typeApp ctorApp
            let lvl ← getLevel t
            let more ←
              withLocalDecl nm bi t fun var => do
                mkLambdaFVars #[var] <| ← mkFields (b.instantiate1 var) (ctorApp.app var) ctorName
            if lvl.isEquiv Level.one then
              let inst ← synthInstanceDeriving (.app (.const ``GenRandom []) t)
              let randValue := mkApp2 (.const ``GenRandom.random []) t inst
              return mkApp4 ioBind t input.typeApp randValue more
            else if lvl.isAlwaysZero then
              let inst ← synthInstanceDeriving (.app (.const ``Decidable []) t)
              let fail :=
                mkApp2 ioThrow input.typeApp
                  (.app (.const ``IO.Error.userError [])
                    (toExpr s!"Guard failed at constructor `{ctorName}`"))
              return mkApp5 (.const ``dite [1]) (.app io input.typeApp) t inst more
                (.lam `h (mkNot t) fail .default)
            else
              throwError "Unexpected level {lvl} at field type{indentExpr t}\
                \nof constructor `{.ofConstName ctorName}`"
          let rec ctorBranch (ctor : Name) := do
            let mut ctorApp := mkAppN (.const ctor (← read).indLParams) (← read).indParams
            let ctorType ← inferType ctorApp
            mkFields ctorType ctorApp ctor
          if let [ctor] := info.ctors then
            return ← ctorBranch ctor
          let branch ←
            withLocalDeclD `cidx Nat.mkType fun cidx => do
              let rec decisionTree (ctors : List Name) (i : Nat) := do
                match ctors with
                | [] => unreachable!
                | [ctor] => ctorBranch ctor
                | head :: tail => do
                  let eq ← mkEq cidx (toExpr i)
                  let decEq := mkApp2 (.const ``Nat.decEq []) cidx (toExpr i)
                  let thenBranch ← ctorBranch head
                  let elseBranch ← decisionTree tail (i + 1)
                  return mkApp5 (.const ``ite [1]) (.app io input.typeApp) eq decEq thenBranch
                    elseBranch
              mkLambdaFVars #[cidx] <| ← decisionTree info.ctors 0
          return mkApp4 ioBind Nat.mkType input.typeApp
            (mkApp2 ioLift Nat.mkType
              (mkApp2 (.const ``IO.rand []) (toExpr 0) (toExpr (info.numCtors - 1))))
            branch
      | _ => .unhandled
    return true

meta def deriveDefault : DerivingHandler :=
  mkInductiveDerivingHandler ``Default do
    makeInstancesUsingCtor (nonRec := true) fun
      | ``Default.default => fun input => do
        let info ← getConstInfoInduct input.induct
        let mut remaining := info.numCtors
        let mut ok := false
        for ctor in info.ctors do
          let oldState ← get
          let oldMCtx ← getMCtx
          let oldCache := (← getThe Meta.State).cache
          try
            let ctorApp := mkAppN (.const ctor (← read).indLParams) (← read).indParams
            let (vars, _bis, body) ← forallMetaTelescope (← inferType ctorApp)
            unless ← isDefEq body input.typeApp do
              throwError "Constructor `{.ofConstName ctor}` is not generalized for all indices"
            for var in vars do
              let type ← instantiateMVars (← inferType var)
              forallTelescope type fun params type => do
                let u ← getLevel type
                let inst ← synthInstanceDeriving (.app (.const ``Default [u]) type)
                let default := mkApp2 (.const ``Default.default [u]) type inst
                var.mvarId!.assign (← mkLambdaFVars params default)
            let ctorApp := mkAppN ctorApp vars
            if isPrivateName ctor then
              return .usingHelper fun _ _ => pure ctorApp
            return .inline ctorApp
          catch ex =>
            set oldState
            modifyThe Meta.State ({ · with cache := oldCache, mctx := oldMCtx })
            remaining := remaining - 1
            if remaining = 0 then
              throwError m!"All attempts to generate a `{.ofConstName ``Default}` \
                instance failed, the last error was:{indentD ex.toMessageData}"
        throwError "Failed to generate `{.ofConstName ``Default}` instance, \
          there are no constructors"
      | _ => .unhandled
    return true

meta def A.deriveSimilar : DerivingHandler :=
  mkInductiveDerivingHandler ``Similar do
    -- we notably don't mark this as `nonRec` to make it
    -- generate instances for the whole mutual block
    deriveTransformationInstPerConstructor fun _ival cval _fields _ctorApp => do
      return toExpr <| cval.cidx % 2 == 0

meta def B.deriveSimilar : DerivingHandler :=
  mkInductiveDerivingHandler ``Similar do
    -- we notably don't mark this as `nonRec` to make it
    -- generate instances for the whole mutual block
    deriveTransformationInstPerConstructor fun _ival cval _fields _ctorApp => do
      return toExpr <| cval.cidx % 2 == 1

meta def deriveTransform : DerivingHandler :=
  mkInductiveDerivingHandler ``Transform do
    deriveTransformationInstPerConstructor fun _ival cval fields _ => do
      let mut newCtorApp := mkAppN (.const cval.name (← read).indLParams) (← read).indParams
      let mut type ← inferType newCtorApp
      for field in fields do
        let .forallE _ _ b _ := type
          | throwError "Internal error in deriving handler for `{.ofConstName ``Transform}`"
        if b.hasLooseBVars then
          -- don't break dependencies by transforming
          newCtorApp := newCtorApp.app field
          type := b.instantiate1 field
        else
          type := b
          let ty ← inferType field
          let some lvl ← getDecLevel? ty
            | newCtorApp := newCtorApp.app field
          let inst ← synthInstanceDeriving (.app (.const ``Transform [lvl]) ty)
          newCtorApp := newCtorApp.app (mkApp3 (.const ``Transform.transform [lvl]) ty inst field)
      return newCtorApp

meta def deriveIsInvolution : DerivingHandler :=
  mkInductiveDerivingHandler ``IsInvolution do
    deriveLawClassUsingCtor fun
      | ctx, ``IsInvolution.transform_transform =>
        ctx.withUnfoldOnce <| .casesLaw fun _ival _cval _fields _ctorApp expectedType _ => do
          let some (_, l, r) := expectedType.eq?
            | throwError
                "Unexpected goal in `IsInvolution` deriving handler:{indentExpr expectedType}"
          let mut lhs := l.getAppFn
          let mut rhs := r.getAppFn
          let largs := l.getAppArgs
          let rargs := r.getAppArgs
          unless lhs == rhs && largs.size = rargs.size do
            throwError "Unexpected goal in `IsInvolution` deriving handler, expected an equality \
              of two applications of the same function with the same \
              arity:{indentExpr expectedType}"
          let mut type ← inferType lhs
          let mut eq? : Option Expr := none
          for larg in largs, rarg in rargs do
            if larg == rarg then
              if let some eq := eq? then
                eq? ← mkCongrFun eq larg
            else
              let fail :=
                throwError "Unexpected goal in `IsInvolution` deriving handler, expected left \
                  argument to be a double application of `transform`:{indentExpr expectedType}"
              let_expr c@Transform.transform α inst x := larg
                | fail
              let_expr c@Transform.transform _ inst' x' := x
                | fail
              unless ← isDefEq inst inst' do
                fail
              let lawInst ←
                synthInstanceDeriving (mkApp2 (.const ``IsInvolution c.constLevels!) α inst)
              let argEq :=
                mkApp4 (.const ``IsInvolution.transform_transform c.constLevels!) α inst lawInst x'
              if let some eq := eq? then
                eq? ← mkCongr eq argEq
              else
                eq? ← mkCongrArg lhs argEq
            lhs := lhs.app larg
            rhs := rhs.app rarg
          eq?.getDM (mkEqRefl l)
      | _, _ => .unhandled
    return true

meta def deriveAbbrevClass : DerivingHandler :=
  mkInductiveDerivingHandler ``AbbrevClass do
    makeInstancesUsingCtor (nonRec := true) fun
      | ``ActualClass.thing => fun input => do
        assert! input.classParams[1]! == toExpr "hi"
        let n := input.classParams[0]!
        let max := input.classParams[3]!
        let cont : FieldHelperProvider Unit :=
          .cases fun _ival cval _fields _ctorApp () =>
            return mkNatAdd max (mkNatMul n (toExpr cval.cidx))
        -- `.cases` will get confused by the expected type ``(α, `foo).fst → Nat``
        -- so clean up the expected type
        cont { input with expectedType := ← mkArrow input.typeApp Nat.mkType }
      | _ => .unhandled
    return true

meta def deriveFlatten : DerivingHandler :=
  mkInductiveDerivingHandler ``Flatten do
    deriveTransformationInstPerConstructor fun ival cval fields _ => do
      withLocalDeclD `acc (.app (.const ``List [0]) Nat.mkType) fun accVar => do
        let mut acc := accVar
        for field in fields.reverse do
          let ty ← inferType field
          let some lvl ← getDecLevel? ty
            | continue
          let inst ← synthInstanceDeriving (.app (.const ``Flatten [lvl]) ty)
          acc := mkApp4 (.const ``Flatten.flatten [lvl]) ty inst field acc
        unless ival.ctors matches [_] do
          acc := mkApp3 (.const ``List.cons [0]) Nat.mkType (toExpr cval.cidx) acc
        mkLambdaFVars #[accVar] acc

meta partial def deriveLawfulFlatten : DerivingHandler :=
  mkInductiveDerivingHandler ``LawfulFlatten do
    deriveLawClassUsingCtor fun
      | ctx, ``LawfulFlatten.flatten_append =>
        ctx.withUnfoldOnce <| .casesLaw fun _ _ _ _ expectedType () => do
          forallBoundedTelescope expectedType (some 2) fun lists expectedType => do
            let some (_, a, b) := expectedType.eq?
              | unreachable!
            let_expr HAppend.hAppend _ _ _ _ e l₂ := b
              | unreachable!
            let (res, proof) ← pushInAppend e l₂
            unless ← isDefEq a res do
              throwError "Failed to derive `LawfulFlatten`, got stuck at equality\
                {indentExpr (← mkEq a res)}"
            mkLambdaFVars lists proof
      | _, _ => .unhandled
    return true
where
  /-- Returns `(e', h : e' = e ++ l₂)` -/
  pushInAppend (e l₂ : Expr) : DerivingM (Expr × Expr) := do
    let accType := .app (.const ``List [0]) Nat.mkType
    let fallback :=
      return (mkListAppend e l₂, mkApp2 (.const ``rfl [1]) accType (mkListAppend e l₂))
    let .app fn acc := e
      | fallback
    match_expr fn with
    | c@Flatten.flatten α inst thing =>
      let (e', h) ← pushInAppend acc l₂
      let h := mkApp6 (.const ``congrArg [1, 1]) accType accType e' (mkListAppend acc l₂) fn h
      let lawInst ← synthInstanceDeriving (mkApp2 (.const ``LawfulFlatten c.constLevels!) α inst)
      -- `law : fn (acc ++ l₂) = fn acc ++ l₂`
      let law :=
        mkApp6 (.const ``LawfulFlatten.flatten_append c.constLevels!) α inst lawInst thing acc l₂
      return (fn.app e', ← mkEqTrans h law)
    | List.cons _ head =>
      let (e', h) ← pushInAppend acc l₂
      let h := mkApp6 (.const ``congrArg [1, 1]) accType accType e' (mkListAppend acc l₂) fn h
      -- `law : fn (acc ++ l₂) = fn acc ++ l₂`
      let law := mkApp4 (.const ``List.cons_append [0]) Nat.mkType head acc l₂
      return (fn.app e', ← mkEqTrans h law)
    | _ => fallback
  mkListAppend (a b : Expr) : Expr :=
    let accType := .app (.const ``List [0]) Nat.mkType
    mkApp6 (.const ``HAppend.hAppend [0, 0, 0]) accType accType accType
      (mkApp2 (.const ``instHAppendOfAppend [0]) accType
        (.app (.const ``List.instAppend [0]) Nat.mkType))
      a b

/-!
At the same time, this is also a good test for `.synthesize` and `derivePrerequisite`
-/

open AllGeneralClasses in
meta def deriveAllGeneralClasses : DerivingHandler :=
  let inner : DerivingHandler :=
    mkInductiveDerivingHandler ``AllGeneralClasses do
      makeInstancesUsingCtor (nonRec := true) fun
        | ``toToData
        | ``toFirstDiff
        | ``toCompareCtorIdx
        | ``toBounds
        | ``toLawfulBounds
        | ``toULiftCtorIdx
        | ``toConst
        | ``toASimilar
        | ``toBSimilar
        | ``toTransform
        | ``toAbbrevClass
        | ``toFlatten =>
          .synthesize
        | _ => .unhandled
      return true
  -- the `--` comments prevent the autoformatter from putting multiple calls into one line
  derivePrerequisite ``ToData deriveToData <| --
    derivePrerequisite ``FirstDiff deriveFirstDiff <| --
      derivePrerequisite ``CompareCtorIdx deriveCompareCtorIdx <| --
        derivePrerequisite ``Bounds deriveBounds <| --
          derivePrerequisite ``LawfulBounds deriveLawfulBounds <| --
            derivePrerequisite ``Secret deriveSecret <| --
              derivePrerequisite ``ULiftCtorIdx deriveULiftCtorIdx <| --
                derivePrerequisite ``Const deriveConst <| --
                  derivePrerequisite ``A.Similar A.deriveSimilar <| --
                    derivePrerequisite ``B.Similar B.deriveSimilar <| --
                      derivePrerequisite ``Transform deriveTransform <| --
                        derivePrerequisite ``AbbrevClass deriveAbbrevClass <| --
                          derivePrerequisite ``Flatten deriveFlatten <| --
                            inner

open OtherDataClasses in
meta def deriveOtherDataClasses : DerivingHandler :=
  let inner : DerivingHandler :=
    mkInductiveDerivingHandler ``OtherDataClasses do
      makeInstancesUsingCtor (nonRec := true) fun
        | ``toGenRandom | ``toDefault => .synthesize
        | _ => .unhandled
      return true
  derivePrerequisite ``GenRandom deriveGenRandom <| --
    derivePrerequisite ``Default deriveDefault <| --
      inner

open OtherLawClasses in
meta def deriveOtherLawClasses : DerivingHandler :=
  let inner : DerivingHandler :=
    mkInductiveDerivingHandler ``OtherLawClasses do
      makeInstancesUsingCtor (nonRec := true) fun
        | ``toAllGeneralClasses
        | ``toToDataDepLaw
        | ``toIsSmallToData
        | ``toIsInvolution
        | ``toLawfulFlatten =>
          .synthesize
        | _ => .unhandled
      return true
  derivePrerequisite ``AllGeneralClasses deriveAllGeneralClasses <| --
    derivePrerequisite ``ToDataDepLaw deriveToDataDepLaw <| --
      derivePrerequisite ``IsSmallToData deriveIsSmallToData <| --
        derivePrerequisite ``IsInvolution deriveIsInvolution <| --
          derivePrerequisite ``LawfulFlatten deriveLawfulFlatten <| --
            inner

meta initialize
  registerDerivingHandler ``ToData deriveToData
  registerDerivingHandler ``IsSmallToData deriveIsSmallToData
  registerDerivingHandler ``FirstDiff deriveFirstDiff
  registerDerivingHandler ``CompareCtorIdx deriveCompareCtorIdx
  registerDerivingHandler ``Bounds deriveBounds
  registerDerivingHandler ``LawfulBounds deriveLawfulBounds
  registerDerivingHandler ``Secret deriveSecret
  registerDerivingHandler ``ULiftCtorIdx deriveULiftCtorIdx
  registerDerivingHandler ``Const deriveConst
  registerDerivingHandler ``ToDataDepLaw deriveToDataDepLaw
  registerDerivingHandler ``GenRandom deriveGenRandom
  registerDerivingHandler ``Default deriveDefault
  registerDerivingHandler ``A.Similar A.deriveSimilar
  registerDerivingHandler ``B.Similar B.deriveSimilar
  registerDerivingHandler ``Transform deriveTransform
  registerDerivingHandler ``IsInvolution deriveIsInvolution
  registerDerivingHandler ``AbbrevClass deriveAbbrevClass
  registerDerivingHandler ``Flatten deriveFlatten
  registerDerivingHandler ``LawfulFlatten deriveLawfulFlatten
  registerDerivingHandler ``AllGeneralClasses deriveAllGeneralClasses
  registerDerivingHandler ``OtherDataClasses deriveOtherDataClasses
  registerDerivingHandler ``OtherLawClasses deriveOtherLawClasses
