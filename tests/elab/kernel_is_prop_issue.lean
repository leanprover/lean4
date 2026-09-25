import Lean

open Lean Meta

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.defProp false

namespace Issue

-- The independently qualified, closed stuck-sort gate.  Its equality is
-- separate from the open Nat equality that the history sequence will unlock.
def gateStep (x : Bool) (n : Nat) (ih : (m : Nat) → m < n → Bool) : Bool :=
  match n with
  | 0 => x
  | k + 1 => ih k (Nat.lt_succ_self k)
def gateRun (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => gateStep x m) h
opaque gateSeed : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1
def gateA := gateRun false 1 gateSeed
def gateB := gateRun false 1 (Acc.intro 1 fun _ => Acc.inv gateSeed)
def gateC := gateRun false 0 (Acc.inv gateSeed (Nat.lt_succ_self 0))
theorem gateRun_eq (x : Bool) (n : Nat) (h : Acc (· < ·) n) : gateRun x n h = x := by
  induction h with
  | intro n smaller ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [gateRun, gateStep] using ih n (Nat.lt_succ_self n)
def GateP : Prop := gateA = gateB
def GateQ : Prop := gateA = gateC
opaque gateWitness : GateQ :=
  (gateRun_eq false _ _).trans (gateRun_eq false _ _).symm
def resultSort (h : GateP) : Type := Eq.rec (motive := fun _ _ => Type) Prop h

-- The finite weak-true/eager-false control, using only tiny natural numbers.
def modeRel (_ _ : Unit) : Prop := False
abbrev ModeP := Acc modeRel ()
def modeQ : ModeP := Acc.intro () (fun _ h => False.elim h)
def modeG (p : ModeP) : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => 0) p
theorem modeG_eq_zero (p : ModeP) : modeG p = 0 := by
  cases p
  rfl

-- The first primer compares this exact identity wrapper inside a regular
-- phantom head.  No forbidden projection occurs in submitted source syntax.
abbrev preserveType (A : Type) : Type := A
def PhantomType (_ : Type) : Type := Unit

def emptyTypeRel (_ _ : Type) : Prop := False
abbrev Fiber (A : Type) : Prop := Acc emptyTypeRel A
def leaf (A : Type) : Fiber A :=
  Acc.intro A (fun _ impossible => False.elim impossible)
def fiberEq (A X : Type) : Fiber A = Fiber X :=
  propext ⟨fun _ => leaf X, fun _ => leaf A⟩
def transport (X A : Type) : Fiber X :=
  cast (fiberEq (preserveType A) X) (leaf (preserveType A))

def identityType (X : Type) (h : Fiber X) : Type :=
  Acc.rec (motive := fun _ _ => Type) (fun A _ _ => A → A) h
noncomputable def identityValue (X : Type) (h : Fiber X) : identityType X h :=
  Acc.rec (motive := fun X h => identityType X h)
    (fun A _ _ => fun value : A => value) h
theorem identityType_eq (X : Type) (h : Fiber X) : identityType X h = (X → X) := by
  cases h
  rfl
theorem identityValue_heq (X : Type) (h : Fiber X) :
    HEq (identityValue X h) (fun value : X => value) := by
  cases h
  rfl
theorem emptyFalse (value : Empty) : False := Empty.elim value

private def natExpr : Expr := mkConst ``Nat
private def modePropExpr : Expr := mkConst ``ModeP
private def trueExpr : Expr := mkConst ``True
private def falseExpr : Expr := mkConst ``False
private def zeroExpr : Expr := mkRawNatLit 0
private def eqExpr (type left right : Expr) (level : Level) : Expr :=
  mkApp3 (mkConst ``Eq [level]) type left right
private def reflExpr (type value : Expr) (level : Level) : Expr :=
  mkApp2 (mkConst ``Eq.refl [level]) type value
private def eqNatExpr (left right : Expr) : Expr := eqExpr natExpr left right Level.one
private def reflNatExpr (value : Expr) : Expr := reflExpr natExpr value Level.one
private def addZeroExpr (value : Expr) : Expr := mkApp2 (mkConst ``Nat.add) value zeroExpr
private def openEndpointExpr (p : Expr) : Expr := addZeroExpr (mkApp (mkConst ``modeG) p)
private def closedEndpointExpr : Expr := addZeroExpr (mkApp (mkConst ``modeG) (mkConst ``modeQ))

private def ownerName : Name := `Issue.Owner
private def ownerPropName : Name := `Issue.proposition
private def endpointUseName : Name := `Issue.endpointUse
private def opaqueProofName : Name := `Issue.opaqueEndpoint
private def delayedName : Name := `Issue.delayedOwner
private def seedUseName : Name := `Issue.projectionSeedUse
private def ownerPropExpr : Expr := mkConst ownerPropName
private def ownerCtorExpr (A : Expr) : Expr :=
  mkApp2 (mkConst (.str ownerName "mk")) (mkConst ``gateWitness) A

private def theoremDecl (name : Name) (type value : Expr) : Declaration :=
  .thmDecl {name, levelParams := [], type, value}
private def definitionDecl (name : Name) (type value : Expr)
    (hints : ReducibilityHints := .regular 0) : Declaration :=
  .defnDecl {name, levelParams := [], type, value, hints, safety := .safe}
private def checkBudget (env : Environment) (decl : Declaration) :
    CoreM (Except Kernel.Exception Environment) := do
  let task := Task.spawn (fun _ => env.addDeclCore 1800000 10000 decl none)
    Task.Priority.dedicated
  return task.get
private def checked (env : Environment) (decl : Declaration) : CoreM Environment := do
  match ← checkBudget env decl with
  | .ok next => return next
  | .error error => throwError "checked setup {decl.getNames}: {error.toMessageData (← getOptions)}"

private def consumerDecl (name : Name) (fieldType : Expr) : Declaration :=
  definitionDecl name
    (mkForall `p .default modePropExpr (mkForall `witness .default fieldType trueExpr))
    (mkLambda `p .default modePropExpr
      (mkLambda `witness .default fieldType (mkConst ``True.intro)))
private def eagerProofExpr (proofType proof : Expr) : Expr :=
  mkApp2 (mkConst ``eagerReduce [Level.zero]) proofType proof
private def endpointSeedExpr (p : Expr) : Expr :=
  mkApp2 (mkConst endpointUseName) p (reflNatExpr closedEndpointExpr)

private def rawDelayExpr (p value : Expr) : Expr :=
  let left := openEndpointExpr p
  let motive := mkLambda `endpoint .default natExpr <|
    mkLambda `equality .default
      (eqNatExpr (left.liftLooseBVars 0 1) (.bvar 0)) ownerPropExpr
  mkAppN (mkConst ``Eq.rec [Level.zero, Level.one])
    #[natExpr, left, motive, value, closedEndpointExpr, mkApp (mkConst opaqueProofName) p]
private def sourceMajorExpr (p A : Expr) : Expr :=
  mkApp2 (mkConst delayedName) p (ownerCtorExpr A)

private def phantomExpr (A : Expr) : Expr :=
  mkApp (mkConst ``PhantomType) (mkApp (mkConst ``preserveType) A)
private def proofFunctionTypeExpr : Expr :=
  mkForall `value .default (phantomExpr (mkConst ``Empty)) trueExpr
private def ownerRecExpr (resultType minor major : Expr) : Expr :=
  mkAppN (mkConst (mkRecName ownerName)) #[mkConst ``gateWitness,
    mkLambda `major .default ownerPropExpr resultType, minor, major]
private def proofFunctionExpr (p A : Expr) : Expr :=
  let minor := mkLambda `A .default (mkSort 1) <|
    mkLambda `value .default (phantomExpr (.bvar 0)) (mkConst ``True.intro)
  ownerRecExpr proofFunctionTypeExpr minor (sourceMajorExpr p A)
private def projectionSeedTypeExpr (p : Expr) : Expr :=
  eqExpr proofFunctionTypeExpr
    (proofFunctionExpr p (mkConst ``Empty))
    (proofFunctionExpr p (mkConst ``Unit)) Level.zero
private def projectionSeedExpr (p : Expr) : Expr :=
  let left := proofFunctionExpr p (mkConst ``Empty)
  let reflType := eqExpr proofFunctionTypeExpr left left Level.zero
  mkApp2 (mkConst seedUseName) p
    (eagerProofExpr reflType (reflExpr proofFunctionTypeExpr left Level.zero))

private def packetExpr (X p A : Expr) : Expr :=
  let resultType := mkApp (mkConst ``Fiber) X
  ownerRecExpr resultType (mkApp (mkConst ``transport) X) (sourceMajorExpr p A)
private def identityExpr (X p A : Expr) : Expr :=
  mkApp2 (mkConst ``identityValue) X (packetExpr X p A)
private def unitApplicationExpr (p : Expr) : Expr :=
  mkApp (identityExpr (mkConst ``Unit) p (mkConst ``Unit)) (mkConst ``Unit.unit)
private def badEmptyExpr (p : Expr) : Expr :=
  mkApp (identityExpr (mkConst ``Empty) p (mkConst ``Empty)) (unitApplicationExpr p)
private def sequenceExpr (values : Array Expr) (body : Expr) : Expr :=
  values.foldr (fun value body =>
    mkLet `historyStep trueExpr value (body.liftLooseBVars 0 1)) body
private def primedExpr (p body : Expr) : Expr :=
  sequenceExpr #[projectionSeedExpr p, endpointSeedExpr p] body
private def closedAtModeExpr (resultType body : Expr) : Expr × Expr :=
  (mkForall `p .default modePropExpr resultType, mkLambda `p .default modePropExpr body)

private def expectAccepted (env : Environment) (label : String) (decl : Declaration) :
    CoreM Unit := do
  match ← checkBudget env decl with
  | .ok next =>
    let axioms ← withEnv next (collectAxioms decl.getNames.head!)
    unless axioms.all (fun a => a == ``propext) do
      throwError "{label}: unexpected axioms {axioms}"
    logInfo m!"HISTORY CONTROL {label}: accepted; axioms={axioms}"
  | .error error => throwError "{label}: {error.toMessageData (← getOptions)}"

/--
error: eager-projection-seed: (kernel) type expected
  resultSort gateWitness
-/
#guard_msgs in
run_meta do
  let mut env ← getEnv
  unless (Kernel.isDefEq env {} (mkConst ``GateP) (mkConst ``GateQ)).toOption == some true do
    throwError "independent owner sort gate changed"
  let gp := mkConst ``GateP
  let ownerType := mkForall `h .default gp (mkApp (mkConst ``resultSort) (.bvar 0))
  let ctorType := mkForall `h .default gp <|
    mkForall `A .default (mkSort 1) (mkApp (mkConst ownerName) (.bvar 1))
  env ← checked env (.inductDecl [] 1 [{
    name := ownerName, type := ownerType,
    ctors := [{name := .str ownerName "mk", type := ctorType}]
  }] false)
  env ← checked env <| definitionDecl `Issue.asProp
    (mkForall `h .default gp (mkSort 0))
    (mkLambda `h .default gp (mkApp (mkConst ownerName) (.bvar 0))) .abbrev
  env ← checked env <| definitionDecl ownerPropName (mkSort 0)
    (mkApp (mkConst `Issue.asProp) (mkConst ``gateWitness)) .abbrev
  let .some (.recInfo recInfo) := env.find? (mkRecName ownerName)
    | throwError "missing checked owner recursor"
  unless recInfo.levelParams.isEmpty && recInfo.numParams == 1 && recInfo.numIndices == 0 do
    throwError "owner recursor is not the expected Prop-only unindexed recursor"

  env ← checked env <| consumerDecl endpointUseName
    (eqNatExpr (openEndpointExpr (.bvar 0)) closedEndpointExpr)
  env ← checked env <| .opaqueDecl {
    name := opaqueProofName, levelParams := [],
    type := mkForall `p .default modePropExpr
      (eqNatExpr (openEndpointExpr (.bvar 0)) closedEndpointExpr),
    value := mkLambda `p .default modePropExpr (reflNatExpr closedEndpointExpr),
    isUnsafe := false }
  env ← checked env <| definitionDecl delayedName
    (mkForall `p .default modePropExpr (mkForall `value .default ownerPropExpr ownerPropExpr))
    (mkLambda `p .default modePropExpr <|
      mkLambda `value .default ownerPropExpr (rawDelayExpr (.bvar 1) (.bvar 0)))
  env ← checked env <| consumerDecl seedUseName (projectionSeedTypeExpr (.bvar 0))

  let p := Expr.bvar 0
  let (controlType, seedValue) := closedAtModeExpr trueExpr
    (sequenceExpr #[projectionSeedExpr p] (mkConst ``True.intro))
  expectAccepted env "eager-projection-seed" <|
    theoremDecl `Issue.controlSeed controlType seedValue
  let (_, unlockValue) := closedAtModeExpr trueExpr
    (primedExpr p (mkConst ``True.intro))
  expectAccepted env "seed-then-unlock" <|
    theoremDecl `Issue.controlUnlock controlType unlockValue
  let (unitType, unitValue) := closedAtModeExpr (mkConst ``Unit)
    (primedExpr p (unitApplicationExpr p))
  expectAccepted env "honest-Unit-endpoint" <|
    definitionDecl `Issue.controlUnit unitType unitValue .abbrev

  let (badType, badValue) := closedAtModeExpr falseExpr <|
    primedExpr p (mkApp (mkConst ``emptyFalse) (badEmptyExpr p))
  let badName := `Issue.forallFalse
  match ← checkBudget env (theoremDecl badName badType badValue) with
  | .error error =>
    logInfo m!"HISTORY TARGET REJECT: {error.toMessageData (← getOptions)}"
    let .ok inferred := Kernel.check env {} unitValue
      | throwError "full checked Unit diagnostic failed"
    logInfo m!"HISTORY UNIT INFERRED: {reprStr inferred}"
    setEnv env
    logInfo "TRANSPORTED HISTORY COMPLETE: candidate rejected; no False"
  | .ok next =>
    env ← checked next <| theoremDecl `Issue.contradiction falseExpr
      (mkApp (mkConst badName) (mkConst ``modeQ))
    setEnv env
    let .some (.thmInfo info) := env.find? `Issue.contradiction
      | throwError "missing checked False theorem"
    unless info.levelParams.isEmpty && info.type == falseExpr &&
        !info.value.hasFVar && !info.value.hasMVar && !info.value.hasLooseBVars do
      throwError "False theorem is not closed and monomorphic"
    let .ok inferred := Kernel.check env {} info.value
      | throwError "stored False proof fails a fresh full check"
    unless inferred == falseExpr do throwError "stored proof's inferred type is not literal False"
    let axioms ← collectAxioms `Issue.contradiction
    unless axioms.all (fun a => a == ``propext) do
      throwError "unexpected False axioms: {axioms}"
    logInfo m!"CHECKED TRANSPORTED HISTORY FALSE: axioms={axioms}"
    logInfo "TRANSPORTED HISTORY COMPLETE: checked closed False"

end Issue
