/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.CoreC
public import Lean.Kernel.InLean.NatOpPins
public import Lean.Kernel.InLean.Push

/-!
# InLean: the declaration step

Twin of `ConLeche.Cached.ParsedC`'s `checkDeclC` over
`Lean.Declaration`, with the shared checks it runs
(`ConLeche.Kernel.CheckerBase`'s `checkConstantVal`,
`ConLeche.Kernel.DeclCheck`'s guards and pins): the constant checks,
the value checks, the certified `Nat` operations (`certifyNatEqs`,
`checkDivModPinF`), the compiler-trust opaques (`checkReducePinF`), the
pinned axioms (`stdAxiomOkF`, `trustCompilerOkF`, `ofReduceAxOkF`) and the
quotient package (`checkQuotRecordC`).

What a declaration adds is returned, not pushed (`Added`); the caller adds
it (`Lean.Kernel.InLean.AddDecl`).  A value is checked in the environment before
its declaration's constants, as con-leche's fold checks a record at the
view below it.

Beyond con-leche, as the official kernel does (`environment.cpp`):
`unsafe` axioms, definitions and opaques, `partial` definitions and
`mutualDefnDecl`, each checked at the declaration's safety (`FEnv.safety`)
and outside any proof.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- The checker's configuration. -/
structure Config where
  mode : CheckMode := .verified
  /-- The axiom policy (`FEnv.coreAxioms`): `false` is con-leche's (only the
  pinned axioms; `sorryAx` is no constant), `true` the official kernel's. -/
  coreAxioms : Bool := false
  /-- **A pinned `Nat` operation whose certification declines is accepted**,
  and the fast path, which fires by name, then fires on it.  The prelude
  is assumed good: the official kernel fires by name with no certificate,
  and in a replay in dependency order an operation can arrive before what
  its certificates read.  `false` is con-leche's policy. -/
  uncertifiedNatOps : Bool := true
  /-- The official kernel's resource limits (`Limits`; by default none but
  the numerals' size). -/
  limits : Limits := {}

/-- What a declaration adds: its constants, in order, and whether it is the
quotient package (official's `quotInit` flag). -/
structure Added where
  consts : Array ConstantInfo := #[]
  quot : Bool := false

section
variable (mode : CheckMode)

/-- The core's entry points at the plain tower: the knot at the recursion
limit's level, which master's cached stages call directly (`opInfer` is
master's `opI`, `opWhnf` its `opW`, `opSort` its `opSIxC`). -/
@[inline] def opInfer (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Expr :=
  inferI mode fe false (fe.limits.recDepth.getD checkFuel) false d e
@[inline] def opDefeq (fe : FEnv) (d : Nat) (a b : Expr) : CheckCM Bool :=
  defeqI mode fe false (fe.limits.recDepth.getD checkFuel) d a b
@[inline] def opSort (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Level :=
  ensureSortI mode fe false (fe.limits.recDepth.getD checkFuel) d e
@[inline] def opWhnf (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Expr :=
  whnfI mode fe false (fe.limits.recDepth.getD checkFuel) d e

end

/-! ## Syntactic guards -/

/-- Twin of `unresolvedConstsErrorL`; a constant the check does not see is
named (`unseenConstError`). -/
def unresolvedConstsErrorL (fe : FEnv) (strOk : Bool) (where_ : String) (e : Expr) : CheckError :=
  if !strOk && EO.any (fun x => match x with | .lit (.strVal _) => true | _ => false) e then
    .notImplemented "string literals before the String support declarations"
  else
    let cs := EO.usedConstants e
    if cs.contains sorryAxName then
      .notImplemented s!"use of the sorryAx axiom in {where_}"
    else match cs.find? (fun c => (fe.find? c).isNone) with
      | some c => unseenConstError fe c
      | none => .invalid s!"unknown constant in {where_}"

/-- Twin of `Expr.constsResolve` on a term without free variables: every
constant and every projection's structure stored, a literal's support
declarations stored. -/
def constsResolve (fe : FEnv) (e : Expr) : Bool :=
  !EO.any (fun
    | .const c _ => (fe.find? c).isNone
    | .proj s _ _ => (fe.find? s).isNone
    | .lit (.natVal _) => !fe.natLit
    | .lit (.strVal _) => !fe.strLit
    | _ => false) e

/-- Twin of the syntactic gates of `checkConstantValC`/`checkDefnValCI` on
one term (its context message, `pre` then the name, is built only on the
error path): closed, no free variable or metavariable, its level parameters
declared, its constants resolving. -/
def checkTermWF (fe : FEnv) (pre : String) (n : Name) (lps : List Name) (e : Expr) : CheckCM Unit := do
  if e.hasLooseBVars then throw (.invalid s!"loose bound variable in {pre}{n}")
  if e.hasFVar then throw (.invalid s!"unexpected free variable in {pre}{n}")
  if e.hasMVar then throw (.invalid s!"unexpected metavariable in {pre}{n}")
  if e.hasLevelParam then
    unless (EO.levelParams e).all lps.contains do
      throw (.invalid s!"undeclared universe parameter in {pre}{n}")
  unless constsResolve fe e do
    throw (unresolvedConstsErrorL fe fe.strLit s!"{pre}{n}" e)

/-! ## The literal names' shapes (twin of `litShapeOk`) -/

/-- A stored type compared with a shape, `mdata` ignored. -/
@[inline] def tyIs (ty shape : Expr) : Bool := ty == shape

def natTy : Expr := .const natName []
def charTy : Expr := .const charName []

/-- Twin of `litShapeOk`, at a declaration's name, level parameters and type. -/
def litShapeOk (n : Name) (lps : List Name) (ty : Expr) : Bool :=
  if n == natName then lps.isEmpty && tyIs ty (.sort (.succ .zero))
  else if n == natZeroName then lps.isEmpty && tyIs ty natTy
  else if n == natSuccName then lps.isEmpty && tyIs ty (.forallE `n natTy natTy .default)
  else if n == stringName then lps.isEmpty && tyIs ty (.sort (.succ .zero))
  else if n == charName then lps.isEmpty && tyIs ty (.sort (.succ .zero))
  else if n == charOfNatName then lps.isEmpty && tyIs ty (.forallE `n natTy charTy .default)
  else if n == stringOfListName then
    lps.isEmpty && tyIs ty (.forallE `l (.app (.const listName [.zero]) charTy)
      (.const stringName []) .default)
  else if n == listName then
    lps.length == 1 &&
      tyIs ty (.forallE `α (.sort (.succ (.param lps[0]!))) (.sort (.succ (.param lps[0]!))) .default)
  else if n == listNilName then
    lps.length == 1 &&
      tyIs ty (.forallE `α (.sort (.succ (.param lps[0]!)))
        (.app (.const listName [.param lps[0]!]) (.bvar 0)) .implicit)
  else if n == listConsName then
    lps.length == 1 &&
      let l := Expr.app (.const listName [.param lps[0]!])
      tyIs ty (.forallE `α (.sort (.succ (.param lps[0]!)))
        (.forallE `head (.bvar 0) (.forallE `tail (l (.bvar 1)) (l (.bvar 2)) .default) .default)
        .implicit)
  else true

/-- Twin of `natOpName`. -/
def natOpName (n : Name) : Bool := natOpNames.contains n || natDivModNames.contains n

/-! ## The constant and value checks -/

section
variable (mode : CheckMode)

/-- Twin of `checkConstantValC`; the name's freshness read off the
environment itself, as official's `check_name` (`FEnv.find?` hides
constants a check does not see). -/
def checkConstantValC (fe : FEnv) (cv : ConstantVal) (allowOp : Bool := false) :
    CheckCM Unit := do
  if (fe.env.find? cv.name).isSome then throw (alreadyDeclared cv.name)
  if natOpName cv.name && !allowOp then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk cv.name cv.levelParams cv.type do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless namesNodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  checkTermWF fe "type of " cv.name cv.levelParams cv.type
  let stype ← opInfer mode fe 0 cv.type
  let _u ← opSort mode fe 0 stype

/-- Twin of the value half of `checkDefnValCI`/`checkThmValCI`/`checkOpaqueValCI`. -/
def checkValueC (fe : FEnv) (kind : String) (n : Name) (lps : List Name) (ty v : Expr) :
    CheckCM Unit := do
  checkTermWF fe "value of " n lps v
  let vt ← opInfer mode fe 0 v
  unless ← opDefeq mode fe 0 vt ty do throw (.invalid s!"type mismatch in {kind} {n}")

/-! ## The certified `Nat` operations -/

/-- Twin of `natOpCodF`. -/
def natOpCod (fe : FEnv) (c : Name) (e : Expr) : Bool :=
  if c == natBeqName || c == natBleName then
    tyIs e (.const boolName []) && (match fe.find? boolName with
      | some ci => boolPin.matches ci
      | none => false)
  else tyIs e natTy

/-- Twin of `natOpTyPinnedF`. -/
def natOpTyPinned (fe : FEnv) (c : Name) (ty : Expr) : Bool :=
  if c == natPredName then
    match EO.stripTop (ty) with
    | .forallE _ dom body _ => tyIs dom natTy && natOpCod fe c body
    | _ => false
  else
    match EO.stripTop (ty) with
    | .forallE _ dom b _ =>
      match EO.stripTop b with
      | .forallE _ dom2 body _ => tyIs dom natTy && tyIs dom2 natTy && natOpCod fe c body
      | _ => false
    | _ => false

/-- Twin of `natOpStoredOkF`. -/
def natOpStoredOk (fe : FEnv) (n : Name) : Bool :=
  match fe.find? n with
  | some (.defnInfo v) => v.levelParams.isEmpty && natOpTyPinned fe n (EO.stripMData v.type)
  | _ => false

/-- Twin of `natOpGuardF` (its `natLitSupported` conjunct: the `Nat` names'
shapes, which their own checks fix, `litShapeOk`). -/
def natOpGuard (fe : FEnv) (c : Name) : Bool :=
  fe.natLit &&
  (natOpDeps c).all (fun n => match fe.find? n with
    | some (.defnInfo v) => v.levelParams.isEmpty
    | _ => false) &&
  (if c == natBeqName || c == natBleName || natDivModNames.contains c then
    (match fe.find? boolTrueName with
      | some ci => ci.levelParams.isEmpty && tyIs ci.type (.const boolName [])
      | none => false) &&
    (match fe.find? boolFalseName with
      | some ci => ci.levelParams.isEmpty && tyIs ci.type (.const boolName [])
      | none => false)
   else true)

/-- The two `Nat` variables of the certificates (con-leche's `fvar 0`,
`fvar 1` of type `Nat`). -/
def natVars : CheckCM (Expr × Expr) := do
  return (← mkFVarM 0 natTy, ← mkFVarM 1 natTy)

/-- Twin of `certifyNatEqs` (at depth 2). -/
def certifyNatEqs (fe : FEnv) : List (Expr × Expr) → CheckCM Bool
  | [] => pure true
  | (l, r) :: rest => do
    if ← opDefeq mode fe 2 l r then certifyNatEqs fe rest else pure false

/-- Twin of `divModEnvGuardF`. -/
def divModEnvGuard (fe2 : FEnv) (c : Name) : Bool :=
  natOpGuard fe2 c && (natOpDeps c).all (natOpStoredOk fe2) &&
  (fe2.find? eqName).isSome &&
  (match fe2.find? boolTrueName with
    | some ci => tyIs ci.type (.const boolName [])
    | none => false) &&
  (match fe2.find? boolFalseName with
    | some ci => tyIs ci.type (.const boolName [])
    | none => false)

/-- Twin of `divModPinGuardC`. -/
def divModPinGuard (fe : FEnv) (op : PinOp) : Bool :=
  !op.pin.hasLooseBVars && !op.pin.hasFVar && !op.pin.hasLevelParam && constsResolve fe op.pin &&
  op.typePins.all fun (n, ty) =>
    match fe.find? n with
    | some ci => !ci.type.hasFVar && !ty.hasLooseBVars && !ty.hasFVar && constsResolve fe ty
    | none => false

/-- Twin of `divModCertGuardC`: at the certificate's proof `sp` with the
operation substituted (`checkDivModPinLoop` substitutes each once). -/
def divModCertGuard (fe : FEnv) (c : Name) (annVal : Expr) (hyps : List Expr)
    (eqE sp : Expr) : Bool :=
  !sp.hasLooseBVars && !sp.hasFVar && !sp.hasLevelParam && constsResolve fe sp &&
    (hyps.map (substConst0 c annVal)).all (constsResolve fe) &&
    constsResolve fe (substConst0 c annVal eqE)

/-- Twin of `checkDivModCertsC` (at depth 4: the two variables and the
hypotheses), at the substituted proofs. -/
def checkDivModCerts (fe : FEnv) (c : Name) (annVal : Expr) (x y : Expr) :
    List (List Expr × Expr) → List Expr → CheckCM Bool
  | [], [] => pure true
  | (hyps, eqE) :: srest, sp :: prest => do
    if divModCertGuard fe c annVal hyps eqE sp then
      let hs := hyps.map (substConst0 c annVal)
      let base := mkApp2 sp x y
      let applied ← match hs with
        | [h1] => pure (.app base (← mkFVarM 2 h1))
        | [h1, h2] => pure (mkApp2 base (← mkFVarM 2 h1) (← mkFVarM 3 h2))
        | _ => pure base
      let tp ← opInfer mode fe 4 applied
      if ← opDefeq mode fe 4 tp (substConst0 c annVal eqE) then
        checkDivModCerts fe c annVal x y srest prest
      else pure false
    else pure false
  | _, _ => pure false

/-- Twin of `checkTypePinsC`. -/
def checkTypePins (fe : FEnv) : List (Name × Expr) → CheckCM Bool
  | [] => pure true
  | (n, ty) :: rest => do
    let stored := match fe.find? n with
      | some ci => ci.type
      | none => .sort .zero
    if ← opDefeq mode fe 0 stored ty then checkTypePins fe rest else pure false

/-- Twin of `checkDivModPinAtC`: the type pins, then the pin, then the
certificates at the substituted proofs `sps`. -/
def checkDivModPinAt (fe : FEnv) (c : Name) (value' x y : Expr) (op : PinOp) (sps : List Expr) :
    CheckCM Bool := do
  if ← checkTypePins mode fe op.typePins.toList then
    if ← opDefeq mode fe 0 value' op.pin then
      checkDivModCerts mode fe c value' x y (divModCertStmts x y c) sps
    else pure false
  else pure false

/-- Twin of `checkDivModPinLoopC`: each variant's proofs substituted once.
A variant's entry for `c` is decoded here, when it is tried. -/
def checkDivModPinLoop (fe : FEnv) (c : Name) (value' x y : Expr) :
    List PinSet → List String → CheckCM Unit
  | [], tried =>
    throw (.notImplemented s!"unsupported Nat.div/mod spelling ({c}: no pin variant matched — \
      {String.intercalate "; " tried})")
  | ps :: rest, tried =>
    match ps.op? c with
    | .error e => throw (.internal s!"the Nat-operation pin dump {ps.toolchain} does not decode: {e}")
    | .ok none => checkDivModPinLoop fe c value' x y rest (tried ++ [s!"{ps.toolchain}: no pin"])
    | .ok (some op) =>
      let sps := op.proofs.toList.map (substConstAll c value')
      if divModPinGuard fe op && ((divModCertStmts x y c).zip sps).all
          (fun p => divModCertGuard fe c value' p.1.1 p.1.2 p.2) then do
        if ← checkDivModPinAt mode fe c value' x y op sps then pure ()
        else
          checkDivModPinLoop fe c value' x y rest (tried ++ [s!"{ps.toolchain}: a type pin or \
            the pin not definitionally equal, or a certificate failed"])
      else
        checkDivModPinLoop fe c value' x y rest
          (tried ++ [s!"{ps.toolchain}: pin or certificate ground constants absent"])

/-- Twin of `checkDivModPinC` over the committed pin variants. -/
def checkDivModPin (fe fe2 : FEnv) (c : Name) (value' : Expr) : CheckCM Unit := do
  unless divModEnvGuard fe2 c do
    throw (.notImplemented s!"unsupported Nat.div/mod environment ({c})")
  let (x, y) ← natVars
  checkDivModPinLoop mode fe c value' x y pinSets.toList []

/-! ## The compiler-trust opaques and axioms -/

/-- A pinned family's inductive type, as master's guards read it: stored as
an inductive (`some (.indInfo cv _)`) matching the pin. -/
def pinFoundInd (fe : FEnv) (p : Pin) : Bool :=
  match fe.find? p.name with
  | some ci@(.inductInfo _) => p.matchesExact ci
  | _ => false

/-- A pinned family's constructor, as master's guards read it: stored as a
constructor with the pinned counts (`some (.ctorInfo cv nP nF)`) matching the
pin. -/
def pinFoundCtor (fe : FEnv) (p : Pin) (nP nF : Nat) : Bool :=
  match fe.find? p.name with
  | some ci@(.ctorInfo v) => v.numParams == nP && v.numFields == nF && p.matchesExact ci
  | _ => false

/-- A pinned family's recursor, as master's guards read it: stored as a
recursor with the pinned major index and rule prefix (`some (.recInfo cv mI rP _ _)`,
the counts con-leche's record carries) matching the pin. -/
def pinFoundRec (fe : FEnv) (p : Pin) (mI rP : Nat) : Bool :=
  match fe.find? p.name with
  | some ci@(.recInfo v) =>
    v.numParams + v.numMotives + v.numMinors + v.numIndices == mI &&
      v.numParams + v.numMotives + v.numMinors == rP && p.matchesExact ci
  | _ => false

/-- Twin of `reduceElemOkF`: `Nat` resp. `Bool` stored as an inductive
matching its pin. -/
def reduceElemOk (fe : FEnv) (c : Name) : Bool :=
  if c == reduceNatName then pinFoundInd fe natPin
  else pinFoundInd fe boolPin

/-- Twin of `reduceStoredOkF` (Lean stores the opaque as an opaque). -/
def reduceStoredOk (fe : FEnv) (c : Name) : Bool :=
  match fe.find? c with
  | some ci@(.opaqueInfo _) => (reduceOpPin c).matchesExact ci
  | some ci@(.axiomInfo _) => (reduceOpPin c).matchesExact ci
  | _ => false

/-- Twin of `reducePinGuardC`: the pin closed, without free variables or
level parameters, its constants stored. -/
def reducePinGuard (fe : FEnv) (c : Name) : Bool :=
  !(reduceDeclPin c).hasLooseBVars && !(reduceDeclPin c).hasFVar &&
  !(reduceDeclPin c).hasLevelParam && constsResolve fe (reduceDeclPin c)

/-- Twin of `checkReducePinC`. -/
def checkReducePin (fe fe2 : FEnv) (c : Name) (value : Expr) : CheckCM Unit := do
  unless reduceStoredOk fe2 c && reduceElemOk fe c do
    throw (.notImplemented s!"unsupported compiler-trust opaque declaration ({c})")
  unless reducePinGuard fe c do
    throw (.notImplemented
      s!"unsupported compiler-trust opaque spelling ({c}: pin ground constants absent)")
  unless ← opDefeq mode fe 0 value (reduceDeclPin c) do
    throw (.notImplemented s!"unsupported compiler-trust opaque spelling ({c})")
  let x ← mkFVarM 0 (reduceElemTy c)
  unless ← opDefeq mode fe 1 (.app value x) x do
    throw (.internal s!"pinned compiler-trust opaque is not the identity ({c})")

/-- Twin of `stdAxiomOkF`: the families' kinds and counts read as master's. -/
def stdAxiomOk (fe : FEnv) (n : Name) (lps : List Name) (ty : Expr) : Bool :=
  let me : Pin → Bool := fun p => p.matchesDeclExact n lps ty
  if n == propextName then
    (fe.find? eqName).isSome && pinFoundInd fe iffPin && pinFoundCtor fe iffIntroPin 2 2 &&
      pinFoundRec fe iffRecPin 4 4 && me propextPin
  else if n == choiceName then
    pinFoundInd fe nonemptyPin && pinFoundCtor fe nonemptyIntroPin 1 1 &&
      pinFoundRec fe nonemptyRecPin 3 3 && me choicePin
  else false

/-- Twin of `trustCompilerOkF`: `True` an inductive, `True.intro` a constructor
with no parameter and no field. -/
def trustCompilerOk (fe : FEnv) (n : Name) (lps : List Name) (ty : Expr) : Bool :=
  pinFoundInd fe truePin && pinFoundCtor fe trueIntroPin 0 0 &&
    trustCompilerPin.matchesDeclExact n lps ty

/-- Twin of `ofReduceAxOkF`. -/
def ofReduceAxOk (fe : FEnv) (n : Name) (lps : List Name) (ty : Expr) : Bool :=
  let c := ofReduceOp n
  (fe.find? eqName).isSome && reduceElemOk fe c && reduceStoredOk fe c &&
    (ofReducePin n).matchesDeclExact n lps ty

/-! ## The quotient package -/

/-- Twin of `quotPredsOk`: what the package's types mention, stored before
it.  Lean declares the four quotient constants at once (`quotDecl`), so
the slots' mutual needs are met by the declaration itself; what is read
of the environment is `Eq`. -/
def quotPredsOk (fe : FEnv) : Bool := (fe.find? eqName).isSome

/-- Twin of `checkQuotRecordC` for Lean's `quotDecl`: the four quotient
constants, the pins at the official kernel's level names (`quot.cpp`).  A
quotient declaration in an environment whose quotient package is declared
adds nothing, as official's `environment::add_quot` (`Lean.Replay` sends one
per quotient constant). -/
def checkQuotC (fe : FEnv) : CheckCM Added := do
  if quotInitialized fe.env then return { quot := true }
  unless quotPredsOk fe do
    throw (.notImplemented "quotient declaration before what it needs")
  for p in [quotPin, quotMkPin, quotLiftPin, quotIndPin] do
    if (fe.env.find? p.name).isSome then throw (alreadyDeclared p.name)
  let mk (p : Pin) (k : QuotKind) : ConstantInfo :=
    .quotInfo { name := p.name, levelParams := p.lps, type := p.type, kind := k }
  return { consts := #[mk quotPin .type, mk quotMkPin .ctor, mk quotLiftPin .lift,
                       mk quotIndPin .ind], quot := true }

/-! ## The declaration kinds -/

/-- A definition (twin of `checkDeclC`'s `defnDecl` arm, the certified
`Nat` operations included; official `add_definition` for an unsafe one,
whose own constant is in the environment its value is checked in). -/
def checkDefnC (cfg : Config) (fe : FEnv) (v : DefinitionVal) : CheckCM Added := do
  let ci := ConstantInfo.defnInfo v
  if v.safety == .unsafe then
    let fe := fe.withSafety .unsafe
    checkConstantValC mode fe v.toConstantVal true
    checkValueC mode (fe.push ci) "definition" v.name v.levelParams
      v.type v.value
    return { consts := #[ci] }
  checkConstantValC mode fe v.toConstantVal true
  checkValueC mode fe "definition" v.name v.levelParams v.type v.value
  if natOpNames.contains v.name || natDivModNames.contains v.name then
    let fe2 : FEnv := fe.push ci
    let certify : CheckCM Unit := do
      if natOpNames.contains v.name then
        unless natOpGuard fe2 v.name && (natOpDeps v.name).all (natOpStoredOk fe2) do
          throw (.notImplemented s!"nonstandard structural Nat operation environment ({v.name})")
        let (x, y) ← natVars
        let eqs := (natOpEquations x y v.name).map fun (l, r) =>
          (substConst0 v.name v.value l, substConst0 v.name v.value r)
        unless ← certifyNatEqs mode fe eqs do
          throw (.notImplemented s!"nonstandard structural Nat operation ({v.name})")
      if natDivModNames.contains v.name then
        checkDivModPin mode fe fe2 v.name v.value
    if cfg.uncertifiedNatOps then
      tryCatch certify fun e => match e with
        | .notImplemented _ => pure ()
        | _ => throw e
    else certify
  return { consts := #[ci] }

/-- A theorem (twin of `checkThmValCI`; stored with its value, which the core
never unfolds). -/
def checkThmC (fe : FEnv) (v : TheoremVal) : CheckCM Added := do
  checkConstantValC mode fe v.toConstantVal
  let u ← opSort mode fe 0 (← opInfer mode fe 0 v.type)
  unless ← liftFueled "level comparison" (Lvl.isEquiv u .zero) do
    throw (.invalid s!"type of theorem {v.name} is not a proposition")
  checkValueC mode fe "theorem" v.name v.levelParams v.type v.value
  return { consts := #[.thmInfo v] }

/-- An opaque (twin of `checkOpaqueValCI`; official `add_opaque` checks at
the safe safety even for an unsafe one). -/
def checkOpaqueC (fe : FEnv) (v : OpaqueVal) : CheckCM Added := do
  checkConstantValC mode fe v.toConstantVal
  checkValueC mode fe "opaque" v.name v.levelParams v.type v.value
  let ci := ConstantInfo.opaqueInfo v
  if reduceOpNames.contains v.name then
    checkReducePin mode fe (fe.push ci) v.name v.value
  return { consts := #[ci] }

/-- An axiom (twin of `checkDeclC`'s `axiomDecl` arm).  `sorryAx` is added to
Lean's environment (the elaborator needs it), and is no constant unless
`coreAxioms` (`FEnv.find?`). -/
def checkAxiomC (cfg : Config) (fe : FEnv) (v : AxiomVal) : CheckCM Added := do
  let ci := ConstantInfo.axiomInfo v
  if v.name == quotSoundName then
    -- twin of `checkQuotRecordC fe .sound`: the pin, what it needs, then
    -- `installBasisDeclF`'s freshness (official's `check_name`)
    unless quotSoundHit v.name v.levelParams v.type do
      throw (.notImplemented "quotient soundness axiom mismatch")
    unless quotPredsOk fe && (fe.find? quotName).isSome && (fe.find? quotMkName).isSome do
      throw (.notImplemented "quotient declaration before what it needs")
    if (fe.env.find? v.name).isSome then throw (alreadyDeclared v.name)
    return { consts := #[ci] }
  let fe' := fe.withSafety (if v.isUnsafe then .unsafe else .safe)
  -- the official policy (`coreAxioms`) admits an axiom at a certified `Nat`
  -- operation's name: the elaborator adds a recursive definition as an axiom
  -- while it elaborates it (`addAsAxiom`); any other declaration there is checked
  checkConstantValC mode fe' v.toConstantVal (allowOp := fe.coreAxioms)
  if v.isUnsafe then return { consts := #[ci] }
  if stdAxiomOk fe v.name v.levelParams v.type then return { consts := #[ci] }
  if v.name == trustCompilerName then
    if trustCompilerOk fe v.name v.levelParams v.type then return { consts := #[ci] }
    else throw (.notImplemented s!"unsupported Lean.trustCompiler shape ({v.name})")
  if v.name == ofReduceNatName || v.name == ofReduceBoolName then
    if ofReduceAxOk fe v.name v.levelParams v.type then return { consts := #[ci] }
    else throw (.notImplemented s!"unsupported compiler-trust axiom environment ({v.name})")
  if v.name == propextName || v.name == choiceName then
    throw (.notImplemented s!"standard axiom shape mismatch ({v.name})")
  if v.name == sorryAxName || cfg.coreAxioms then return { consts := #[ci] }
  throw (.notImplemented (nonStdAxiomMsg v.name))

/-- A mutual block of unsafe or partial definitions (official `add_mutual`;
con-leche has no such declaration). -/
def checkMutualC (fe : FEnv) (vs : List DefinitionVal) : CheckCM Added := do
  let some v₀ := vs.head? | throw (.invalid "invalid empty mutual definition")
  let safety := v₀.safety
  if safety == .safe then
    throw (.invalid "invalid mutual definition, declaration is not tagged as unsafe/partial")
  let fe := fe.withSafety safety
  let mut found : Array Name := #[]
  for v in vs do
    if v.safety != safety then
      throw (.invalid "invalid mutual definition, declarations must have the same safety annotation")
    if v.levelParams != v₀.levelParams then
      throw (.invalid "invalid mutual definition, declarations must have the same universe level \
        parameters")
    if found.contains v.name then
      throw (.invalid s!"invalid mutual definition, duplicate declaration name '{v.name}'")
    found := found.push v.name
    checkConstantValC mode fe v.toConstantVal true
  let fe' := fe.pushAll (vs.map ConstantInfo.defnInfo)
  for v in vs do
    checkValueC mode fe' "definition" v.name v.levelParams v.type v.value
  return { consts := (vs.map ConstantInfo.defnInfo).toArray }

end

end Lean.Kernel.InLean
