/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Core
public import Lean.Kernel.InLean.NatOpPins
public import Lean.Util.CollectLevelParams
public import Lean.Util.FoldConsts

/-!
# InLean: declaration checking

Twin of `ConLeche/Cached/ParsedC.lean`'s `checkDeclC` and
`ConLeche/Kernel/CheckDecl.lean`'s `checkDecl` over `Lean.Declaration`:
the constant checks (`checkConstantValC`), the value checks
(`checkDefnValCI`, `checkThmVal`, `checkOpaqueValCI`), the pinned axioms
(`stdAxiomOkF`, `trustCompilerOkF`, `ofReduceAxOkF`, `Quot.sound`), the
structural Nat operations' recurrence certificates (`certifyNatEqs`), the
pin-certified ones' variants (`checkDivModPinF`) and the compiler-trust
opaques' pins (`checkReducePinF`).

Beyond con-leche, as the official kernel does
(`environment.cpp`): `unsafe` axioms, definitions and opaques, `partial`
definitions and `mutualDefnDecl`.  Each runs the core at the
declaration's safety (`Ctx.safety`); none of them is covered by any
proof.

What is returned is the list of constants to add, in order; the caller
(`Lean/Kernel/InLean/AddDecl.lean`) adds them.  A recursive `unsafe` definition and a
mutual block need their own constants in the environment their values are
checked in: `addConst` is passed in for that.

Theorems are stored with their values (Lean's elaborator reads them);
the core never unfolds one (`unfoldDefinition`).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## Syntactic guards -/

/-- The level parameters `e` mentions (a memoised DAG walk). -/
def levelParamsOf (e : Expr) : Array Name :=
  EO.levelParams e

/-- Twin of the syntactic half of `checkConstantValC` /
`checkDefnValCI` on one expression: closed, no metavariable, level
parameters declared, constants resolve (`sorryAx`: a decline). -/
def checkExprWF (what : String) (lps : List Name) (e : Expr) : M Unit := do
  if e.hasLooseBVars then throwInvalid s!"loose bound variable in {what}"
  if e.hasFVar then throwInvalid s!"unexpected free variable in {what}"
  if e.hasMVar then throwInvalid s!"unexpected metavariable in {what}"
  if e.hasLevelParam then
    unless (levelParamsOf e).all lps.contains do
      throwInvalid s!"undeclared universe parameter in {what}"
  let env := (← read).env
  let coreAxioms := (← read).coreAxioms
  for c in EO.usedConstants e do
    if c == sorryAxName && !coreAxioms then throwDeclined "use of the sorryAx axiom"
    unless (env.find? c).isSome do
      throwInvalid s!"unknown constant {c} in {what}"

/-- Twin of `checkConstantValC`, at a set of names already taken by the
block (`mutualDefnDecl`'s duplicate check). -/
def checkConstantVal (μ : CheckMode) (n : Name) (lps : List Name) (ty : Expr) : M Unit := do
  if ((← read).env.find? n).isSome then throwInvalid s!"already declared {n}"
  if reservedBasisNames.contains n then throwInvalid s!"reserved basis name {n}"
  unless namesNodup lps do throwInvalid s!"duplicate universe parameters in {n}"
  checkExprWF s!"type of {n}" lps ty
  let _ ← ensureSort μ 0 (← infer μ 0 ty)

/-- A value against its declared type (twin of the value half of
`checkDefnValCI`/`checkOpaqueValCI`). -/
def checkValue (μ : CheckMode) (kind : String) (n : Name) (lps : List Name) (ty v : Expr) :
    M Unit := do
  checkExprWF s!"value of {n}" lps v
  let vt ← infer μ 0 v
  unless ← defeq μ 0 vt ty do throwInvalid s!"type mismatch in {kind} {n}"

/-! ## The structural Nat operations (twin of `checkDeclC`'s pinned arm) -/

/-- Twin of `natOpCodF`. -/
def natOpCod (env : Kernel.Environment) (c : Name) (e : Expr) : Bool :=
  if c == natBeqName || c == natBleName then
    e == .const boolName [] && (match env.find? boolName with
      | some ci => boolPin.matches ci
      | none => false)
  else e == .const natName []

/-- Twin of `natOpTyPinnedF`. -/
def natOpTyPinned (env : Kernel.Environment) (c : Name) (ty : Expr) : Bool :=
  if c == natPredName then
    match ty with
    | .forallE _ dom body _ => dom == .const natName [] && natOpCod env c body
    | _ => false
  else
    match ty with
    | .forallE _ dom (.forallE _ dom2 body _) _ =>
      dom == .const natName [] && dom2 == .const natName [] && natOpCod env c body
    | _ => false

/-- Twin of `natOpStoredOkF`. -/
def natOpStoredOk (env : Kernel.Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo v) => v.levelParams.isEmpty && natOpTyPinned env n (stripMData v.type)
  | _ => false

/-- Twin of `natOpGuardF`. -/
def natOpGuard (env : Kernel.Environment) (c : Name) : Bool :=
  natLitSupported env &&
  (natOpDeps c).all (fun n => match env.find? n with
    | some (.defnInfo v) => v.levelParams.isEmpty
    | _ => false) &&
  (if c == natBeqName || c == natBleName || natDivModNames.contains c then
    (match env.find? boolTrueName with
      | some ci => ci.levelParams.isEmpty && stripMData ci.type == .const boolName []
      | none => false) &&
    (match env.find? boolFalseName with
      | some ci => ci.levelParams.isEmpty && stripMData ci.type == .const boolName []
      | none => false)
   else true)

/-- Twin of `certifyNatEqs` (the recurrences over the two variables, at
depth 2). -/
def certifyNatEqs (μ : CheckMode) (eqs : List (Expr × Expr)) : M Bool := do
  for (l, r) in eqs do
    unless ← defeq μ 2 l r do return false
  return true

/-- The two `Nat` variables of the certificates (con-leche's `fvar 0`,
`fvar 1` of type `Nat`). -/
def natVars : M (Expr × Expr) := do
  let natTy : Expr := .const natName []
  return (← mkFVar 0 natTy, ← mkFVar 1 natTy)

/-- Twin of `divModEnvGuardF`. -/
def divModEnvGuard (env2 : Kernel.Environment) (c : Name) : Bool :=
  natOpGuard env2 c && (natOpDeps c).all (natOpStoredOk env2) &&
  (match env2.find? eqName with
    | some ci => eqPin.matches ci
    | none => false) &&
  (match env2.find? boolTrueName with
    | some ci => ci.type == .const boolName []
    | none => false) &&
  (match env2.find? boolFalseName with
    | some ci => ci.type == .const boolName []
    | none => false)

/-- Every constant of `e` resolves in `env`. -/
def constsResolve (env : Kernel.Environment) (e : Expr) : Bool :=
  (EO.usedConstants e).all fun c => (env.find? c).isSome

/-- Twin of `divModPinGuardF`. -/
def divModPinGuard (env : Kernel.Environment) (op : PinOp) : Bool :=
  !op.pin.hasLooseBVars && !op.pin.hasFVar && !op.pin.hasLevelParam && constsResolve env op.pin &&
  op.typePins.all fun (n, ty) =>
    match env.find? n with
    | some ci => !ci.type.hasFVar && !ty.hasLooseBVars && !ty.hasFVar && constsResolve env ty
    | none => false

/-- Twin of `divModCertGuardF`. -/
def divModCertGuard (env : Kernel.Environment) (c : Name) (annVal : Expr)
    (hyps : List Expr) (eqE proof : Expr) : Bool :=
  let p := substConstAll c annVal proof
  !p.hasLooseBVars && !p.hasFVar && !p.hasLevelParam && constsResolve env p &&
    (hyps.map (substConst0 c annVal)).all (constsResolve env) &&
    constsResolve env (substConst0 c annVal eqE)

/-- Twin of `checkDivModCertsF`: each certificate applied to the two
variables and its hypotheses (`divModCertApplied`, at depth 4) has its
statement as type. -/
def checkDivModCerts (μ : CheckMode) (c : Name) (annVal : Expr) (x y : Expr)
    (stmts : List (List Expr × Expr)) (proofs : List Expr) : M Bool := do
  match stmts, proofs with
  | [], [] => return true
  | (hyps, eqE) :: srest, proof :: prest =>
    if divModCertGuard (← read).env c annVal hyps eqE proof then
      let p := substConstAll c annVal proof
      let hs := hyps.map (substConst0 c annVal)
      let base := mkApp2 p x y
      let applied ← match hs with
        | [h1] => pure (.app base (← mkFVar 2 h1))
        | [h1, h2] => pure (mkApp2 base (← mkFVar 2 h1) (← mkFVar 3 h2))
        | _ => pure base
      let tp ← infer μ 4 applied
      if ← defeq μ 4 tp (substConst0 c annVal eqE) then
        checkDivModCerts μ c annVal x y srest prest
      else return false
    else return false
  | _, _ => return false

/-- Twin of `checkDivModPinF` (with `checkDivModPinLoopF`,
`checkDivModPinAtF`, `checkTypePinsF`). -/
def checkDivModPin (μ : CheckMode) (env2 : Kernel.Environment) (c : Name) (value' : Expr) :
    M Unit := do
  unless divModEnvGuard env2 c do
    throwDeclined s!"unsupported Nat.div/mod environment ({c})"
  let sets ← match loadPinSets () with
    | .ok s => pure s
    | .error e => throwInternal s!"the Nat-operation pin dumps do not decode: {e}"
  let (x, y) ← natVars
  let mut tried : Array String := #[]
  for ps in sets do
    let some op := ps.op? c
      | tried := tried.push s!"{ps.toolchain}: no pin"; continue
    let stmts := divModCertStmts x y c
    let env := (← read).env
    if divModPinGuard env op &&
        (stmts.zip op.proofs.toList).all (fun p => divModCertGuard env c value' p.1.1 p.1.2 p.2) then
      let mut typesOk := true
      for (n, ty) in op.typePins do
        let stored := match env.find? n with
          | some ci => ci.type
          | none => .sort .zero
        unless ← defeq μ 0 stored ty do typesOk := false; break
      if typesOk && (← defeq μ 0 value' op.pin) &&
          (← checkDivModCerts μ c value' x y stmts op.proofs.toList) then
        return
      tried := tried.push s!"{ps.toolchain}: a type pin or the pin not definitionally equal, or \
        a certificate failed"
    else
      tried := tried.push s!"{ps.toolchain}: pin or certificate ground constants absent"
  throwDeclined s!"unsupported Nat.div/mod spelling ({c}: no pin variant matched — \
    {String.intercalate "; " tried.toList})"

/-! ## The compiler-trust opaques and axioms -/

/-- Twin of `reduceElemOkF`. -/
def reduceElemOk (env : Kernel.Environment) (c : Name) : Bool :=
  if c == reduceNatName then natLitSupported env && (match env.find? natName with
    | some ci => natPin.matches ci
    | none => false)
  else match env.find? boolName with
    | some ci => boolPin.matches ci
    | none => false

/-- Twin of `reduceStoredOkF` (Lean stores the opaque as an opaque). -/
def reduceStoredOk (env : Kernel.Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci@(.opaqueInfo _) => (reduceOpPin c).matches ci
  | some ci@(.axiomInfo _) => (reduceOpPin c).matches ci
  | _ => false

/-- Twin of `checkReducePinF`. -/
def checkReducePin (μ : CheckMode) (env2 : Kernel.Environment) (c : Name) (value : Expr) :
    M Unit := do
  let env := (← read).env
  unless reduceStoredOk env2 c && reduceElemOk env c do
    throwDeclined s!"unsupported compiler-trust opaque declaration ({c})"
  unless constsResolve env (reduceDeclPin c) do
    throwDeclined s!"unsupported compiler-trust opaque spelling ({c}: pin ground constants absent)"
  unless ← defeq μ 0 value (reduceDeclPin c) do
    throwDeclined s!"unsupported compiler-trust opaque spelling ({c})"
  let x ← mkFVar 0 (reduceElemTy c)
  unless ← defeq μ 1 (.app value x) x do
    throwInternal s!"pinned compiler-trust opaque is not the identity ({c})"

def pinFound (env : Kernel.Environment) (p : Pin) : Bool :=
  match env.find? p.name with
  | some ci => p.matches ci
  | none => false

/-- Twin of `stdAxiomOkF`. -/
def stdAxiomOk (env : Kernel.Environment) (n : Name) (lps : List Name) (ty : Expr) : Bool :=
  let me : Pin → Bool := fun p => p.matchesDecl n lps ty
  if n == propextName then
    pinFound env eqPin && pinFound env iffPin && pinFound env iffIntroPin && pinFound env iffRecPin &&
      me propextPin
  else if n == choiceName then
    pinFound env nonemptyPin && pinFound env nonemptyIntroPin && pinFound env nonemptyRecPin &&
      me choicePin
  else false

/-- Twin of `trustCompilerOkF`. -/
def trustCompilerOk (env : Kernel.Environment) (n : Name) (lps : List Name) (ty : Expr) : Bool :=
  pinFound env truePin && pinFound env trueIntroPin &&
    trustCompilerPin.matchesDecl n lps ty

/-- Twin of `ofReduceAxOkF`. -/
def ofReduceAxOk (env : Kernel.Environment) (n : Name) (lps : List Name) (ty : Expr) : Bool :=
  let c := ofReduceOp n
  let p := ofReducePin n
  pinFound env eqPin && reduceElemOk env c && reduceStoredOk env c &&
    p.matchesDecl n lps ty

/-! ## The declaration step -/

/-- What a declaration adds: the constants, in order, and whether it is
the quotient package (official's `quotInit` flag). -/
structure Added where
  consts : Array ConstantInfo := #[]
  quot : Bool := false

/-- A definition's check (official `add_definition`; con-leche's
`checkDeclC` `defnDecl` arm, the pinned Nat operations included).
`addConst` is core's private `Kernel.Environment.add`. -/
def checkDefn (μ : CheckMode) (addConst : Kernel.Environment → ConstantInfo → Kernel.Environment)
    (v : DefinitionVal) : M Added := do
  let ci := ConstantInfo.defnInfo v
  if v.safety == .unsafe then
    -- an unsafe definition may be recursive: header, add, then the body
    withReader (fun c => { c with safety := .unsafe }) do
      checkConstantVal μ v.name v.levelParams v.type
    let env' := addConst (← read).env ci
    withReader (fun c => { c with env := env', safety := .unsafe }) do
      checkValue μ "definition" v.name v.levelParams v.type v.value
    return { consts := #[ci] }
  checkConstantVal μ v.name v.levelParams v.type
  checkValue μ "definition" v.name v.levelParams v.type v.value
  if natOpNames.contains v.name || natDivModNames.contains v.name then
    let env2 := addConst (← read).env ci
    let certify : M Unit := do
      if natOpNames.contains v.name then
        unless natOpGuard env2 v.name && (natOpDeps v.name).all (natOpStoredOk env2) do
          throwDeclined s!"nonstandard structural Nat operation environment ({v.name})"
        let (x, y) ← natVars
        let eqs := (natOpEquations x y v.name).map fun (l, r) =>
          (substConst0 v.name v.value l, substConst0 v.name v.value r)
        unless ← certifyNatEqs μ eqs do
          throwDeclined s!"nonstandard structural Nat operation ({v.name})"
      if natDivModNames.contains v.name then
        checkDivModPin μ env2 v.name v.value
    if (← read).uncertifiedNatOps then
      -- the stopgap (`Ctx.uncertifiedNatOps`): a declined certification accepts
      tryCatch certify fun e => if e.isDecline then pure () else throw e
    else certify
  return { consts := #[ci] }

/-- A theorem's check (twin of `checkThmVal`; official `add_theorem`).
Stored with its value, never unfolded. -/
def checkThm (μ : CheckMode) (v : TheoremVal) : M Added := do
  checkConstantVal μ v.name v.levelParams v.type
  let u ← ensureSort μ 0 (← infer μ 0 v.type)
  unless ← isEquivL u .zero do throwInvalid s!"type of theorem {v.name} is not a proposition"
  checkValue μ "theorem" v.name v.levelParams v.type v.value
  return { consts := #[.thmInfo v] }

/-- An opaque's check (twin of `checkOpaqueValCI`; official `add_opaque`,
which checks at the safe safety even for an unsafe opaque). -/
def checkOpaque (μ : CheckMode) (addConst : Kernel.Environment → ConstantInfo → Kernel.Environment)
    (v : OpaqueVal) : M Added := do
  checkConstantVal μ v.name v.levelParams v.type
  checkValue μ "opaque" v.name v.levelParams v.type v.value
  let ci := ConstantInfo.opaqueInfo v
  if reduceOpNames.contains v.name then
    checkReducePin μ (addConst (← read).env ci) v.name v.value
  return { consts := #[ci] }

/-- An axiom's check (twin of `checkDeclC`'s `axiomDecl` arm).  The
pinned axioms are accepted; `sorryAx` is added (Lean's elaborator needs
it; a use declines, `checkExprWF`, `inferBody`); an unsafe axiom is
accepted as the official kernel does; any other axiom
declines, as con-leche's. -/
def checkAxiom (μ : CheckMode) (v : AxiomVal) : M Added := do
  let ci := ConstantInfo.axiomInfo v
  let env := (← read).env
  if v.name == quotSoundName then
    if quotSoundPin.matches ci then return { consts := #[ci] }
    else throwDeclined "quotient soundness axiom mismatch"
  withReader (fun c => { c with safety := if v.isUnsafe then .unsafe else .safe }) do
    checkConstantVal μ v.name v.levelParams v.type
  if v.isUnsafe then return { consts := #[ci] }
  if stdAxiomOk env v.name v.levelParams v.type then return { consts := #[ci] }
  if v.name == trustCompilerName then
    if trustCompilerOk env v.name v.levelParams v.type then return { consts := #[ci] }
    else throwDeclined s!"unsupported Lean.trustCompiler shape ({v.name})"
  if v.name == ofReduceNatName || v.name == ofReduceBoolName then
    if ofReduceAxOk env v.name v.levelParams v.type then return { consts := #[ci] }
    else throwDeclined s!"unsupported compiler-trust axiom environment ({v.name})"
  if v.name == propextName || v.name == choiceName then
    throwDeclined s!"standard axiom shape mismatch ({v.name})"
  if v.name == sorryAxName || (← read).coreAxioms then return { consts := #[ci] }
  throwDeclined (nonStdAxiomMsg v.name)

/-- A mutual block of unsafe or partial definitions (official
`add_mutual`; con-leche has no such declaration). -/
def checkMutual (μ : CheckMode) (addConst : Kernel.Environment → ConstantInfo → Kernel.Environment)
    (vs : List DefinitionVal) : M Added := do
  let some v₀ := vs.head? | throwInvalid "invalid empty mutual definition"
  let safety := v₀.safety
  if safety == .safe then
    throwInvalid "invalid mutual definition, declaration is not tagged as unsafe/partial"
  let mut found : Array Name := #[]
  for v in vs do
    if v.safety != safety then
      throwInvalid "invalid mutual definition, declarations must have the same safety annotation"
    if v.levelParams != v₀.levelParams then
      throwInvalid "invalid mutual definition, declarations must have the same universe level \
        parameters"
    if found.contains v.name then
      throwInvalid s!"invalid mutual definition, duplicate declaration name '{v.name}'"
    found := found.push v.name
    withReader (fun c => { c with safety := safety }) do
      checkConstantVal μ v.name v.levelParams v.type
  let mut env' := (← read).env
  for v in vs do
    env' := addConst env' (.defnInfo v)
  for v in vs do
    withReader (fun c => { c with env := env', safety := safety }) do
      checkValue μ "definition" v.name v.levelParams v.type v.value
  return { consts := (vs.map ConstantInfo.defnInfo).toArray }

/-- The quotient package (twin of `checkBasisDeclC .quotK`): the pinned
`Eq`, then the pinned block's four constants. -/
def checkQuot : M Added := do
  unless pinFound (← read).env eqPin do
    throwDeclined "quotient basis requires the pinned Eq basis"
  let mk (p : Pin) (k : QuotKind) : ConstantInfo :=
    .quotInfo { name := p.name, levelParams := p.lps, type := p.type, kind := k }
  return { consts := #[mk quotPin .type, mk quotMkPin .ctor, mk quotLiftPin .lift,
                       mk quotIndPin .ind], quot := true }

end Lean.Kernel.InLean
