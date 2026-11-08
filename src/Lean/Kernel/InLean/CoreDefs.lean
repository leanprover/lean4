/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.FEnv

/-!
# InLean: the core's helpers

Twins of the fuel-free helpers the cached core calls, from
`ConLeche.Kernel.CoreDefs`, `ConLeche.Kernel.Core` (the error
choices, the small expression predicates) and
`ConLeche.Kernel.PropRead` (the head-symbol readers).

Two shapes differ from con-leche's because a `Lean.Expr` free variable is
an id: where con-leche reads a variable's type off the node, the readers
here take it from the state (`fvTy`), and building a variable is a state
operation (`mkFVarM`), so the telescope openers are in `CheckCM`.
`mdata` is looked through wherever a head is read (con-leche's terms
have none).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## Names -/

/-- Twin of `natOpWfNames`. -/
def natOpWfNames : List Name :=
  [natDivName, natModName, natGcdName, natLandName, natLorName,
   natXorName, natShiftLeftName, natShiftRightName]

/-! ## Errors -/

/-- Twin of `unknownConstError`. -/
def unknownConstError (n : Name) : CheckError :=
  if n == sorryAxName then .notImplemented "use of the sorryAx axiom"
  else .invalid s!"unknown constant {n}"

/-- Twin of `projIndexedStructLike`. -/
def projIndexedStructLike (fe : FEnv) (T sn : Name) (i nArgs : Nat) : Bool :=
  T == sn &&
    match fe.indView? T with
    | some (_, caps) =>
      match caps.ctors with
      | [c] =>
        caps.nparams < nArgs &&
          match fe.ctorView? c with
          | some (_, _, nF) => decide (i < nF)
          | none => false
      | _ => false
    | none => false

/-- Twin of `projMissError`. -/
def projMissError (fe : FEnv) (hasTable : Bool) (T sn : Name) (i nArgs : Nat) : CheckError :=
  if hasTable then .invalid "projection index out of range"
  else if projIndexedStructLike fe T sn i nArgs then
    .notImplemented "projection on an indexed structure-like type"
  else .invalid "invalid projection: not a structure-like type, or no such field"

/-! ## Expression predicates -/

/-- Twin of `Expr.piResult`. -/
def piResult : Expr → Expr
  | .mdata _ e => piResult e
  | .forallE _ _ b _ => piResult b
  | e => e

/-- Twin of `Expr.peelPis`. -/
def peelPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ _ b _ => peelPis k b
  | k + 1, .mdata _ e => peelPis (k + 1) e
  | _ + 1, _ => none

/-- Twin of `Expr.binderDom`. -/
def binderDom : Nat → Expr → Option Expr
  | k, .mdata _ e => binderDom k e
  | 0, .forallE _ A _ _ => some A
  | k + 1, .forallE _ _ b _ => binderDom k b
  | _, _ => none

/-- Twin of `teleArityOk`. -/
def teleArityOk (ty : Expr) (args : List Expr) : Bool := (peelPis args.length ty).isSome

/-- Twin of `Expr.ioNeutral`. -/
def Expr.ioNeutral (e : Expr) : Bool :=
  match e.getAppFnT with
  | .lam .. | .letE .. | .bvar _ => false
  | _ => true

/-- Twin of `Expr.headIsProj`. -/
def Expr.headIsProj (e : Expr) : Bool :=
  match e.getAppFnT with
  | .proj .. => true
  | _ => false

/-- Twin of `Expr.isNatZero`. -/
def Expr.isNatZero : Expr → Bool
  | .mdata _ e => Expr.isNatZero e
  | .lit (.natVal 0) => true
  | .const c [] => c == natZeroName
  | _ => false

/-- Twin of `Expr.isLit`. -/
def Expr.isLitI : Expr → Bool
  | .mdata _ e => Expr.isLitI e
  | .lit _ => true
  | _ => false

/-- Twin of `Expr.isStrLit`. -/
def Expr.isStrLitI : Expr → Bool
  | .mdata _ e => Expr.isStrLitI e
  | .lit (.strVal _) => true
  | _ => false

/-- Twin of `Expr.natPred?`. -/
def Expr.natPred? : Expr → Option Expr
  | .mdata _ e => Expr.natPred? e
  | .lit (.natVal (n + 1)) => some (.lit (.natVal n))
  | .app f x =>
    match EO.stripTop f with
    | .const c [] => if c == natSuccName then some x else none
    | _ => none
  | _ => none

/-- Twin of `Expr.isBoolTrue`. -/
def Expr.isBoolTrue : Expr → Bool
  | .mdata _ e => Expr.isBoolTrue e
  | .const c [] => c == boolTrueName
  | _ => false

/-- Twin of `Expr.isEagerReduce`. -/
def Expr.isEagerReduce (e : Expr) : Bool :=
  e.getAppNumArgsT == 2 &&
    match e.getAppFnT with
    | .const c _ => c == eagerReduceName
    | _ => false

/-- Twin of `Expr.lamPair?`. -/
def Expr.lamPair? : Expr → Expr → Option (Expr × Expr × Expr × Expr)
  | .mdata _ a, b => Expr.lamPair? a b
  | a, .mdata _ b => Expr.lamPair? a b
  | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _ => some (t₁, b₁, t₂, b₂)
  | _, _ => none

/-- Twin of `rawNatLitC?`. -/
def rawNatLitC? (e : Expr) : Option Nat :=
  match EO.stripTop (e) with
  | .lit (.natVal n) => some n
  | .const c [] => if c == natZeroName then some 0 else none
  | _ => none

/-- Twin of `sameConstHeadsC`. -/
def sameConstHeadsC (a b : Expr) : Bool :=
  match EO.stripTop a, EO.stripTop b with
  | .app f₁ _, .app f₂ _ =>
    match f₁.getAppFnT, f₂.getAppFnT with
    | .const n₁ _, .const n₂ _ => n₁ == n₂
    | _, _ => false
  | _, _ => false

/-- Twin of `Expr.wscopedBC d e`: every free variable of `e` is at a depth
below `d` (read off the interned ids; an interned variable's type is
scoped below its own depth by construction). -/
def Expr.wscopedBC (d : Nat) (e : Expr) : Bool :=
  !e.hasFVar || (EO.fvarIds e).all fun id =>
    match EO.fvDepth? id with
    | some i => i < d
    | none => false

/-- Twin of `Expr.looseBVarsBounded 0`. -/
@[inline] def Expr.closedBV (e : Expr) : Bool := !e.hasLooseBVars

/-! ## Literals -/

/-- Twin of `natLitToConstructor`. -/
def natLitToConstructor (n : Nat) : Expr :=
  match n with
  | 0 => .const natZeroName []
  | k + 1 => .app (.const natSuccName []) (.lit (.natVal k))

/-- Twin of `strLitToConstructor`. -/
def strLitToConstructor (s : String) : Expr :=
  .app (.const stringOfListName []) <|
    s.toList.foldr
      (init := .app (.const listNilName [.zero]) (.const charName []))
      fun c e =>
        .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e

/-- The official kernel's bound on a computed numeral (`LEAN_NAT_MAX_SIZE`'s
default, 128 MB; the environment variable is not read). -/
def natMaxBytes : Nat := 128 * 1024 * 1024

/-- **The official kernel's numeral guards** (`reduce_pow`,
`reduce_bin_nat_op`), a deviation from con-leche: a literal computation the
official kernel refuses is an error here too.  Without them a huge
exponent or shift falls through to unfolding the operation and exhausts
the native stack. -/
def natOpRefusal (c : Name) (a b : Nat) : Option String :=
  let tooBig := "the kernel refused a `Nat` numeral because its size exceeds the maximum"
  if c == natPowName then
    if b ≥ 2 ^ 32 then
      some "the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer"
    else if a > 1 && (a.log2 + 1) * b > natMaxBytes * 8 then
      some "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size"
    else none
  else if c == natShiftLeftName then
    if b ≥ 2 ^ 32 then
      some "the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer"
    else if a != 0 && a.log2 + 1 + b > natMaxBytes * 8 then some tooBig
    else none
  else if c == natMulName then
    if a.log2 + b.log2 + 2 > natMaxBytes * 8 then some tooBig else none
  else none

/-- Twin of `natOpResult`. -/
def natOpResult (c : Name) (a b : Nat) : Option Expr :=
  if c == natPredName then some (.lit (.natVal (a - 1)))
  else if c == natAddName then some (.lit (.natVal (a + b)))
  else if c == natSubName then some (.lit (.natVal (a - b)))
  else if c == natMulName then some (.lit (.natVal (a * b)))
  else if c == natPowName then
    if b > 16777216 then none else some (.lit (.natVal (a ^ b)))
  else if c == natDivName then some (.lit (.natVal (a / b)))
  else if c == natModName then some (.lit (.natVal (a % b)))
  else if c == natGcdName then some (.lit (.natVal (Nat.gcd a b)))
  else if c == natLandName then some (.lit (.natVal (Nat.land a b)))
  else if c == natLorName then some (.lit (.natVal (Nat.lor a b)))
  else if c == natXorName then some (.lit (.natVal (Nat.xor a b)))
  else if c == natShiftLeftName then some (.lit (.natVal (Nat.shiftLeft a b)))
  else if c == natShiftRightName then some (.lit (.natVal (Nat.shiftRight a b)))
  else if c == natBeqName then
    some (.const (if a == b then boolTrueName else boolFalseName) [])
  else if c == natBleName then
    some (.const (if a ≤ b then boolTrueName else boolFalseName) [])
  else none

/-! ## A family's sort, read at use -/

/-- Twin of `formerResSort`. -/
def formerResSort (ty : Expr) : Option Level :=
  match EO.stripTop (piResult ty) with
  | .sort s => some s
  | _ => none

/-- Twin of `formerDefHeaded`. -/
def formerDefHeaded (cv : ConstantVal) : Bool := (formerResSort cv.type).isNone

/-- Twin of `formerZ`. -/
def formerZ (cvT : ConstantVal) : PropWhen :=
  match formerResSort cvT.type with
  | some s => Lvl.zeronessOf s
  | none => .ifAllZero []

/-- Twin of `formerNeverZero`. -/
def formerNeverZero (cvT : ConstantVal) (us : List Level) : Bool :=
  (Lvl.substPW cvT.levelParams us (formerZ cvT)).isNever

/-- Twin of `ctorFamily`. -/
def ctorFamily (fe : FEnv) (cvj : ConstantVal) : Option (ConstantVal × IndCaps) :=
  match EO.stripTop ((piResult cvj.type).getAppFnT) with
  | .const T _ => fe.indView? T
  | _ => none

/-- Twin of `etaRescueOk`. -/
def etaRescueOk (ctor : Name) (cvj cvT : ConstantVal) (caps : IndCaps) : Bool :=
  caps.eta && caps.etaCtor == ctor && cvj.levelParams == cvT.levelParams && ctor != andIntroName

/-! ## Telescopes opened at free variables -/

/-- Twin of `openPisAtFvars`: the first `n` binders opened at the
variables of depths `i, i + 1, …`. -/
def openPisAtFvarsM : Nat → Expr → Nat → CheckCM (Option (List Expr × Expr))
  | 0, e, _ => pure (some ([], e))
  | n + 1, .mdata _ e, i => openPisAtFvarsM (n + 1) e i
  | n + 1, .forallE _ dom body _, i => do
    let fv ← mkFVarM i dom
    match ← openPisAtFvarsM n (body.inst1I fv) (i + 1) with
    | some (fvs, e) => pure (some (fv :: fvs, e))
    | none => pure none
  | _ + 1, _, _ => pure none

/-- Twin of `structUsedLater`. -/
def structUsedLater (cty : Expr) (nP j : Nat) : Bool :=
  match peelPis (nP + j + 1) cty with
  | some rest => rest.hasLooseBVarI 0
  | none => false

/-- Twin of `projGuardRowsGo`: the field loop of the official `infer_proj`.
`r` is the constructor telescope with its parameters and every field before
the current one opened, the current field's variable at depth `d`; `k`
fields remain before the projected one.  A field the rest uses is a row and
is opened at its variable, one it does not use is stepped over. -/
def projGuardRowsGoM : Nat → Nat → Expr → CheckCM (Option (List (Nat × Expr)))
  | k, d, .mdata _ e => projGuardRowsGoM k d e
  | 0, d, .forallE _ dom _ _ => pure (some [(d, dom)])
  | k + 1, d, .forallE _ dom body _ =>
    if body.hasLooseBVarI 0 then do
      let fv ← mkFVarM d dom
      match ← projGuardRowsGoM k (d + 1) (body.inst1I fv) with
      | some rows => pure (some ((d, dom) :: rows))
      | none => pure none
    else projGuardRowsGoM k (d + 1) body
  | _, _, _ => pure none

/-- Twin of `Expr.leafGuard fab base`: the free variables of `fab` are among
`base`'s, hereditarily through their types (con-leche's variable carries its
type, so its leaves include the annotations'). -/
def leafGuardM (fab base : Expr) : CheckCM Bool := do
  if !fab.hasFVar then return true
  let tys := (← get).fvTys
  let seen := closure tys tys.size (EO.fvarIds base).toList {} {}
  return (EO.fvarIds fab).all seen.contains
where
  /-- The worklist: every id met goes into `seen`; a table number's type is
  expanded once (`done`), and only an expansion spends fuel.  An expanded
  number is a fresh index of `tys`, so the fuel `tys.size` never runs out. -/
  closure (tys : Array Expr) (fuel : Nat) (todo : List FVarId) (seen : Std.HashSet FVarId)
      (done : Std.HashSet Nat) : Std.HashSet FVarId :=
    match todo with
    | [] => seen
    | id :: todo =>
      let seen := seen.insert id
      match fvParts? id with
      | some (_, n) =>
        match tys[n]? with
        | some ty =>
          if done.contains n then closure tys fuel todo seen done
          else match fuel with
            | 0 => seen
            | fuel + 1 => closure tys fuel ((EO.fvarIds ty).toList ++ todo) seen (done.insert n)
        | none => closure tys fuel todo seen done
      | none => closure tys fuel todo seen done
  termination_by (fuel, todo.length)

/-- The free variables reachable from `e`, hereditarily through their types. -/
def fvarClosureM (e : Expr) : CheckCM (Std.HashSet FVarId) := do
  if !e.hasFVar then return {}
  let tys := (← get).fvTys
  return leafGuardM.closure tys tys.size (EO.fvarIds e).toList {} {}

/-! ## The head-symbol readers (twin of `ConLeche.Kernel.PropRead`) -/

/-- Twin of `residualPW`. -/
def residualPW : Option Expr → Option PropWhen
  | some e =>
    match EO.stripTop e with
    | .sort u => some (Lvl.zeronessOf u)
    | _ => none
  | none => none

/-- Twin of `lamProj?`. -/
def lamProj? : Nat → Expr → Option (Nat × Nat)
  | k, .mdata _ e => lamProj? k e
  | k, .lam _ _ b _ => lamProj? (k + 1) b
  | k, .bvar j => if j < k then some (k, j) else none
  | _, _ => none

/-- Twin of `unwrapIdDefs`. -/
def unwrapIdDefs (fe : FEnv) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    match e.getAppFnT with
    | .const c _ =>
      match fe.defnView? c with
      | some (_, v, _) =>
        match lamProj? 0 v with
        | some (k, j) =>
          let args := e.getAppArgsT
          if k ≤ args.size && args.size == k then
            unwrapIdDefs fe fuel (args.getD (k - 1 - j) e)
          else e
        | none => e
      | none => e
    | _ => e

/-- Twin of `peelPisW`. -/
def peelPisW (fe : FEnv) : Nat → Expr → Option Expr
  | 0, e => some (unwrapIdDefs fe 4 e)
  | k + 1, .forallE _ _ b _ => peelPisW fe k b
  | k + 1, .mdata _ e => peelPisW fe (k + 1) e
  | k + 1, e =>
    match EO.stripTop (unwrapIdDefs fe 4 e) with
    | .forallE _ _ b _ => peelPisW fe k b
    | _ => none

/-- Twin of `headTypePW`. -/
def headTypePW (fe : FEnv) (fvTy : FVarId → Option Expr) (root : Expr) (d : Nat) :
    Expr → Nat → Option PropWhen
  | .mdata _ e, n => headTypePW fe fvTy root d e n
  | .const I us, n =>
    match fe.find? I with
    | some ci =>
      if us.length == ci.levelParams.length then
        (residualPW (peelPisW fe n ci.type)).map (Lvl.substPW ci.levelParams us)
      else none
    | none => none
  | .fvar id, n =>
    match fvTy id with
    | some ty => residualPW (peelPisW fe n ty)
    | none => none
  | .bvar i, n =>
    if i < d then
      match binderDom (d - 1 - i) root with
      | some D => residualPW (peelPisW fe n D)
      | none => none
    else none
  | _, _ => none

/-- Twin of `typeSortPWGo`. -/
def typeSortPWGo (fe : FEnv) (fvTy : FVarId → Option Expr) (root : Expr) :
    Expr → Nat → Option PropWhen
  | .mdata _ e, d => typeSortPWGo fe fvTy root e d
  | .forallE _ _ b _, d => typeSortPWGo fe fvTy root b (d + 1)
  | .sort _, _ => some .never
  | R, d => headTypePW fe fvTy root d R.getAppFnT R.getAppNumArgsT

/-- Twin of `typeSortPW`. -/
def typeSortPW (fe : FEnv) (fvTy : FVarId → Option Expr) (T : Expr) : Option PropWhen :=
  typeSortPWGo fe fvTy T T 0

/-- Twin of `headProofPW`; a projection head reads its field's body
(`projBodyAt`). -/
def headProofPW (fe : FEnv) (fvTy : FVarId → Option Expr) : Expr → Option PropWhen
  | .mdata _ e => headProofPW fe fvTy e
  | .const c us =>
    match fe.find? c with
    | some ci =>
      if us.length == ci.levelParams.length then
        (typeSortPW fe fvTy ci.type).map (Lvl.substPW ci.levelParams us)
      else none
    | none => none
  | .fvar id =>
    match fvTy id with
    | some ty => typeSortPW fe fvTy ty
    | none => none
  | .sort _ | .forallE .. | .lit _ => some .never
  | .proj S i _ =>
    match fe.findProj? S i with
    | some entry =>
      match projBodyAt S entry.numParams i entry.ctorType with
      | some body =>
        match typeSortPW fe fvTy body with
        | some pw => if pw.isNever then some pw else none
        | none => none
      | none => none
    | none => none
  | _ => none

/-- Twin of `proofPW`. -/
def proofPW (fe : FEnv) (fvTy : FVarId → Option Expr) : Expr → Option PropWhen
  | .lam _ _ b _ => proofPW fe fvTy b
  | .letE _ _ _ b _ => proofPW fe fvTy b
  | .app f _ => proofPW fe fvTy f
  | .mdata _ e => proofPW fe fvTy e
  | h => headProofPW fe fvTy h

/-- The state's free-variable types as a reader's lookup. -/
def fvTyOf (tys : Array Expr) (id : FVarId) : Option Expr :=
  match fvParts? id with
  | some (_, n) => tys[n]?
  | none => none

/-- Twin of `notProofFast`. -/
def notProofFastM (fe : FEnv) (a : Expr) : CheckCM Bool := do
  let tys := (← get).fvTys
  return match proofPW fe (fvTyOf tys) a with
    | some pw => !pw.isProp
    | none => false

/-- Twin of `isProofFast`. -/
def isProofFastM (fe : FEnv) (a : Expr) : CheckCM Bool := do
  let tys := (← get).fvTys
  return match proofPW fe (fvTyOf tys) a with
    | some pw => pw.isProp
    | none => false

end Lean.Kernel.InLean
