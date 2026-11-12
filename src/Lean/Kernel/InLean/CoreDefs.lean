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

/-! ## Errors -/

/-- **The reject of a constant the check does not see** (`FEnv.sees`),
worded as the official kernel's: an `unsafe` or `partial` constant in the
check of a safe declaration (official `infer_constant`), else an unknown
constant. -/
def unseenConstError (fe : FEnv) (n : Name) : CheckError :=
  match fe.env.find? n with
  | some (.defnInfo v) =>
    if v.safety == .unsafe then
      .invalid s!"invalid declaration, it uses unsafe declaration '{n}'"
    else if v.safety == .partial then
      .invalid s!"invalid declaration, safe declaration must not contain partial declaration '{n}'"
    else .invalid s!"unknown constant '{n}'"
  | some ci =>
    if ci.isUnsafe then .invalid s!"invalid declaration, it uses unsafe declaration '{n}'"
    else .invalid s!"unknown constant '{n}'"
  | none => .invalid s!"unknown constant '{n}'"

/-- Twin of `unknownConstError`. -/
def unknownConstError (fe : FEnv) (n : Name) : CheckError :=
  if n == sorryAxName then .notImplemented "use of the sorryAx axiom"
  else unseenConstError fe n

/-- Twin of `projIndexedStructLike`. -/
def projIndexedStructLike (fe : FEnv) (T sn : Name) (i nArgs : Nat) : Bool :=
  T == sn &&
    match fe.indView? T with
    | some (_, caps) =>
      match caps.ctors with
      | [c] =>
        caps.nparams < nArgs &&
          match fe.ctorView? c with
          | some (_, _, nF, _) => decide (i < nF)
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

/-- Twin of `teleArityOk`. -/
def teleArityOk (ty : Expr) (args : List Expr) : Bool := (peelPis args.length ty).isSome

/-- Twin of `etaCtorPartialC`. -/
def etaCtorPartialC (fe : FEnv) (e : Expr) : Option Nat :=
  match e.getAppFnT with
  | .const c _ =>
    match fe.ctorView? c with
    | some (_, cnP, cnF, T) =>
      if e.getAppNumArgsT < cnP + cnF then
        match fe.indView? T with
        | some (_, caps) =>
          match fe.findTable? T with
          | some tbl =>
            if caps.eta = true ∧ tbl.ctor == c then
              some (cnP + cnF - e.getAppNumArgsT)
            else none
          | none => none
        | none => none
      else none
    | none => none
  | _ => none

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

/-- Twin of `Expr.binderPair?`: two λs (`lam = true`) or two ∀s
(`lam = false`), read through `mdata`. -/
def Expr.binderPair? (lam : Bool) : Expr → Expr → Option (Expr × Expr × Expr × Expr)
  | .mdata _ a, b => Expr.binderPair? lam a b
  | a, .mdata _ b => Expr.binderPair? lam a b
  | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _ => if lam then some (t₁, b₁, t₂, b₂) else none
  | .forallE _ t₁ b₁ _, .forallE _ t₂ b₂ _ => if lam then none else some (t₁, b₁, t₂, b₂)
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

/-- The node test of `Expr.wscopedBC`: a subterm without free variables is
scoped, a free variable is out of scope unless its depth is below `d`. -/
def wscopedOut (d : Nat) (x : Expr) (_ : Nat) : Option Bool :=
  if !x.hasFVar then some false else
  match x with
  | .fvar id => some (match EO.fvDepth? id with
    | some i => !decide (i < d)
    | none => true)
  | _ => none

/-- Twin of `Expr.wscopedBC d e`: every free variable of `e` is at a depth
below `d`, one walk stopping at the first variable out of scope and below
no subterm without free variables (an interned variable's type is scoped
below its own depth by construction). -/
def Expr.wscopedBC (d : Nat) (e : Expr) : Bool :=
  !EO.anyNode (wscopedOut d) e 0

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

/-- Twin of `natSizeBytes` (the same value; the scalar case without the
logarithm): **a numeral's size in bytes**, as the runtime's
`lean_nat_size_in_bytes` reports it on a 64-bit platform: a scalar (below
`2 ^ 63`) occupies one word, a big number its 64-bit limbs. -/
def natSizeBytes (n : Nat) : Nat :=
  if n < 9223372036854775808 then 8 else 8 * ((n.log2 + 64) / 64)  -- 2 ^ 63

/-- The official kernel's message for a numeral past the size bound. -/
def natTooBigMsg : String :=
  "the kernel refused a `Nat` numeral because its size exceeds the maximum; increase the \
  LEAN_NAT_MAX_SIZE environment variable to allow it"

/-! ## The binary `Nat` operations (twin of master's `NatBinOp`)

`reduceNatI` finds the operation of `.app (.app (.const c []) a) b` once, by
the name's cached hash and one structural confirmation (`NatBinOp.ofName?`),
and dispatches on it: the operation's result and its size refusals. -/

/-- Twin of `NatBinOp`: the fourteen binary `Nat` operations the kernel
computes on literals, in the order of `reduceNat`'s name test. -/
inductive NatBinOp where
  | add | sub | mul | pow | beq | ble | div | mod | gcd | land | lor | xor
  | shiftLeft | shiftRight

/-- Twin of `NatBinOp.name`. -/
def NatBinOp.name : NatBinOp → Name
  | .add => natAddName | .sub => natSubName | .mul => natMulName | .pow => natPowName
  | .beq => natBeqName | .ble => natBleName | .div => natDivName | .mod => natModName
  | .gcd => natGcdName | .land => natLandName | .lor => natLorName | .xor => natXorName
  | .shiftLeft => natShiftLeftName | .shiftRight => natShiftRightName

/-- Twin of `nameIsC`: `c = n`, the cached hashes first. -/
@[inline] def nameIsC (c n : Name) : Bool := c.hash == n.hash && c == n

/-- Twin of `NatBinOp.ofName?`: the operation named `c`, if any. -/
def NatBinOp.ofName? (c : Name) : Option NatBinOp :=
  if nameIsC c natAddName then some .add
  else if nameIsC c natSubName then some .sub
  else if nameIsC c natMulName then some .mul
  else if nameIsC c natPowName then some .pow
  else if nameIsC c natBeqName then some .beq
  else if nameIsC c natBleName then some .ble
  else if nameIsC c natDivName then some .div
  else if nameIsC c natModName then some .mod
  else if nameIsC c natGcdName then some .gcd
  else if nameIsC c natLandName then some .land
  else if nameIsC c natLorName then some .lor
  else if nameIsC c natXorName then some .xor
  else if nameIsC c natShiftLeftName then some .shiftLeft
  else if nameIsC c natShiftRightName then some .shiftRight
  else none

/-- Twin of `NatBinOp.result`: the operation's result on literals. -/
def NatBinOp.result : NatBinOp → Nat → Nat → Expr
  | .add, a, b => .lit (.natVal (a + b))
  | .sub, a, b => .lit (.natVal (a - b))
  | .mul, a, b => .lit (.natVal (a * b))
  | .pow, a, b => .lit (.natVal (a ^ b))
  | .beq, a, b => .const (if a = b then boolTrueName else boolFalseName) []
  | .ble, a, b => .const (if a ≤ b then boolTrueName else boolFalseName) []
  | .div, a, b => .lit (.natVal (a / b))
  | .mod, a, b => .lit (.natVal (a % b))
  | .gcd, a, b => .lit (.natVal (Nat.gcd a b))
  | .land, a, b => .lit (.natVal (Nat.land a b))
  | .lor, a, b => .lit (.natVal (Nat.lor a b))
  | .xor, a, b => .lit (.natVal (Nat.xor a b))
  | .shiftLeft, a, b => .lit (.natVal (Nat.shiftLeft a b))
  | .shiftRight, a, b => .lit (.natVal (Nat.shiftRight a b))

/-- Twin of `natOpRefusal`: **the official kernel's guards on a literal
computation** (`reduce_pow`, `reduce_shiftLeft`), before the result is
computed, at the size bound `maxBytes` (`Limits.maxNatSize`): an exponent or
shift past 32 bits, a power whose size bound (the base's size times the
exponent) exceeds the bound, a shift whose result would.  The messages are
the official kernel's. -/
def natOpRefusal (maxBytes : Nat) (op : NatBinOp) (a b : Nat) : Option String :=
  match op with
  | .pow =>
    if b ≥ 2 ^ 32 then
      some "the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer"
    else if a > 1 && b != 0 && natSizeBytes a > maxBytes / b then
      some "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum \
        numeral size; increase the LEAN_NAT_MAX_SIZE environment variable to allow it"
    else none
  | .shiftLeft =>
    if a == 0 then none
    else if b ≥ 2 ^ 32 then
      some "the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer"
    else if natSizeBytes a + b / 8 + 1 > maxBytes then some natTooBigMsg
    else none
  | _ => none

/-- Twin of `natResultRefused`: **the official kernel's guard on a computed numeral**
(`reduce_bin_nat_op`'s `check_size`): the result of `Nat.add`, `Nat.sub`
and `Nat.mul` past the size bound. -/
def natResultRefused (maxBytes : Nat) (op : NatBinOp) (x : Expr) : Bool :=
  match op with
  | .add | .sub | .mul =>
    match x with
    | .lit (.natVal r) => natSizeBytes r > maxBytes
    | _ => false
  | _ => false

/-! ## A family's sort, read at use -/

/-- Twin of `formerDefHeaded`. -/
def formerDefHeaded (cv : ConstantVal) : Bool := (formerResSort cv.type).isNone

/-- Twin of `formerNeverZero`. -/
def formerNeverZero (cvT : ConstantVal) (us : List Level) : Bool :=
  (Lvl.substPW cvT.levelParams us (formerZ cvT)).isNever

/-- Twin of `ctorFamily`: the former and the capabilities stored at the
constructor's `induct` (Lean's `ConstructorVal.induct`, read by
`ctorView?`). -/
def ctorFamily (fe : FEnv) (induct : Name) : Option (ConstantVal × IndCaps) :=
  fe.indView? induct

/-- Twin of `recFireLevelCount`: how many comparand levels a rule firing at
`fire` has, read without substituting. -/
def recFireLevelCount (fire : RecRuleFire) (cvjLps : List Name) : Nat :=
  match fire with
  | .nested lvls _ => lvls.length
  | .plain => cvjLps.length
  | .levels lvls => lvls.length

/-- Twin of `iotaNoCert`: a rule fires with no certificate at a K recursor,
or where the constructor's family records a never-zero sort
(`IndCaps.neverZero`) and has `n` level parameters. -/
def iotaNoCert (fe : FEnv) (isK : Bool) (induct : Name) (n : Nat) : Bool :=
  isK ||
    match ctorFamily fe induct with
    | some (cvT, caps) => caps.neverZero && cvT.levelParams.length == n
    | none => false

/-- Twin of `etaRescueTable?`. -/
def etaRescueTable? (tbl? : Option TableView) (ctor : Name) (cvj cvT : ConstantVal)
    (caps : IndCaps) : Option TableView :=
  match tbl? with
  | some tbl =>
    if caps.eta && tbl.ctor == ctor && cvj.levelParams == cvT.levelParams &&
        ctor != andIntroName then some tbl
    else none
  | none => none

/-! ## Telescopes opened at free variables -/

/-- Twin of `openPisRawGoC`: the first `n` binders opened at the variables
of depths `i, i + 1, …`, each domain instantiated by the variables so far
(`acc`, outermost first) in one walk; the residual is left raw, the
variables returned. -/
def openPisRawM (acc : Array Expr) : Nat → Expr → Nat → CheckCM (Option (Array Expr × Expr))
  | 0, e, _ => pure (some (acc, e))
  | n + 1, .mdata _ e, i => openPisRawM acc (n + 1) e i
  | n + 1, .forallE _ dom body _, i => do
    let fv ← mkFVarM i (dom.instRevI acc)
    openPisRawM (acc.push fv) n body (i + 1)
  | _ + 1, _, _ => pure none

/-- Twin of `openPisAtFvarsC`: the first `n` binders opened at the
variables of depths `i, i + 1, …` by the raw opening (`openPisRawM`), then
the residual instantiated by the variables in one walk. -/
def openPisAtFvarsM (n : Nat) (e : Expr) (i : Nat) : CheckCM (Option (List Expr × Expr)) := do
  match ← openPisRawM #[] n e i with
  | some (fvs, r) => pure (some (fvs.toList, r.instRevI fvs))
  | none => pure none

/-- Twin of `projGuardFastC`: on the raw field telescope, `some` the
projected field's raw domain where no field's type up to the projected one,
and nothing after it, mentions a field before it; `j` counts the fields
passed. -/
def projGuardFast : Nat → Nat → Expr → Option Expr
  | k, j, .mdata _ e => projGuardFast k j e
  | 0, j, e@(.forallE _ dom _ _) => if EO.hasLooseBVarIn e 0 j then none else some dom
  | k + 1, j, .forallE _ dom body _ =>
    if EO.hasLooseBVarIn dom 0 j then none else projGuardFast k (j + 1) body
  | _, _, _ => none

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
