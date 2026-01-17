/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Init.Data.Int.Gcd
namespace Lean.Meta.Sym.Simp

/-!
# Ground Term Evaluation for `Sym.simp`

This module provides simplification procedures (`Simproc`) for evaluating ground terms
of builtin types. It is designed for the `Sym.Simp` simplifier and addresses
performance issues in the standard `Meta.Simp` simprocs.

## Design Differences from `Meta.Simp` Simprocs

### 1. Pure Value Extraction

The `getValue?` functions are pure (`OptionT Id`) rather than monadic (`MetaM`).
This is possible because `Sym` assumes terms are in canonical form, no `whnf` or
reduction is needed to recognize literals.

### 2. Proof by Definitional Equality

All evaluation steps produce `Eq.refl` proofs and. The kernel verifies correctness
by checking that the input and output are definitionally equal.

### 3. Specialized Lemmas for Predicates

Predicates (`<`, `≤`, `=`, etc.) use specialized lemmas that short-circuit the
standard `decide` proof chain:
```
-- Standard approach (Meta.Simp)
eq_true (of_decide_eq_true (h : decide (a < b) = true)) : (a < b) = True

-- Specialized lemma (Sym.Simp)
theorem Int.lt_eq_true (a b : Int) (h : decide (a < b) = true) : (a < b) = True :=
  eq_true (of_decide_eq_true h)
```

The simproc applies the lemma directly with `rfl` for `h`:
```
Int.lt_eq_true 5 7 rfl : (5 < 7) = True
```

This avoids reconstructing `Decidable` instances at each call site.

### 4. Maximal Sharing

Results are passed through `share` to maintain the invariant that structurally
equal subterms have pointer equality. This enables O(1) cache lookup in the
simplifier.

### 5. Type Dispatch via `match_expr`

Operations dispatch on the type expression directly. It assumes non-standard instances are
**not** used.

**TODO**: additional bit-vector operations, `Char`, `String` support
-/

def getNatValue? (e : Expr) : OptionT Id Nat := do
  let_expr OfNat.ofNat _ n _ := e | failure
  let .lit (.natVal n) := n | failure
  return n

def getIntValue? (e : Expr) : OptionT Id Int := do
  let_expr Neg.neg _ _ a := e | getNatValue? e
  let v : Int ← getNatValue? a
  return -v

def getRatValue? (e : Expr) : OptionT Id Rat := do
  let_expr HDiv.hDiv _ _ _ _ n d := e | getIntValue? e
  let n ← getIntValue? n
  let d ← getNatValue? d
  return n / d

structure BitVecValue where
  n : Nat
  val : BitVec n

def getBitVecValue? (e : Expr) : OptionT Id BitVecValue :=
  match_expr e with
  | BitVec.ofNat nExpr vExpr => do
    let n ← getNatValue? nExpr
    let v ← getNatValue? vExpr
    return ⟨n, BitVec.ofNat n v⟩
  | BitVec.ofNatLT nExpr vExpr _ => do
    let n ← getNatValue? nExpr
    let v ← getNatValue? vExpr
    return ⟨n, BitVec.ofNat n v⟩
  | OfNat.ofNat α v _ => do
    let_expr BitVec n := α | failure
    let n ← getNatValue? n
    let v ← getNatValue? v
    return ⟨n, BitVec.ofNat n v⟩
  | _ => failure

def getUInt8Value? (e : Expr) : OptionT Id UInt8 := return UInt8.ofNat (← getNatValue? e)
def getUInt16Value? (e : Expr) : OptionT Id UInt16 := return UInt16.ofNat (← getNatValue? e)
def getUInt32Value? (e : Expr) : OptionT Id UInt32 := return UInt32.ofNat (← getNatValue? e)
def getUInt64Value? (e : Expr) : OptionT Id UInt64 := return UInt64.ofNat (← getNatValue? e)
def getInt8Value? (e : Expr) : OptionT Id Int8 := return Int8.ofInt (← getIntValue? e)
def getInt16Value? (e : Expr) : OptionT Id Int16 := return Int16.ofInt (← getIntValue? e)
def getInt32Value? (e : Expr) : OptionT Id Int32 := return Int32.ofInt (← getIntValue? e)
def getInt64Value? (e : Expr) : OptionT Id Int64 := return Int64.ofInt (← getIntValue? e)

structure FinValue where
  n : Nat
  val : Fin n

def getFinValue? (e : Expr) : OptionT Id FinValue := do
  let_expr OfNat.ofNat α v _ := e | failure
  let_expr Fin n := α | failure
  let n ← getNatValue? n
  let .lit (.natVal v) := v | failure
  if h : n = 0 then failure else
  let : NeZero n := ⟨h⟩
  return { n, val := Fin.ofNat n v }

abbrev evalUnary [ToExpr α] (toValue? : Expr → Option α) (op : α → α) (a : Expr) : SimpM Result := do
  let some a := toValue? a | return .rfl
  let e ← share <| toExpr (op a)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) (ToExpr.toTypeExpr (α := α)) e) (done := true)

abbrev evalUnaryNat : (op : Nat → Nat) → (a : Expr) → SimpM Result := evalUnary getNatValue?
abbrev evalUnaryInt : (op : Int → Int) → (a : Expr) → SimpM Result := evalUnary getIntValue?
abbrev evalUnaryRat : (op : Rat → Rat) → (a : Expr) → SimpM Result := evalUnary getRatValue?
abbrev evalUnaryUInt8 : (op : UInt8 → UInt8) → (a : Expr) → SimpM Result := evalUnary getUInt8Value?
abbrev evalUnaryUInt16 : (op : UInt16 → UInt16) → (a : Expr) → SimpM Result := evalUnary getUInt16Value?
abbrev evalUnaryUInt32 : (op : UInt32 → UInt32) → (a : Expr) → SimpM Result := evalUnary getUInt32Value?
abbrev evalUnaryUInt64 : (op : UInt64 → UInt64) → (a : Expr) → SimpM Result := evalUnary getUInt64Value?
abbrev evalUnaryInt8 : (op : Int8 → Int8) → (a : Expr) → SimpM Result := evalUnary getInt8Value?
abbrev evalUnaryInt16 : (op : Int16 → Int16) → (a : Expr) → SimpM Result := evalUnary getInt16Value?
abbrev evalUnaryInt32 : (op : Int32 → Int32) → (a : Expr) → SimpM Result := evalUnary getInt32Value?
abbrev evalUnaryInt64 : (op : Int64 → Int64) → (a : Expr) → SimpM Result := evalUnary getInt64Value?

abbrev evalUnaryFin' (op : {n : Nat} → Fin n → Fin n) (αExpr : Expr) (a : Expr) : SimpM Result := do
  let some a := getFinValue? a | return .rfl
  let e ← share <| toExpr (op a.val)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) αExpr e) (done := true)

abbrev evalUnaryBitVec' (op : {n : Nat} → BitVec n → BitVec n) (αExpr : Expr) (a : Expr) : SimpM Result := do
  let some a := getBitVecValue? a | return .rfl
  let e ← share <| toExpr (op a.val)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) αExpr e) (done := true)

abbrev evalBin [ToExpr α] (toValue? : Expr → Option α) (op : α → α → α) (a b : Expr) : SimpM Result := do
  let some a := toValue? a | return .rfl
  let some b := toValue? b | return .rfl
  let e ← share <| toExpr (op a b)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) (ToExpr.toTypeExpr (α := α)) e) (done := true)

abbrev evalBinNat : (op : Nat → Nat → Nat) → (a b : Expr) → SimpM Result := evalBin getNatValue?
abbrev evalBinInt : (op : Int → Int → Int) → (a b : Expr) → SimpM Result := evalBin getIntValue?
abbrev evalBinRat : (op : Rat → Rat → Rat) → (a b : Expr) → SimpM Result := evalBin getRatValue?
abbrev evalBinUInt8 : (op : UInt8 → UInt8 → UInt8) → (a b : Expr) → SimpM Result := evalBin getUInt8Value?
abbrev evalBinUInt16 : (op : UInt16 → UInt16 → UInt16) → (a b : Expr) → SimpM Result := evalBin getUInt16Value?
abbrev evalBinUInt32 : (op : UInt32 → UInt32 → UInt32) → (a b : Expr) → SimpM Result := evalBin getUInt32Value?
abbrev evalBinUInt64 : (op : UInt64 → UInt64 → UInt64) → (a b : Expr) → SimpM Result := evalBin getUInt64Value?
abbrev evalBinInt8 : (op : Int8 → Int8 → Int8) → (a b : Expr) → SimpM Result := evalBin getInt8Value?
abbrev evalBinInt16 : (op : Int16 → Int16 → Int16) → (a b : Expr) → SimpM Result := evalBin getInt16Value?
abbrev evalBinInt32 : (op : Int32 → Int32 → Int32) → (a b : Expr) → SimpM Result := evalBin getInt32Value?
abbrev evalBinInt64 : (op : Int64 → Int64 → Int64) → (a b : Expr) → SimpM Result := evalBin getInt64Value?

abbrev evalBinFin' (op : {n : Nat} → Fin n → Fin n → Fin n) (αExpr : Expr) (a b : Expr) : SimpM Result := do
  let some a := getFinValue? a | return .rfl
  let some b := getFinValue? b | return .rfl
  if h : a.n = b.n then
    let e ← share <| toExpr (op a.val (h ▸ b.val))
    return .step e (mkApp2 (mkConst ``Eq.refl [1]) αExpr e) (done := true)
  else
    return .rfl

abbrev evalBinBitVec' (op : {n : Nat} → BitVec n → BitVec n → BitVec n) (αExpr : Expr) (a b : Expr) : SimpM Result := do
  let some a := getBitVecValue? a | return .rfl
  let some b := getBitVecValue? b | return .rfl
  if h : a.n = b.n then
    let e ← share <| toExpr (op a.val (h ▸ b.val))
    return .step e (mkApp2 (mkConst ``Eq.refl [1]) αExpr e) (done := true)
  else
    return .rfl

abbrev evalPowNat [ToExpr α] (maxExponent : Nat) (toValue? : Expr → Option α) (op : α → Nat → α) (a b : Expr) : SimpM Result := do
  let some a := toValue? a | return .rfl
  let some b := getNatValue? b | return .rfl
  if b > maxExponent then return .rfl
  let e ← share <| toExpr (op a b)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) (ToExpr.toTypeExpr (α := α)) e) (done := true)

abbrev evalPowInt [ToExpr α] (maxExponent : Nat) (toValue? : Expr → Option α) (op : α → Int → α) (a b : Expr) : SimpM Result := do
  let some a := toValue? a | return .rfl
  let some b := getIntValue? b | return .rfl
  if b.natAbs > maxExponent then return .rfl
  let e ← share <| toExpr (op a b)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) (ToExpr.toTypeExpr (α := α)) e) (done := true)

macro "declare_eval_bin" id:ident op:term : command =>
  `(def $id:ident (α : Expr) (a b : Expr) : SimpM Result :=
  match_expr α with
  | Nat => evalBinNat $op a b
  | Int => evalBinInt $op a b
  | Rat => evalBinRat $op a b
  | Fin _ => evalBinFin' $op α a b
  | BitVec _ => evalBinBitVec' $op α a b
  | UInt8 => evalBinUInt8 $op a b
  | UInt16 => evalBinUInt16 $op a b
  | UInt32 => evalBinUInt32 $op a b
  | UInt64 => evalBinUInt64 $op a b
  | Int8 => evalBinInt8 $op a b
  | Int16 => evalBinInt16 $op a b
  | Int32 => evalBinInt32 $op a b
  | Int64 => evalBinInt64 $op a b
  | _ => return .rfl
  )

declare_eval_bin evalAdd (· + ·)
declare_eval_bin evalSub (· - ·)
declare_eval_bin evalMul (· * ·)
declare_eval_bin evalDiv (· / ·)

def evalMod (α : Expr) (a b : Expr) : SimpM Result :=
  match_expr α with
  | Nat => evalBinNat (· % ·) a b
  | Int => evalBinInt (· % ·) a b
  | Fin _ => evalBinFin' (· % ·) α a b
  | BitVec _ => evalBinBitVec' (· % ·) α a b
  | UInt8 => evalBinUInt8 (· % ·) a b
  | UInt16 => evalBinUInt16 (· % ·) a b
  | UInt32 => evalBinUInt32 (· % ·) a b
  | UInt64 => evalBinUInt64 (· % ·) a b
  | Int8 => evalBinInt8 (· % ·) a b
  | Int16 => evalBinInt16 (· % ·) a b
  | Int32 => evalBinInt32 (· % ·) a b
  | Int64 => evalBinInt64 (· % ·) a b
  | _ => return .rfl

def evalNeg (α : Expr) (a : Expr) : SimpM Result :=
  match_expr α with
  | Int => evalUnaryInt (- ·) a
  | Rat => evalUnaryRat (- ·) a
  | Fin _ => evalUnaryFin' (- ·) α a
  | BitVec _ => evalUnaryBitVec' (- ·) α a
  | UInt8 => evalUnaryUInt8 (- ·) a
  | UInt16 => evalUnaryUInt16 (- ·) a
  | UInt32 => evalUnaryUInt32 (- ·) a
  | UInt64 => evalUnaryUInt64 (- ·) a
  | Int8 => evalUnaryInt8 (- ·) a
  | Int16 => evalUnaryInt16 (- ·) a
  | Int32 => evalUnaryInt32 (- ·) a
  | Int64 => evalUnaryInt64 (- ·) a
  | _ => return .rfl

def evalComplement (α : Expr) (a : Expr) : SimpM Result :=
  match_expr α with
  | Int => evalUnaryInt (~~~ ·) a
  | BitVec _ => evalUnaryBitVec' (~~~ ·) α a
  | UInt8 => evalUnaryUInt8 (~~~ ·) a
  | UInt16 => evalUnaryUInt16 (~~~ ·) a
  | UInt32 => evalUnaryUInt32 (~~~ ·) a
  | UInt64 => evalUnaryUInt64 (~~~ ·) a
  | Int8 => evalUnaryInt8 (~~~ ·) a
  | Int16 => evalUnaryInt16 (~~~ ·) a
  | Int32 => evalUnaryInt32 (~~~ ·) a
  | Int64 => evalUnaryInt64 (~~~ ·) a
  | _ => return .rfl

def evalInv (α : Expr) (a : Expr) : SimpM Result :=
  match_expr α with
  | Rat => evalUnaryRat (· ⁻¹) a
  | _ => return .rfl

macro "declare_eval_bin_bitwise" id:ident op:term : command =>
  `(def $id:ident (α : Expr) (a b : Expr) : SimpM Result :=
  match_expr α with
  | Nat => evalBinNat $op a b
  | Fin _ => evalBinFin' $op α a b
  | BitVec _ => evalBinBitVec' $op α a b
  | UInt8 => evalBinUInt8 $op a b
  | UInt16 => evalBinUInt16 $op a b
  | UInt32 => evalBinUInt32 $op a b
  | UInt64 => evalBinUInt64 $op a b
  | Int8 => evalBinInt8 $op a b
  | Int16 => evalBinInt16 $op a b
  | Int32 => evalBinInt32 $op a b
  | Int64 => evalBinInt64 $op a b
  | _ => return .rfl
  )

declare_eval_bin_bitwise evalAnd (· &&& ·)
declare_eval_bin_bitwise evalOr (· ||| ·)
declare_eval_bin_bitwise evalXOr (· ^^^ ·)

def evalPow (maxExponent : Nat) (α β : Expr) (a b : Expr) : SimpM Result :=
  match_expr β with
  | Nat => match_expr α with
    | Nat => evalPowNat maxExponent getNatValue? (· ^ ·) a b
    | Int => evalPowNat maxExponent getIntValue? (· ^ ·) a b
    | Rat => evalPowNat maxExponent getRatValue? (· ^ ·) a b
    | UInt8 => evalPowNat maxExponent getUInt8Value? (· ^ ·) a b
    | UInt16 => evalPowNat maxExponent getUInt16Value? (· ^ ·) a b
    | UInt32 => evalPowNat maxExponent getUInt32Value? (· ^ ·) a b
    | UInt64 => evalPowNat maxExponent getUInt64Value? (· ^ ·) a b
    | Int8 => evalPowNat maxExponent getInt8Value? (· ^ ·) a b
    | Int16 => evalPowNat maxExponent getInt16Value? (· ^ ·) a b
    | Int32 => evalPowNat maxExponent getInt32Value? (· ^ ·) a b
    | Int64 => evalPowNat maxExponent getInt64Value? (· ^ ·) a b
    | _ => return .rfl
  | Int => match_expr α with
    | Rat => evalPowInt maxExponent getRatValue? (· ^ ·) a b
    | _ => return .rfl
  | _ => return .rfl

abbrev shift [ShiftLeft α] [ShiftRight α] (left : Bool) (a b : α) : α :=
  if left then a <<< b else a >>> b

def evalShift (left : Bool) (α β : Expr) (a b : Expr) : SimpM Result :=
  if isSameExpr α β then
    match_expr α with
    | Nat => evalBinNat (shift left) a b
    | Fin _ => if left then evalBinFin' (· <<< ·) α a b else evalBinFin' (· >>> ·) α a b
    | BitVec _ => if left then evalBinBitVec' (· <<< ·) α a b else evalBinBitVec' (· >>> ·) α a b
    | UInt8 => evalBinUInt8 (shift left) a b
    | UInt16 => evalBinUInt16 (shift left) a b
    | UInt32 => evalBinUInt32 (shift left) a b
    | UInt64 => evalBinUInt64 (shift left) a b
    | Int8 => evalBinInt8 (shift left) a b
    | Int16 => evalBinInt16 (shift left) a b
    | Int32 => evalBinInt32 (shift left) a b
    | Int64 => evalBinInt64 (shift left) a b
    | _ => return .rfl
  else
  match_expr β with
  | Nat =>
    match_expr α with
    | Int => do
      let some a := getIntValue? a | return .rfl
      let some b := getNatValue? b | return .rfl
      let e := if left then a <<< b else a >>> b
      let e ← share <| toExpr e
      return .step e (mkApp2 (mkConst ``Eq.refl [1]) α e) (done := true)
    | BitVec _ => do
      let some a := getBitVecValue? a | return .rfl
      let some b := getNatValue? b | return .rfl
      let e := if left then a.val <<< b else a.val >>> b
      let e ← share <| toExpr e
      return .step e (mkApp2 (mkConst ``Eq.refl [1]) α e) (done := true)
    | _ => return .rfl
  | BitVec _ => do
    let_expr BitVec _ := α | return .rfl
    let some a := getBitVecValue? a | return .rfl
    let some b := getBitVecValue? b | return .rfl
    let e := if left then a.val <<< b.val else a.val >>> b.val
    let e ← share <| toExpr e
    return .step e (mkApp2 (mkConst ``Eq.refl [1]) α e) (done := true)
  | _ => return .rfl

def evalIntGcd (a b : Expr) : SimpM Result := do
  let some a := getIntValue? a | return .rfl
  let some b := getIntValue? b | return .rfl
  let e ← share <| toExpr (Int.gcd a b)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) Nat.mkType e) (done := true)

def evalIntBMod (a b : Expr) : SimpM Result := do
  let some a := getIntValue? a | return .rfl
  let some b := getNatValue? b | return .rfl
  let e ← share <| toExpr (Int.bmod a b)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) Int.mkType e) (done := true)

def evalIntBDiv (a b : Expr) : SimpM Result := do
  let some a := getIntValue? a | return .rfl
  let some b := getNatValue? b | return .rfl
  let e ← share <| toExpr (Int.bdiv a b)
  return .step e (mkApp2 (mkConst ``Eq.refl [1]) Int.mkType e) (done := true)

public structure EvalStepConfig where
  maxExponent := 255

/--
Simplification procedure that evaluates ground terms of builtin types.

**Important:** This procedure assumes subterms have already been simplified. It evaluates
a single operation on literal arguments only. For example:
- `2 + 3` → evaluates to `5`
- `2 + (3 * 4)` → returns `.rfl` (the argument `3 * 4` is not a literal)

The simplifier is responsible for term traversal, ensuring subterms are reduced
before `evalGround` is called on the parent expression.
-/
public def evalGround (config : EvalStepConfig := {}) : Simproc := fun e =>
  match_expr e with
  | HAdd.hAdd α _ _ _ a b => evalAdd α a b
  | HSub.hSub α _ _ _ a b => evalSub α a b
  | HMul.hMul α _ _ _ a b => evalMul α a b
  | HDiv.hDiv α _ _ _ a b => evalDiv α a b
  | HMod.hMod α _ _ _ a b => evalMod α a b
  | HPow.hPow α β _ _ a b => evalPow config.maxExponent α β a b
  | HAnd.hAnd α _ _ _ a b => evalAnd α a b
  | HXor.hXor α _ _ _ a b => evalXOr α a b
  | HOr.hOr α _ _ _ a b => evalOr α a b
  | HShiftLeft.hShiftLeft α β _ _ a b => evalShift (left := true) α β a b
  | HShiftRight.hShiftRight α β _ _ a b => evalShift (left := false) α β a b
  | Inv.inv α _ a => evalInv α a
  | Neg.neg α _ a => evalNeg α a
  | Complement.complement α _ a => evalComplement α a
  | Nat.gcd a b => evalBinNat Nat.gcd a b
  | Nat.succ a => evalUnaryNat (· + 1) a
  | Int.gcd a b => evalIntGcd a b
  | Int.tdiv a b => evalBinInt Int.tdiv a b
  | Int.fdiv a b => evalBinInt Int.fdiv a b
  | Int.bdiv a b => evalIntBDiv a b
  | Int.tmod a b => evalBinInt Int.tmod a b
  | Int.fmod a b => evalBinInt Int.fmod a b
  | Int.bmod a b => evalIntBMod a b
  | LE.le α _ a b => return .rfl
  | GE.ge α _ a b => return .rfl
  | LT.lt α _ a b => return .rfl
  | GT.gt α _ a b => return .rfl
  | Dvd.dvd α _ a b => return .rfl
  | Eq α a b => return .rfl
  | Ne α a b => return .rfl
  | BEq.beq α _ a b => return .rfl
  | bne α _ a b => return .rfl
  | _  => return .rfl

end Lean.Meta.Sym.Simp
