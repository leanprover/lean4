module

public import Lean
public meta import Lean

/-!
Tests literal classification, agreement between `isNatValue`/`isNonZeroNatValue`/`isLitValue`
and their value extractors, and `Grind.isInterpreted` on literals, non-normal literals, and near-literals.
-/

open Lean Meta Elab Term Command

def w := 8
def MyNat := Nat
instance : OfNat MyNat n := ⟨(n : Nat)⟩
opaque x : Int
opaque k : Nat

elab "#lit_check " t:term : command => liftTermElabM do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  logInfo m!"{e}: isLitValue := {← isLitValue e}, isInterpreted := {← Grind.isInterpreted e}"

/-- info: 3: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check (3 : Nat)
/-- info: -3: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check (-3 : Int)
/-- info: 3: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check (3 : Fin 5)
/-- info: 3: isLitValue := false, isInterpreted := false -/
#guard_msgs in #lit_check (3 : Fin (k + 1))
/-- info: 5: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check (5 : BitVec 8)
/-- info: 5: isLitValue := true, isInterpreted := false -/
#guard_msgs in #lit_check (5 : BitVec w)
/-- info: 5#8: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check BitVec.ofNat 8 5
/-- info: 5#k: isLitValue := false, isInterpreted := false -/
#guard_msgs in #lit_check BitVec.ofNat k 5
/-- info: 3#'⋯: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check (BitVec.ofNatLT 3 (by decide) : BitVec 4)
/-- info: 3: isLitValue := true, isInterpreted := false -/
#guard_msgs in #lit_check (3 : MyNat)
/-- info: 3: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check (3 : UInt8)
/-- info: 3: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check (3 : UInt64)
/-- info: 3: isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check (3 : Int8)
/-- info: 'a': isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check 'a'
/-- info: Char.ofNat k: isLitValue := false, isInterpreted := false -/
#guard_msgs in #lit_check Char.ofNat k
/-- info: "abc": isLitValue := true, isInterpreted := true -/
#guard_msgs in #lit_check "abc"
/-- info: 2.5: isLitValue := true, isInterpreted := false -/
#guard_msgs in #lit_check (2.5 : Float)
/-- info: -2.5: isLitValue := true, isInterpreted := false -/
#guard_msgs in #lit_check (-2.5 : Float32)
/-- info: 2: isLitValue := true, isInterpreted := false -/
#guard_msgs in #lit_check (2 : Float)
/-- info: -2: isLitValue := true, isInterpreted := false -/
#guard_msgs in #lit_check (-2 : Float)
/-- info: -x: isLitValue := false, isInterpreted := false -/
#guard_msgs in #lit_check -x
/-- info: x + 1: isLitValue := false, isInterpreted := false -/
#guard_msgs in #lit_check x + 1
/-- info: True: isLitValue := false, isInterpreted := true -/
#guard_msgs in #lit_check True

/-- info: ((some 3), (false, false)) -/
#guard_msgs in
run_meta do
  -- `Fin 0` has no `OfNat` instance; the instance argument is not inspected.
  let e := mkApp3 (mkConst ``OfNat.ofNat [0]) (mkApp (mkConst ``Fin) (mkNatLit 0)) (mkRawNatLit 3) (mkConst ``True)
  IO.println ((← getNatValue? (mkRawNatLit 3)), (← isLitValue e), (← Grind.isInterpreted e))

/-- info: (true, (true, (true, false))) -/
#guard_msgs in
run_meta do
  let n := mkNatLit 3
  IO.println ((← isLitValue (mkRawNatLit 3)), (← Grind.isInterpreted (.mdata {} (mkRawNatLit 3))),
    (← Grind.isInterpreted (.mdata {} n)), (← isLitValue (.mdata {} (mkStrLit "a"))))

example : (3 : Fin 5) + 1 = 4 := by grind
example : (5 : BitVec 8) + 1#8 = 6 := by grind
example (a : Int) : a = -3 → a + 3 = 0 := by grind
example (c : Char) : c = 'a' → c ≠ 'b' := by grind
example (u : UInt8) : u = 3 → u + 1 = 4 := by grind

namespace LitValueTests

/-- The extractors supported by `isLitValue`, including their value conversions. -/
meta def gettersRecognize (e : Expr) : MetaM Bool := do
  return [
    (← getNatValue? e).isSome,
    (← getIntValue? e).isSome,
    (← getRatValue? e).isSome,
    (← getFinValue? e).isSome,
    (← getBitVecValue? e).isSome,
    (getStringValue? e).isSome,
    (← getCharValue? e).isSome,
    (← getUInt8Value? e).isSome,
    (← getUInt16Value? e).isSome,
    (← getUInt32Value? e).isSome,
    (← getUInt64Value? e).isSome,
    (← getInt8Value? e).isSome,
    (← getInt16Value? e).isSome,
    (← getInt32Value? e).isSome,
    (← getInt64Value? e).isSome,
    (← getFloatValue? e).isSome,
    (← getFloat32Value? e).isSome
  ].any id

meta def checkConsistency (e : Expr) : MetaM Unit := do
  let expectedNat := (← getNatValue? e).isSome
  unless (← isNatValue e) == expectedNat do
    throwError "isNatValue disagrees with getNatValue?: {repr e}"
  unless (← isNonZeroNatValue e) == (← getNatValue? e).any (· != 0) do
    throwError "isNonZeroNatValue disagrees with getNatValue?: {repr e}"
  -- Unlike the individual extractors, `isLitValue` instantiates the whole expression.
  let expectedLit ← gettersRecognize (← instantiateMVars e)
  unless (← isLitValue e) == expectedLit do
    throwError "isLitValue disagrees with the value extractors: {repr e}"

/-- Insert metadata at each application, function, and argument position separately. -/
meta partial def metadataVariants (e : Expr) : Array Expr := Id.run do
  let mut result := #[.mdata {} e, .mdata {} (.mdata {} e)]
  if let .app f a := e then
    for f' in metadataVariants f do
      result := result.push (.app f' a)
    for a' in metadataVariants a do
      result := result.push (.app f a')
  return result

meta def checkClassifiers (e : Expr) (expectedLit expectedInterpreted : Bool) : MetaM Unit := do
  checkConsistency e
  let lit ← isLitValue e
  -- `grind` instantiates metavariables before calling `isInterpreted`.
  let interpreted ← Grind.isInterpreted (← instantiateMVars e)
  unless lit == expectedLit && interpreted == expectedInterpreted do
    throwError "classification of {repr e}: expected {(expectedLit, expectedInterpreted)}, got {(lit, interpreted)}"

elab "#check_lit " t:term " => " "(" expectedLit:ident ", " expectedInterpreted:ident ")" : command => liftTermElabM do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  for expected in [expectedLit, expectedInterpreted] do
    unless expected.getId == `true || expected.getId == `false do
      throwErrorAt expected "expected true or false"
  checkClassifiers e (expectedLit.getId == `true) (expectedInterpreted.getId == `true)
  for e' in metadataVariants e do
    checkConsistency e'
  let m ← mkFreshExprMVar (← inferType e)
  checkConsistency m
  m.mvarId!.assign e
  checkConsistency m

/-! Positive and negative coverage for every supported literal type and representation. -/

#check_lit (0 : Nat) => (true, true)
#check_lit (18446744073709551616 : Nat) => (true, true)
#check_lit (3 : Int) => (true, true)
#check_lit (-0 : Int) => (true, true)
#check_lit (-18446744073709551616 : Int) => (true, true)
#check_lit (257 : UInt8) => (true, true)
#check_lit (65537 : UInt16) => (true, true)
#check_lit (4294967297 : UInt32) => (true, true)
#check_lit (18446744073709551617 : UInt64) => (true, true)
#check_lit (3 : USize) => (false, false)
#check_lit (3 : ISize) => (false, false)
#check_lit (-3 : ISize) => (false, false)
#check_lit (@Neg.neg Nat ⟨id⟩ 3) => (false, false)
#check_lit (-(-3) : Int) => (false, false)
#check_lit Int.ofNat 3 => (false, false)
#check_lit Int.negSucc 3 => (false, false)
#check_lit Nat.succ 2 => (false, false)
#check_lit (OfNat.ofNat 3 : Nat) => (false, false)
#check_lit "" => (true, true)
#check_lit "λ🙂" => (true, true)
#check_lit '\x00' => (true, true)
#check_lit 'λ' => (true, true)
#check_lit Char.ofNat 0xD800 => (true, true)
#check_lit Char.ofNat 0x110000 => (true, true)
#check_lit Char.ofNat k => (false, false)
#check_lit True => (false, true)
#check_lit False => (false, true)
#check_lit true => (false, false)
#check_lit false => (false, false)
#check_lit x => (false, false)
#check_lit -x => (false, false)

/-! Rational literals must agree with `getRatValue?`, including its division representation. -/

opaque rat : Rat

#check_lit (0 : Rat) => (true, false)
#check_lit (3 : Rat) => (true, false)
#check_lit (-3 : Rat) => (true, false)
#check_lit (-0 : Rat) => (true, false)
#check_lit (18446744073709551616 : Rat) => (true, false)
#check_lit (3 / 4 : Rat) => (true, false)
#check_lit (-3 / 4 : Rat) => (true, false)
#check_lit (0 / 4 : Rat) => (true, false)
#check_lit (3 / 0 : Rat) => (true, false)
#check_lit (-3 / 0 : Rat) => (true, false)
#check_lit (0 / 0 : Rat) => (true, false)
#check_lit (6 / 8 : Rat) => (true, false)
#check_lit (-(3 / 4) : Rat) => (false, false)
#check_lit (3 / -4 : Rat) => (false, false)
#check_lit (3 / (-0) : Rat) => (false, false)
#check_lit (-(-3) : Rat) => (false, false)
#check_lit ((3 / 4) / 5 : Rat) => (false, false)
#check_lit (3 / (4 / 5) : Rat) => (false, false)
#check_lit rat => (false, false)
#check_lit -rat => (false, false)
#check_lit (rat / 4) => (false, false)
#check_lit (3 / rat) => (false, false)
#check_lit (OfNat.ofNat 3 : Rat) => (false, false)
#check_lit (OfNat.ofNat 3 / 4 : Rat) => (false, false)
#check_lit (3 / OfNat.ofNat 4 : Rat) => (false, false)
#check_lit (3 / 4 : Nat) => (false, false)
#check_lit (3 / 4 : Int) => (false, false)
#check_lit (3 / 4 : Float) => (false, false)
#check_lit (3 / 4 : Float32) => (false, false)

def MyRat := Rat
instance : OfNat MyRat n := ⟨@OfNat.ofNat Rat n inferInstance⟩
instance : Neg MyRat := ⟨fun n => @Neg.neg Rat inferInstance n⟩
instance : Div MyRat := ⟨fun a b => @Div.div Rat inferInstance a b⟩

#check_lit (3 : MyRat) => (true, false)
#check_lit (-3 : MyRat) => (true, false)
#check_lit (3 / 4 : MyRat) => (true, false)
#check_lit (-3 / 4 : MyRat) => (true, false)

instance : OfScientific MyRat := ⟨fun m s e => Rat.ofScientific m s e⟩

#check_lit (1.25 : Rat) => (true, false)
#check_lit (1.0 : Rat) => (true, false)
#check_lit (-1.0 : Rat) => (true, false)
#check_lit (-1.25 : Rat) => (true, false)
#check_lit (1.25e2 : Rat) => (true, false)
#check_lit (1.25e-2 : Rat) => (true, false)
#check_lit (-0.0 : Rat) => (true, false)
#check_lit (1.25 : MyRat) => (true, false)
#check_lit (-1.25 : MyRat) => (true, false)
#check_lit (1.25 / 2 : Rat) => (false, false)
#check_lit (-1.25 / 2 : Rat) => (false, false)
#check_lit (3 / 2.5 : Rat) => (false, false)
#check_lit (1.25 / 2.5 : Rat) => (false, false)
#check_lit (-1.25 / 2.5 : Rat) => (false, false)
#check_lit (1.25 / 0.0 : Rat) => (false, false)
#check_lit (1.0 / 2 : Rat) => (false, false)
#check_lit (3 / 2.0 : Rat) => (false, false)
#check_lit (3 / 0.0 : Rat) => (false, false)
#check_lit (3 / 2.5 : MyRat) => (false, false)
#check_lit (3 / -2.5 : Rat) => (false, false)
#check_lit (-(1.25 / 2) : Rat) => (false, false)
#check_lit (-(-1.25) : Rat) => (false, false)

run_meta do
  for r in [(0 : Rat), 1, -1, 3 / 4, -3 / 4, 18446744073709551617 / 19] do
    let e := toExpr r
    unless (← getRatValue? e) == some r do
      throwError "rational literal round trip failed: {repr e}"
    checkClassifiers e true false

run_meta do
  for (m, s, exp, expected) in [
      (125, true, 2, (5 / 4 : Rat)),
      (125, false, 2, (12500 : Rat)),
      (125, true, 0, (125 : Rat)),
      (0, true, 2, (0 : Rat))] do
    for mExpr in #[mkRawNatLit m, mkNatLit m] do
      for expExpr in #[mkRawNatLit exp, mkNatLit exp] do
        let e := mkApp5 (mkConst ``OfScientific.ofScientific [0]) (mkConst ``Rat)
          (mkConst ``True) mExpr (toExpr s) expExpr
        unless (← getRatValue? e) == some expected do
          throwError "incorrect scientific rational value: {repr e}"
        checkClassifiers e true false
        let neg := mkApp3 (mkConst ``Neg.neg [0]) (mkConst ``Rat) (mkConst ``True) e
        unless (← getRatValue? neg) == some (-expected) do
          throwError "incorrect negative scientific rational value: {repr neg}"
        checkClassifiers neg true false

example : (3 / 4 : Rat) + 1 / 4 = 1 := by grind
example (a : Rat) : a = -3 / 4 → 4 * a = -3 := by grind
example (a : Rat) (h : a = 1 / 2 → False) (ha : 2 * a = 1) : False := by grind
example (a : Rat) (h₁ : a = 1 / 2) (h₂ : a = 2 / 4) : a ≠ 0 := by grind
example (a : Rat) (h : a = 2 / 4) : a = 1 / 2 := by grind

/-!
Signed fixed-width literals are interpreted only in the form produced by `ToExpr`, since, e.g.,
`(200 : Int8)` and `(-56 : Int8)` denote the same value.
-/

#check_lit (3 : Int8) => (true, true)
#check_lit (3 : Int16) => (true, true)
#check_lit (3 : Int32) => (true, true)
#check_lit (3 : Int64) => (true, true)
#check_lit (-3 : Int8) => (true, true)
#check_lit (-3 : Int16) => (true, true)
#check_lit (-3 : Int32) => (true, true)
#check_lit (-3 : Int64) => (true, true)
#check_lit (0 : Int8) => (true, true)
#check_lit (-0 : Int8) => (true, false)
#check_lit (127 : Int8) => (true, true)
#check_lit (128 : Int8) => (true, false)
#check_lit (200 : Int8) => (true, false)
#check_lit (256 : Int8) => (true, false)
#check_lit (-128 : Int8) => (true, true)
#check_lit (-129 : Int8) => (true, false)
#check_lit (32767 : Int16) => (true, true)
#check_lit (32768 : Int16) => (true, false)
#check_lit (-32768 : Int16) => (true, true)
#check_lit (-32769 : Int16) => (true, false)
#check_lit (2147483647 : Int32) => (true, true)
#check_lit (2147483648 : Int32) => (true, false)
#check_lit (-2147483648 : Int32) => (true, true)
#check_lit (-2147483649 : Int32) => (true, false)
#check_lit (9223372036854775807 : Int64) => (true, true)
#check_lit (9223372036854775808 : Int64) => (true, false)
#check_lit (-9223372036854775808 : Int64) => (true, true)
#check_lit (-9223372036854775809 : Int64) => (true, false)
#check_lit (-(-3) : Int8) => (false, false)
#check_lit Int8.ofInt 3 => (false, false)

def MyInt8 := Int8
instance : OfNat MyInt8 n := ⟨(OfNat.ofNat n : Int8)⟩
instance : Neg MyInt8 := ⟨fun n => @Neg.neg Int8 Int8.instNeg n⟩

#check_lit (3 : MyInt8) => (true, false)
#check_lit (-3 : MyInt8) => (true, false)
#check_lit (@Neg.neg Int8 Int8.instNeg (3 : MyInt8)) => (true, false)

example (x : Int8) (h : x = @Neg.neg Int8 Int8.instNeg (3 : MyInt8))
    (h' : x = -3) : x = -3 := by
  grind -lia -ring -order -linarith -hom

meta def mkSignedLiteral (typeName : Name) (negative : Bool) (n : Nat) : Expr :=
  let type := Lean.mkConst typeName
  let n := mkRawNatLit n
  let e := mkApp3 (mkConst ``OfNat.ofNat [0]) type n
    (mkApp (mkConst (typeName ++ `instOfNat)) n)
  if negative then
    mkApp3 (mkConst ``Neg.neg [0]) type (mkConst (typeName ++ `instNeg)) e
  else e

meta def checkSignedValues (typeName : Name) (width : Nat)
    (getValue : Expr → MetaM (Option Int)) : MetaM Unit := do
  let modulus := 2 ^ width
  let half := modulus / 2
  let magnitudes := if width == 8 then (List.range (2 * modulus + 1)).toArray else
    #[0, 1, half - 1, half, half + 1, modulus - 1, modulus, modulus + 1,
      2 * modulus - 1, 2 * modulus, 2 * modulus + 1, 2 ^ 128 + half]
  for n in magnitudes do
    for negative in [false, true] do
      let e := mkSignedLiteral typeName negative n
      let i : Int := if negative then -(n : Int) else n
      let residue := i % modulus
      let expected := if residue < half then residue else residue - modulus
      unless (← getValue e) == some expected do
        throwError "incorrect signed literal value: {repr e}"
      let interpreted := if negative then 0 < n && n ≤ half else n < half
      checkClassifiers e true interpreted
      let normalized ← normLitValue e
      unless normalized == mkSignedLiteral typeName (expected < 0) expected.natAbs do
        throwError "incorrect signed literal normal form: {repr e}"
      unless (← getValue normalized) == some expected do
        throwError "normalization changed signed literal value: {repr e}"
      checkClassifiers normalized true true
      unless (← normLitValue normalized) == normalized do
        throwError "signed literal normalization is not idempotent: {repr e}"

set_option maxHeartbeats 2000000 in
run_meta do
  checkSignedValues ``Int8 8 fun e => return (← getInt8Value? e).map Int8.toInt
  checkSignedValues ``Int16 16 fun e => return (← getInt16Value? e).map Int16.toInt
  checkSignedValues ``Int32 32 fun e => return (← getInt32Value? e).map Int32.toInt
  checkSignedValues ``Int64 64 fun e => return (← getInt64Value? e).map Int64.toInt

run_meta do
  for typeName in [``Int8, ``Int16, ``Int32, ``Int64] do
    let type := Lean.mkConst typeName
    let e := mkSignedLiteral typeName false 3
    let neg := mkApp2 (mkConst ``Neg.neg [0]) type (mkConst (typeName ++ `instNeg))
    checkClassifiers (mkApp neg (mkRawNatLit 3)) false false
    checkClassifiers (mkApp neg (mkApp neg e)) false false
    checkClassifiers e.appFn! false false
    checkClassifiers (mkApp e (mkRawNatLit 0)) false false
    -- A reducible inner type is a literal, but cannot identify an interpreted term.
    let alias := mkLet `T (mkSort 1) type (mkBVar 0)
    let aliased := mkApp3 (mkConst ``OfNat.ofNat [0]) alias e.appFn!.appArg! e.appArg!
    checkClassifiers (mkApp neg aliased) true false
    let value ← mkFreshExprMVar (mkConst ``Nat)
    let unresolved := mkApp3 (mkConst ``OfNat.ofNat [0]) type value
      (mkApp (mkConst (typeName ++ `instOfNat)) value)
    checkClassifiers (mkApp neg unresolved) false false
    value.mvarId!.assign (mkRawNatLit 3)
    checkClassifiers (mkApp neg unresolved) true true

run_meta do
  for i in [(0 : Int), 1, -1, 127, -128, 200, -200, 128, -129, 256, -256] do
    let e ← normLitValue (toExpr (Int8.ofInt i))
    unless (← getInt8Value? e) == some (Int8.ofInt i) do
      throwError "signed literal round trip failed: {repr e}"
    checkClassifiers e true true
    unless (← normLitValue e) == e do
      throwError "`normLitValue` is not idempotent: {repr e}"
  for i in [(0 : Int), 9223372036854775807, -9223372036854775808] do
    checkClassifiers (toExpr (Int64.ofInt i)) true true

elab "#norm_lit " t:term : command => liftTermElabM do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  logInfo m!"{← normLitValue (← instantiateMVars e)}"

/-- info: -56 -/
#guard_msgs in #norm_lit (200 : Int8)
/-- info: 0 -/
#guard_msgs in #norm_lit (-0 : Int8)
/-- info: -128 -/
#guard_msgs in #norm_lit (128 : Int8)
/-- info: 56 -/
#guard_msgs in #norm_lit (-200 : Int8)
/-- info: -1 -/
#guard_msgs in #norm_lit (65535 : Int16)
/-- info: 3 -/
#guard_msgs in #norm_lit (3 : MyInt8)

example (a : Int8) : a = 3 → a ≠ 4 := by grind
example (a : Int8) : a = -3 → a ≠ 3 := by grind
example (a : Int8) (h : a = 200) : a = -56 := by grind
example (a : Int8) (h : a = 128) : a = -128 := by grind
example (a : Int8) (h : a = -0) : a = 0 := by grind
example (a : Int64) (h : a = -9223372036854775808) : a ≠ 9223372036854775807 := by grind
example (a : Int8) (h₁ : a = 3) (h₂ : a = 4) : False := by grind
example (a : Int8) (h₁ : a = -1) (h₂ : a = 255) : a + 1 = 0 := by grind

/-!
With every solver disabled, only interpreted literals can refute these goals. The canonicalizer
reduces out-of-range numerals modulo `2^w` (e.g., `(264 : Int8)` to `8`), but the remaining
spellings of a value, e.g., `(128 : Int8)` and `-128`, are not interpreted and must not be refuted.
-/

-- `Int8`
example (x y : Int8) : x = 8 → x = y → y = 7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = -8 → x = y → y = 8 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = -8 → x = y → y = -7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = 0 → x = y → y = -1 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = -128 → x = y → y = 127 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = 127 → x = y → y = 126 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = -128 → x = y → y = -127 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = 264 → x = y → y = 7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = 256 → x = y → y = -1 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int8) : x = 8 → x = y → y = 7 → x = 8 := by grind -lia -ring -order -linarith -hom
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int8) : x = 263 → x = y → y = 7 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int8) : x = 128 → x = y → y = -128 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int8) : x = -0 → x = y → y = 0 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int8) : x = 255 → x = y → y = -1 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry

-- `Int16`
example (x y : Int16) : x = 8 → x = y → y = 7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = -8 → x = y → y = 8 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = -8 → x = y → y = -7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = 0 → x = y → y = -1 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = -32768 → x = y → y = 32767 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = 32767 → x = y → y = 32766 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = -32768 → x = y → y = -32767 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = 65544 → x = y → y = 7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = 65536 → x = y → y = -1 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int16) : x = 8 → x = y → y = 7 → x = 8 := by grind -lia -ring -order -linarith -hom
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int16) : x = 65543 → x = y → y = 7 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int16) : x = 32768 → x = y → y = -32768 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int16) : x = -0 → x = y → y = 0 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int16) : x = 65535 → x = y → y = -1 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry

-- `Int32`
example (x y : Int32) : x = 8 → x = y → y = 7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = -8 → x = y → y = 8 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = -8 → x = y → y = -7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = 0 → x = y → y = -1 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = -2147483648 → x = y → y = 2147483647 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = 2147483647 → x = y → y = 2147483646 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = -2147483648 → x = y → y = -2147483647 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = 4294967304 → x = y → y = 7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = 4294967296 → x = y → y = -1 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int32) : x = 8 → x = y → y = 7 → x = 8 := by grind -lia -ring -order -linarith -hom
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int32) : x = 4294967303 → x = y → y = 7 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int32) : x = 2147483648 → x = y → y = -2147483648 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int32) : x = -0 → x = y → y = 0 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int32) : x = 4294967295 → x = y → y = -1 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry

-- `Int64`
example (x y : Int64) : x = 8 → x = y → y = 7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = -8 → x = y → y = 8 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = -8 → x = y → y = -7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = 0 → x = y → y = -1 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = -9223372036854775808 → x = y → y = 9223372036854775807 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = 9223372036854775807 → x = y → y = 9223372036854775806 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = -9223372036854775808 → x = y → y = -9223372036854775807 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = 18446744073709551624 → x = y → y = 7 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = 18446744073709551616 → x = y → y = -1 → False := by grind -lia -ring -order -linarith -hom
example (x y : Int64) : x = 8 → x = y → y = 7 → x = 8 := by grind -lia -ring -order -linarith -hom
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int64) : x = 18446744073709551623 → x = y → y = 7 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int64) : x = 9223372036854775808 → x = y → y = -9223372036854775808 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int64) : x = -0 → x = y → y = 0 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (x y : Int64) : x = 18446744073709551615 → x = y → y = -1 → False := by
  fail_if_success grind -lia -ring -order -linarith -hom
  sorry

/-! Bounds and widths may be reduced for `OfNat`, but must be syntactic numerals for interpretation. -/

#check_lit (0 : Fin 1) => (true, true)
#check_lit (100 : Fin 3) => (true, true)
#check_lit (3 : Fin (2 + 3)) => (true, false)
#check_lit (3 : Fin (k + 1)) => (false, false)
#check_lit (3 : BitVec 0) => (true, true)
#check_lit (257 : BitVec 8) => (true, true)
#check_lit (3 : BitVec (2 + 3)) => (true, false)
#check_lit (3 : BitVec w) => (true, false)
#check_lit (3 : BitVec k) => (false, false)
#check_lit BitVec.ofNat 0 3 => (true, true)
#check_lit BitVec.ofNat 8 257 => (true, true)
#check_lit BitVec.ofNat w 3 => (false, false)
#check_lit BitVec.ofNat 8 k => (false, false)
#check_lit BitVec.ofNat k 3 => (false, false)
#check_lit (BitVec.ofNatLT 0 (by decide) : BitVec 0) => (true, true)
#check_lit (BitVec.ofNatLT 3 (by decide) : BitVec 4) => (true, true)

def MyInt := Int
instance : OfNat MyInt n := ⟨(n : Int)⟩
instance : Neg MyInt := ⟨fun n => @Neg.neg Int Int.instNegInt n⟩
def MyBitVec := BitVec 8
instance : OfNat MyBitVec n := ⟨BitVec.ofNat 8 n⟩
def MyFin := Fin 5
instance : OfNat MyFin n := ⟨Fin.ofNat 5 n⟩
def MyFloat := Float
instance : OfNat MyFloat n := ⟨Float.ofNat n⟩

#check_lit (3 : MyNat) => (true, false)
#check_lit (3 : MyInt) => (true, false)
#check_lit (-3 : MyInt) => (true, false)
#check_lit (@Neg.neg Int Int.instNegInt (3 : MyInt)) => (true, false)
#check_lit (3 : MyBitVec) => (true, false)
#check_lit (3 : MyFin) => (true, false)
#check_lit (3 : MyFloat) => (true, false)

example (x : Int) (h : x = @Neg.neg Int Int.instNegInt (3 : MyInt))
    (h' : x = -3) : x = -3 := by
  grind -lia -ring -order -linarith -hom

/-! Both float types support natural and scientific literals, with one optional negation. -/

#check_lit (2 : Float) => (true, false)
#check_lit (-2 : Float) => (true, false)
#check_lit (2.5 : Float) => (true, false)
#check_lit (-2.5 : Float) => (true, false)
#check_lit (2 : Float32) => (true, false)
#check_lit (-2 : Float32) => (true, false)
#check_lit (2.5 : Float32) => (true, false)
#check_lit (-2.5 : Float32) => (true, false)
#check_lit (-0.0 : Float) => (true, false)
#check_lit (-0.0 : Float32) => (true, false)
#check_lit (1e400 : Float) => (true, false)
#check_lit (1e-400 : Float) => (true, false)
#check_lit (-(-2.5) : Float) => (false, false)
#check_lit Float.ofNat 2 => (false, false)
#check_lit Float32.ofNat 2 => (false, false)

opaque sign : Bool

#check_lit (OfScientific.ofScientific 25 true 1 : Float) => (true, false)
#check_lit (OfScientific.ofScientific 25 false 1 : Float32) => (true, false)
#check_lit (OfScientific.ofScientific k true 1 : Float) => (false, false)
#check_lit (OfScientific.ofScientific 25 sign 1 : Float) => (false, false)
#check_lit (OfScientific.ofScientific 25 true k : Float) => (false, false)
#check_lit (OfScientific.ofScientific k true 1 : Float32) => (false, false)
#check_lit (OfScientific.ofScientific 25 sign 1 : Float32) => (false, false)
#check_lit (OfScientific.ofScientific 25 true k : Float32) => (false, false)
#check_lit (-(OfScientific.ofScientific 25 sign 1) : Float) => (false, false)
#check_lit (-(OfScientific.ofScientific 25 true k) : Float32) => (false, false)
#check_lit (OfScientific.ofScientific 25 true 1 : Rat) => (true, false)
#check_lit (OfScientific.ofScientific 25 false 1 : Rat) => (true, false)
#check_lit (OfScientific.ofScientific k true 1 : Rat) => (false, false)
#check_lit (OfScientific.ofScientific 25 sign 1 : Rat) => (false, false)
#check_lit (OfScientific.ofScientific 25 true k : Rat) => (false, false)
#check_lit (-(OfScientific.ofScientific 25 sign 1) : Rat) => (false, false)

/-! The extractors recognize numeral syntax without inspecting the instance. -/

#check_lit (@OfNat.ofNat Nat (nat_lit 3) ⟨k⟩) => (true, true)
#check_lit (3 : BitVec (@OfNat.ofNat Nat (nat_lit 5) ⟨k⟩)) => (false, false)
#check_lit BitVec.ofNat (@OfNat.ofNat Nat (nat_lit 5) ⟨k⟩) 3 => (true, true)

/-! Raw literals, malformed near-literals, and metavariables inside literal applications. -/

run_meta do
  for n in [0, 1, 3, 18446744073709551616] do
    for e in #[mkRawNatLit n, mkNatLit n] do
      unless (← isNatValue e) do throwError "expected a natural literal"
      checkClassifiers e true true
      for e' in metadataVariants e do
        checkConsistency e'
  checkClassifiers (.mdata {} (mkStrLit "a")) false false
  let mkOfNat type n := mkApp3 (mkConst ``OfNat.ofNat [0]) type n (mkConst ``True)
  for n in #[mkRawNatLit 0, mkNatLit 0, mkConst ``k] do
    let e := mkOfNat (mkApp (mkConst ``Fin) n) (mkRawNatLit 3)
    checkClassifiers e false false
  for name in [``Nat, ``Int, ``Rat, ``UInt8, ``UInt16, ``UInt32, ``UInt64,
      ``Int8, ``Int16, ``Int32, ``Int64, ``Float, ``Float32] do
    for n in #[mkNatLit 3, mkConst ``k, mkStrLit "3"] do
      checkClassifiers (mkOfNat (mkConst name) n) false false
  let type ← mkFreshExprMVar (mkSort 1)
  let e := mkOfNat type (mkRawNatLit 3)
  checkClassifiers e false false
  type.mvarId!.assign (mkConst ``Nat)
  checkClassifiers e true true
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let e := mkOfNat (mkConst ``Nat) n
  checkClassifiers e false false
  n.mvarId!.assign (mkRawNatLit 3)
  checkClassifiers e true true
  -- `isNatValue`, like `getNatValue?`, does not instantiate the numeral argument.
  unless !(← isNatValue e) do throwError "unexpected metavariable instantiation"
  let width ← mkFreshExprMVar (mkConst ``Nat)
  let e := mkOfNat (mkApp (mkConst ``BitVec) width) (mkRawNatLit 3)
  checkClassifiers e false false
  width.mvarId!.assign (mkNatLit 8)
  checkClassifiers e true true

run_meta do
  -- Recognition of `ofNatLT` ignores the proof, just as `OfNat` ignores its instance.
  for name in [``BitVec.ofNat, ``BitVec.ofNatLT] do
    for width in #[mkRawNatLit 8, mkNatLit 8, mkConst ``w, mkConst ``k] do
      for value in #[mkRawNatLit 3, mkNatLit 3, mkConst ``k] do
        let e := mkApp2 (mkConst name) width value
        let e := if name == ``BitVec.ofNatLT then mkApp e (mkConst ``True) else e
        let expected := (← getNatValue? width).isSome && (← getNatValue? value).isSome
        checkClassifiers e expected expected
        for e' in metadataVariants e do
          checkConsistency e'
  for name in [``Rat, ``Float, ``Float32] do
    let mantissa ← mkFreshExprMVar (mkConst ``Nat)
    let decimal ← mkFreshExprMVar (mkConst ``Bool)
    let exponent ← mkFreshExprMVar (mkConst ``Nat)
    let e := mkApp5 (mkConst ``OfScientific.ofScientific [0]) (mkConst name)
      (mkConst ``True) mantissa decimal exponent
    checkClassifiers e false false
    mantissa.mvarId!.assign (mkRawNatLit 25)
    checkClassifiers e false false
    decimal.mvarId!.assign (mkConst ``Bool.true)
    checkClassifiers e false false
    exponent.mvarId!.assign (mkRawNatLit 1)
    checkClassifiers e true false
  for e in #[mkNatLit 3, toExpr (-3 : Int), toExpr 'a'] do
    checkClassifiers e.appFn! false false
    checkClassifiers (mkApp e (mkRawNatLit 0)) false false

end LitValueTests
