import Lean

/-!
# Tests for `Sym.Arith.normalize?`

Polynomial normalization of `CommRing`/`CommSemiring` terms with proofs by reflection.
Each proof is checked by the kernel through `addDecl`. Also a property test comparing the
guarded polynomial mirror (`Sym.Arith.toPoly?`) with the `Init` functions.
-/

open Lean Meta Sym Arith

def getDefValue (n : Name) : MetaM Expr := do
  let some (.defnInfo info) := (← getEnv).find? n
    | throwError "expected definition: {n}"
  return info.value

/--
Normalizes the body of `n` (atoms simplified by `simpAtom`, side conditions proved by
`discharge?`), prints the result, and kernel-checks the proof.
-/
def test (n : Name) (simpAtom : Expr → SymM Sym.Simp.Result := fun _ => return .rfl)
    (discharge? : Expr → SymM (Option Expr) := fun _ => return none) : SymM Unit := do
  let e ← preprocessExpr (← getDefValue n)
  let cd (b : Bool) : String := if b then " (context-dependent)" else ""
  match (← normalize? e simpAtom discharge?) with
  | .rfl false _ => logInfo m!"{n}: unchanged"
  | .rfl true b => logInfo m!"{n}: {e} (normal){cd b}"
  | .step e' h done b =>
    addDecl <| .thmDecl { name := n ++ `norm, levelParams := [], type := ← mkEq e e', value := h }
    logInfo m!"{n}: {e'}{if done then "" else " (not done)"}{cd b}"

opaque a : Int
opaque b : Int
opaque c : Int
opaque d : Int

def t1 : Int := 0 + a * (0 + b + (0 + c + (0 + d)))
def t2 : Int := (a + 1)^2
def t3 : Int := a - a
def t4 : Int := 2 + a
def t5 : Int := a + b
def t6 : Int := b + a
def t7 : Int := -a
def t8 : Int := a - b
def t9 : Int := (if a = b then a else b) + a * 2 + (if a = b then a else b)
def t10 : Int := 2 + 3
def t11 : Int := a * b * a - b * a ^ 2
def t12 : Int := ((a + b) * (a - b)) ^ 2

/--
info: t1: a * b + a * c + a * d
---
info: t2: a ^ 2 + 2 * a + 1
---
info: t3: 0
---
info: t4: a + 2
---
info: t5: a + b (normal)
---
info: t6: a + b
---
info: t7: -1 * a
---
info: t8: a + -1 * b
---
info: t9: 2 * a + 2 * if a = b then a else b
---
info: t10: 5
---
info: t11: 0
---
info: t12: a ^ 4 + -2 * (a ^ 2 * b ^ 2) + b ^ 4
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``t1, ``t2, ``t3, ``t4, ``t5, ``t6, ``t7, ``t8, ``t9, ``t10, ``t11, ``t12] do
    test n

-- `a + b` and `b + a` have the same (pointer-equal) normal form, and normal forms are fixpoints.
/-- info: same=true, fixpoint=true -/
#guard_msgs in
run_meta SymM.run do
  let e₅ ← preprocessExpr (← getDefValue ``t5)
  let e₆ ← preprocessExpr (← getDefValue ``t6)
  let r₅ := (← normalize? e₅ fun _ => return .rfl).getResultExpr e₅
  let r₆ := (← normalize? e₆ fun _ => return .rfl).getResultExpr e₆
  let fixpoint := (← normalize? r₅ fun _ => return .rfl) matches .rfl true _
  logInfo m!"same={isSameExpr r₅ r₆}, fixpoint={fixpoint}"

opaque x : Nat
opaque y : Nat

def n1 : Nat := 2 * x + x
def n2 : Nat := (x - y) + y + (x - y)
def n3 : Nat := x ^ 0
def n4 : Nat := (x + 1) * (x + 1)
def n5 : Nat := x + 0

/--
info: n1: 3 * x
---
info: n2: y + 2 * (x - y)
---
info: n3: 1
---
info: n4: x ^ 2 + 2 * x + 1
---
info: n5: x
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``n1, ``n2, ``n3, ``n4, ``n5] do
    test n

opaque u : UInt8
opaque v : UInt8

def c1 : UInt8 := 256 * u + v
def c2 : UInt8 := u - v

/--
info: c1: v
---
info: c2: u + 255 * v
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``c1, ``c2] do
    test n

-- Not arithmetic terms.
def s1 : Int := a
def s2 : Int → Int := fun z => z

/--
info: s1: unchanged
---
info: s2: unchanged
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``s1, ``s2] do
    test n

-- Budget.
def big : Int := (a + 1) ^ 100

/-- info: big: unchanged -/
#guard_msgs in
set_option sym.arith.maxDegree 8 in
run_meta SymM.run do
  test ``big

/-- info: big: unchanged -/
#guard_msgs in
set_option sym.arith.maxTerms 8 in
run_meta SymM.run do
  test ``big

/-! ## Relations -/

def r1 : Prop := a + b = c + 2 * a
def r2 : Prop := a ≤ b + a
def r3 : Prop := a < a + 1
def r4 : Prop := a * b + c = c + b * a
def r5 : Prop := a = b
def r6 : Prop := a = 5
def r7 : Prop := (a + b) ^ 2 ≤ a ^ 2 + b ^ 2
def r8 : Prop := 2 * a < b - a

/--
info: r1: b = a + c
---
info: r2: 0 ≤ b
---
info: r3: 0 < 1
---
info: r4: 0 = 0
---
info: r5: a = b (normal)
---
info: r6: a = 5 (normal)
---
info: r7: 2 * (a * b) ≤ 0
---
info: r8: 3 * a < b
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``r1, ``r2, ``r3, ``r4, ``r5, ``r6, ``r7, ``r8] do
    test n

def nr1 : Prop := x + y = y + 2 * x
def nr2 : Prop := x ≤ x + y
def nr3 : Prop := x + 1 < x + 2
def nr4 : Prop := (x + y) * (x + y) = x * x + 2 * x * y + y * y
def nr5 : Prop := 2 * x + 3 ≤ y + x + 1
def nr6 : Prop := x * y = y * x + 0

/--
info: nr1: 0 = x
---
info: nr2: 0 ≤ y
---
info: nr3: 0 < 1
---
info: nr4: 0 = 0
---
info: nr5: x + 2 ≤ y
---
info: nr6: 0 = 0
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``nr1, ``nr2, ``nr3, ``nr4, ``nr5, ``nr6] do
    test n

-- Relations over a ring with a nonzero characteristic.
def cr1 : Prop := 256 * u + v = v
def cr2 : Prop := 255 * u = u * 3 - 4 * u
def cr3 : Prop := u + 2 = v

/--
info: cr1: 0 = 0
---
info: cr2: 0 = 0
---
info: cr3: u + 2 = v (normal)
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``cr1, ``cr2, ``cr3] do
    test n

-- A relation over a type that does not classify is untouched.
def sr1 : Prop := "a" ++ "b" = "ab"

/-- info: sr1: unchanged -/
#guard_msgs in
run_meta SymM.run do
  test ``sr1

/-! ## Fields of characteristic zero: numeral inverses are rational coefficients -/

opaque r : Rat
opaque s : Rat

def f1 : Rat := r / 2 + r / 2
def f2 : Rat := r / 2 + s / 3
def f3 : Rat := r / 2 * 2
def f4 : Rat := (r / 2) ^ 2
def f5 : Rat := (1 : Rat) / 2 + 1 / 3
def f6 : Rat := r / (-2)
def f7 : Rat := (r + s) / 2 * (r - s) / 2
def f8 : Rat := r * 2⁻¹ + s * 3⁻¹
def f9 : Rat := (3 * r + 2 * s) * 6⁻¹
def f10 : Rat := r / 6 + r / 3
def fr1 : Prop := r / 2 = s / 3
def fr2 : Prop := r / 2 ≤ s
def fr3 : Prop := r / 2 < r
def fr4 : Prop := r / 3 + s / 3 = (r + s) / 3

/--
info: f1: r
---
info: f2: (3 * r + 2 * s) * 6⁻¹
---
info: f3: r
---
info: f4: r ^ 2 * 4⁻¹
---
info: f5: 5 * 6⁻¹
---
info: f6: -1 * r * 2⁻¹
---
info: f7: (r ^ 2 + -1 * s ^ 2) * 4⁻¹
---
info: f8: (3 * r + 2 * s) * 6⁻¹
---
info: f9: (3 * r + 2 * s) * 6⁻¹ (normal)
---
info: f10: r * 2⁻¹
---
info: fr1: 3 * r = 2 * s
---
info: fr2: r ≤ 2 * s
---
info: fr3: 0 < r
---
info: fr4: 0 = 0
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``f1, ``f2, ``f3, ``f4, ``f5, ``f6, ``f7, ``f8, ``f9, ``f10, ``fr1, ``fr2, ``fr3, ``fr4] do
    test n

/-! ## Fields: `x * x⁻¹` is cancelled when the side condition `x ≠ 0` is discharged -/

axiom r_ne_zero : r ≠ 0

/-- Proves `r ≠ 0` and nothing else. -/
def dischargeR (p : Expr) : SymM (Option Expr) := do
  let_expr Ne _ x _ := p | return none
  if x == mkConst ``r then return some (mkConst ``r_ne_zero) else return none

def fa1 : Rat := r / r
def fa2 : Rat := r * s / r
def fa3 : Rat := r ^ 3 * r⁻¹
def fa4 : Rat := s / s
def fa5 : Rat := r / (2 * r)
def fa6 : Rat := r⁻¹ * s
-- The inverse of a sum is an atom; its cancellation is left to `grind`.
def fa7 : Rat := (r + s) / (r + s)
def far1 : Prop := r / r = 1
def far2 : Prop := r * s / r ≤ s
def far3 : Prop := s / s = 1

/--
info: fa1: 1 (context-dependent)
---
info: fa2: s (context-dependent)
---
info: fa3: r ^ 2 (context-dependent)
---
info: fa4: s * s⁻¹ (context-dependent)
---
info: fa5: 2⁻¹ (context-dependent)
---
info: fa6: s * r⁻¹
---
info: fa7: r * (r + s)⁻¹ + s * (r + s)⁻¹
---
info: far1: 0 = 0 (context-dependent)
---
info: far2: 0 ≤ 0 (context-dependent)
---
info: far3: s * s⁻¹ = 1 (context-dependent)
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``fa1, ``fa2, ``fa3, ``fa4, ``fa5, ``fa6, ``fa7, ``far1, ``far2, ``far3] do
    test n (discharge? := dischargeR)

/-! ## Atoms are simplified by the callback before normalization -/

def p : Int := 1
def q : Int := 1
theorem pq : p = q := rfl

/-- Rewrites the atom `p` to `q`. -/
def simpP (e : Expr) : SymM Sym.Simp.Result := do
  if e == mkConst ``p then
    return .step (← share (mkConst ``q)) (mkConst ``pq)
  else
    return .rfl

def ap1 : Int := p + p
def ap2 : Int := 2 * q
def ap3 : Int := 2 * p
def ap4 : Int := (p + a) * (p - a)

/--
info: ap1: 2 * q
---
info: ap2: 2 * q (normal)
---
info: ap3: 2 * q
---
info: ap4: -1 * a ^ 2 + q ^ 2
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``ap1, ``ap2, ``ap3, ``ap4] do
    test n simpP

-- The atom rewrite is kept (with `done := false`) when the budget is exceeded.
def ap5 : Int := (p + 1) ^ 100

/-- info: ap5: (q + 1) ^ 100 (not done) -/
#guard_msgs in
set_option sym.arith.maxDegree 8 in
run_meta SymM.run do
  test ``ap5 simpP

/-! ## Property test: the guarded mirror agrees with the `Init` functions -/

open Lean.Grind.CommRing in
def leaves : List RingExpr :=
  [.num (-2), .num 0, .num 3, .var 0, .var 1, .natCast 2, .intCast (-1)]

open Lean.Grind.CommRing in
def grow (es : List RingExpr) (ls : List RingExpr) : List RingExpr :=
  es.flatMap fun e =>
    ls.flatMap (fun l => [.add e l, .mul e l, .sub e l, .add l e, .mul l e])
    ++ [.neg e, .pow e 0, .pow e 1, .pow e 2, .pow e 3]

open Lean.Grind.CommRing in
def isSemiringExpr : RingExpr → Bool
  | .num k => k ≥ 0
  | .natCast _ | .var _ => true
  | .intCast _ | .sub .. | .neg .. => false
  | .add a b | .mul a b => isSemiringExpr a && isSemiringExpr b
  | .pow a _ => isSemiringExpr a

open Lean.Grind.CommRing in
/-- info: exprs=1087, mismatches=0 0 0 0 0 0 -/
#guard_msgs in
run_meta SymM.run do
  let es := leaves ++ grow leaves leaves
  let es := es ++ grow (grow leaves leaves).toArray[:20].toArray.toList leaves
  let check (cfg : PolyConfig) (e : RingExpr) (expected : Poly) : SymM Nat := do
    let some p ← (toPoly? e).run cfg | throwError "unexpected failure"
    return if p == expected then 0 else 1
  let mut bad := Array.replicate 6 0
  for e in es do
    bad := bad.modify 0 (· + (← check {} e e.toPoly))
    bad := bad.modify 1 (· + (← check { char? := some 7 } e (e.toPolyC 7)))
    bad := bad.modify 2 (· + (← check { commutative := false } e e.toPoly_nc))
    bad := bad.modify 3 (· + (← check { commutative := false, char? := some 7 } e (e.toPolyC_nc 7)))
    if isSemiringExpr e then
      bad := bad.modify 4 (· + (← check { semiring := true } e e.toPolyS))
      bad := bad.modify 5 (· + (← check { semiring := true, commutative := false } e e.toPolyS_nc))
  logInfo m!"exprs={es.length}, mismatches={bad[0]!} {bad[1]!} {bad[2]!} {bad[3]!} {bad[4]!} {bad[5]!}"
