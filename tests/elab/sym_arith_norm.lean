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

/-- Normalizes the body of `n` (atoms simplified by `simpAtom`), prints the result, and kernel-checks the proof. -/
def test (n : Name) (simpAtom : Expr → SymM Sym.Simp.Result := fun _ => return .rfl) : SymM Unit := do
  let e ← preprocessExpr (← getDefValue n)
  match (← normalize? e simpAtom) with
  | .rfl false _ => logInfo m!"{n}: not applicable"
  | .rfl true _ => logInfo m!"{n}: {e} (normal)"
  | .step e' h done _ =>
    addDecl <| .thmDecl { name := n ++ `norm, levelParams := [], type := ← mkEq e e', value := h }
    logInfo m!"{n}: {e'}{if done then "" else " (not done)"}"

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
info: s1: not applicable
---
info: s2: not applicable
-/
#guard_msgs in
run_meta SymM.run do
  for n in [``s1, ``s2] do
    test n

-- Budget.
def big : Int := (a + 1) ^ 100

/-- info: big: not applicable -/
#guard_msgs in
set_option sym.arith.maxDegree 8 in
run_meta SymM.run do
  test ``big

/-- info: big: not applicable -/
#guard_msgs in
set_option sym.arith.maxTerms 8 in
run_meta SymM.run do
  test ``big

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
/-- info: exprs=1087, mismatches=0 0 0 -/
#guard_msgs in
run_meta SymM.run do
  let es := leaves ++ grow leaves leaves
  let es := es ++ grow (grow leaves leaves).toArray[:20].toArray.toList leaves
  let mut bad₁ : Nat := 0
  let mut bad₂ : Nat := 0
  let mut bad₃ : Nat := 0
  for e in es do
    let some p ← (toPoly? e).run {} | throwError "unexpected failure"
    unless p == e.toPoly do bad₁ := bad₁ + 1
    let some p ← (toPoly? e).run { char? := some 7 } | throwError "unexpected failure"
    unless p == e.toPolyC 7 do bad₂ := bad₂ + 1
    if isSemiringExpr e then
      let some p ← (toPoly? e).run { semiring := true } | throwError "unexpected failure"
      unless p == e.toPolyS do bad₃ := bad₃ + 1
  logInfo m!"exprs={es.length}, mismatches={bad₁} {bad₂} {bad₃}"
