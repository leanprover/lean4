import Lean

/-!
Tests that the `[grind homo]` environment extension is populated by the homomorphism
rules in `Init.Grind.Homo`. We check both direct retrieval (`getHomoTheorems` +
`Theorems.getMatch`) and that the registered theorems can be used to perform
rewriting: a small metaprogram applies the homomorphisms to fixpoint using `Sym.simp`
and verifies the generated proofs.
-/

open Lean Meta Lean.Meta.Sym Lean.Meta.Sym.Simp

/-- Prints the `[grind homo]` rules matching the (instantiated) body of `declName`. -/
def showMatches (declName : Name) : MetaM Unit := do
  let value := (← getConstInfoDefn declName).value
  lambdaTelescope value fun _ body => SymM.run do
    let body ← share body
    let thms ← Grind.getHomoTheorems
    for thm in thms.getMatch body do
      logInfo m!"{thm.expr}"

/--
Applies the `[grind homo]` rules to the body of `declName` to fixpoint using `Sym.simp`,
prints the result, and checks the generated proof.
-/
def applyHomo (declName : Name) : MetaM Unit := do
  let value := (← getConstInfoDefn declName).value
  lambdaTelescope value fun _ body => SymM.run do
    let thms ← Grind.getHomoTheorems
    let methods : Methods := { pre := thms.rewrite, post := thms.rewrite }
    let body ← share body
    let r ← simp body methods {}
    let result := Result.getResultExpr body r
    logInfo m!"{body}\n==>\n{result}"
    if let .step _ proof _ _ := r then
      Meta.check proof
      unless (← isDefEq (← Meta.inferType proof) (← mkEq body result)) do
        throwError "proof type mismatch"

/-! Extension population: representative operations retrieve the expected rules. -/

def bvAdd (x y : BitVec 8) : Nat := (x + y).toNat
def u8Mul (x y : UInt8) : BitVec 8 := (x * y).toBitVec
def finSub (n : Nat) (a b : Fin n) : Nat := (a - b).val

/--
info: @BitVec.toNat_add
-/
#guard_msgs in
run_meta showMatches ``bvAdd

/--
info: UInt8.toBitVec_ofNat
---
info: @UInt8.toBitVec_mul
-/
#guard_msgs in
run_meta showMatches ``u8Mul

/--
info: @Fin.val_sub
-/
#guard_msgs in
run_meta showMatches ``finSub

/-! Rewriting with the registered homomorphisms. -/

/-- The worked example from the design: cleanup rules remove nested `% 2^8` wrappers. -/
def bvCleanup (x y z : BitVec 8) : Prop := (x + y + z).toNat = 0

def u8Eq (x y z : UInt8) : Prop := (x + y) * z = z

def u8ToNat (x y : UInt8) : Prop := (x + y).toNat = x.toNat

def finEq (n : Nat) (a b : Fin n) : Prop := a + b = b

def listLen (l₁ l₂ : List Nat) : Prop := (l₁ ++ l₂).length = l₁.length

def intCast (a b : Nat) : Prop := ((a + b * a : Nat) : Int) = 0

def i64Eq (a b : Int64) : Prop := a * b = b

/--
info: (x + y + z).toNat = 0
==>
(x.toNat + y.toNat + z.toNat) % 2 ^ 8 = 0
-/
#guard_msgs in
run_meta applyHomo ``bvCleanup

/--
info: (x + y) * z = z
==>
(x.toBitVec.toNat + y.toBitVec.toNat) * z.toBitVec.toNat % 2 ^ 8 = z.toBitVec.toNat
-/
#guard_msgs in
run_meta applyHomo ``u8Eq

/--
info: (x + y).toNat = x.toNat
==>
(x.toBitVec.toNat + y.toBitVec.toNat) % 2 ^ 8 = x.toBitVec.toNat
-/
#guard_msgs in
run_meta applyHomo ``u8ToNat

/--
info: a + b = b
==>
(↑a + ↑b) % n = ↑b
-/
#guard_msgs in
run_meta applyHomo ``finEq

/--
info: (l₁ ++ l₂).length = l₁.length
==>
l₁.length + l₂.length = l₁.length
-/
#guard_msgs in
run_meta applyHomo ``listLen

/--
info: ↑(a + b * a) = 0
==>
↑a + ↑b * ↑a = 0
-/
#guard_msgs in
run_meta applyHomo ``intCast

/--
info: a * b = b
==>
a.toBitVec.toNat * b.toBitVec.toNat % 2 ^ 64 = b.toBitVec.toNat
-/
#guard_msgs in
run_meta applyHomo ``i64Eq

/-! Homomorphism predicates from `Init.Grind.Homo`: range facts and relation
translations are instantiated for representative terms via `mkHomoPredInstances`. -/

/-- Instantiates the `[grind homo_pred]` theorems for the body of `declName`. -/
def showPredInstances (declName : Name) : MetaM Unit := do
  let value := (← getConstInfoDefn declName).value
  lambdaTelescope value fun _ body => do
    for (proof, prop) in ← Grind.mkHomoPredInstances body do
      Meta.check proof
      logInfo m!"{prop}"

def bvToNat (x y : BitVec 8) : Nat := (x + y).toNat
def bvToInt (x : BitVec 8) : Int := x.toInt
def u8Le (x y : UInt8) : Prop := x ≤ y
def finVal (n : Nat) (a : Fin n) : Nat := a.val
def i64Lt (a b : Int64) : Prop := a < b

/--
info: (x + y).toNat < 2 ^ 8
-/
#guard_msgs in
run_meta showPredInstances ``bvToNat

/--
info: 2 * x.toInt < 2 ^ 8
---
info: -2 ^ 8 ≤ 2 * x.toInt
-/
#guard_msgs in
run_meta showPredInstances ``bvToInt

/--
info: x ≤ y
==>
x.toBitVec.toNat ≤ y.toBitVec.toNat
-/
#guard_msgs in
run_meta applyHomo ``u8Le

/--
info: ↑a < n
-/
#guard_msgs in
run_meta showPredInstances ``finVal

/--
info: a < b
==>
a.toBitVec.toInt < b.toBitVec.toInt
-/
#guard_msgs in
run_meta applyHomo ``i64Lt

/-! Signed bitvector comparisons are translated into `Int`. -/

def bvSle (x y : BitVec 8) : Prop := x.sle y
def bvSlt (x y : BitVec 8) : Prop := x.slt y

/--
info: x.sle y = true
==>
x.toInt ≤ y.toInt
-/
#guard_msgs in
run_meta applyHomo ``bvSle

/--
info: x.slt y = true
==>
x.toInt < y.toInt
-/
#guard_msgs in
run_meta applyHomo ``bvSlt
