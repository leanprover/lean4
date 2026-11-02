import Lean
import Std.Tactic.BVDecide

/-!
Tests `Std.Tactic.BVDecide.KernelVM.bvVMProg` against `BVLogicalExpr.eval`: random expressions are
bitblasted by the kernel VM (mode `1`), and the resulting AIG, read from the memory, is evaluated
under random assignments.
-/

open Lean Std.Tactic.BVDecide Std.Tactic.BVDecide.KernelVM Lean.KernelVM

deriving instance Inhabited for BVBinOp, BVUnOp, Gate

structure Rng where
  s : UInt64

def Rng.next (g : Rng) (n : Nat) : Nat × Rng :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % n, ⟨s⟩)

abbrev GenM := StateM Rng

def pick (n : Nat) : GenM Nat := modifyGet fun g => g.next n

def widths : Array Nat := #[0, 1, 2, 3, 5, 8, 13]

/-- Atom `idx` has width `idx / 4`. -/
def atomOf (w : Nat) : GenM Nat := return 4 * w + (← pick 4)

def genBV : (w : Nat) → Nat → GenM (BVExpr w)
  | w, 0 => do
    match ← pick 2 with
    | 0 => return .var (← atomOf w)
    | _ => return .const (BitVec.ofNat w (← pick 100000))
  | w, d + 1 => do
    match ← pick 14 with
    | 0 => return .var (← atomOf w)
    | 1 => return .const (BitVec.ofNat w (← pick 100000))
    | 2 => do
      let w' := widths[← pick widths.size]!
      return .extract (← pick (w' + 2)) w (← genBV w' d)
    | 3 | 4 =>
      let op := #[BVBinOp.and, .or, .xor, .add, .mul, .udiv, .umod][← pick 7]!
      return .bin (← genBV w d) op (← genBV w d)
    | 5 | 6 =>
      let op := #[BVUnOp.not, .rotateLeft (← pick 20), .rotateRight (← pick 20),
        .arithShiftRightConst (← pick 20), .reverse, .clz, .cpop][← pick 7]!
      return .un op (← genBV w d)
    | 7 => do
      let l := (← pick 100) % (w + 1)
      have : l ≤ w := Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos w))
      return .append (← genBV l d) (← genBV (w - l) d) (by omega)
    | 8 => return .replicate w (← genBV 1 d) (Nat.one_mul w).symm
    | 9 => return .shiftLeft (← genBV w d) (← genBV (← pick 5) d)
    | 10 => return .shiftRight (← genBV w d) (← genBV (← pick 5) d)
    | 11 => return .arithShiftRight (← genBV w d) (← genBV (← pick 5) d)
    | _ => return .bin (← genBV w d) .add (← genBV w d)

def genBool : Nat → GenM BVLogicalExpr
  | 0 => do
    let w := widths[← pick widths.size]!
    match ← pick 3 with
    | 0 => return .literal (.bin (← genBV w 2) .eq (← genBV w 2))
    | 1 => return .literal (.bin (← genBV w 2) .ult (← genBV w 2))
    | _ => return .literal (.getLsbD (← genBV w 2) (← pick (w + 2)))
  | d + 1 => do
    match ← pick 5 with
    | 0 => return .not (← genBool d)
    | 1 => return .gate #[Gate.and, .xor, .beq, .or][← pick 4]! (← genBool d) (← genBool d)
    | 2 => return .ite (← genBool d) (← genBool d) (← genBool d)
    | 3 => return .const ((← pick 2) == 0)
    | _ => genBool 0

def genAssign : GenM BVExpr.Assignment := do
  let mut xs : Array BVExpr.PackedBitVec := #[⟨BitVec.ofNat 0 0⟩]
  for idx in 1...(4 * 14) do
    xs := xs.push ⟨BitVec.ofNat (idx / 4) (← pick 100000)⟩
  if h : 0 < xs.size then return Lean.RArray.ofArray xs h else return .leaf ⟨BitVec.ofNat 0 0⟩

def word (mem : ByteArray) (a : Nat) : Nat :=
  (List.range 8).foldl (init := 0) fun r b => r + (mem.get! (8 * a + b)).toNat <<< (8 * b)

/-- Evaluates the AIG in `mem` under `assign` and returns the value of the root. -/
def evalAIG (mem : ByteArray) (numNodes numAtoms : Nat) (assign : BVExpr.Assignment) : Bool := Id.run do
  let numAig := word mem 0
  let atomT := 8 + 2 * numNodes
  let B := atomT + 2 * numAtoms
  -- the value of each atom node
  let mut atomVal : Std.HashMap Nat Bool := {}
  for a in 0...numAtoms do
    let o := word mem (atomT + 2 * a)
    if o != 0 then
      let wd := word mem (atomT + 2 * a + 1)
      let bv := (assign.get a).bv
      for b in 0...wd do
        let lit := word mem (B + 4 * (o - 1 + b) + 2)
        atomVal := atomVal.insert (lit / 2) (bv.getLsbD b)
  let mut val : Array Bool := #[false]
  for n in 1...numAig do
    let l := word mem (B + 4 * n)
    if l == 18446744073709551615 then
      val := val.push (atomVal.getD n false)
    else
      let r := word mem (B + 4 * n + 1)
      let lv := val[l / 2]! != (l % 2 == 1)
      let rv := val[r / 2]! != (r % 2 == 1)
      val := val.push (lv && rv)
  let rootOff := word mem (8 + 2 * (numNodes - 1))
  let root := word mem (B + 4 * rootOff + 2)
  return val[root / 2]! != (root % 2 == 1)

def bitblastTest (n : Nat) : IO Unit := do
  let mut g : Rng := ⟨7⟩
  let mut gates := 0
  for _ in 0...n do
    let (e, g') := (genBool 3).run g
    g := g'
    let enc := encodeBVLogical e
    let numNodes := enc % 4294967296
    let numAtoms := (enc >>> 32) % 4294967296
    let some mem := runMem bvVMProg [.nat enc, .nat 0, .nat 1] 10000000000
      | throw <| IO.userError s!"bitblasting failed for {e}"
    gates := gates + word mem 1
    for _ in 0...5 do
      let (assign, g') := genAssign.run g
      g := g'
      if evalAIG mem numNodes numAtoms assign != e.eval assign then
        throw <| IO.userError s!"mismatch for {e}"
  IO.println s!"agreed on {n} expressions ({gates} clauses)"

/-- info: agreed on 500 expressions (103129 clauses) -/
#guard_msgs in
#eval bitblastTest 500
