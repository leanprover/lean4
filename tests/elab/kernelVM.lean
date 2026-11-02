import Lean

/-!
Tests for `Lean.KernelVM.run` and the kernel's native evaluation of it, and of `Nat.getByte` and
`Nat.getUInt64`. The differential test checks that the kernel agrees with the compiled reference
semantics on random programs.
-/

open Lean Lean.KernelVM

/-! ## Native `Nat` reads -/

example : Nat.getByte 0x1234 0 = 0x34 := by decide +kernel
example : Nat.getByte 0x1234 1 = 0x12 := by decide +kernel
example : Nat.getByte 0x1234 2 = 0 := by decide +kernel
example : Nat.getUInt64 (2 ^ 200 + 5) 25 = 1 := by decide +kernel
example : Nat.getUInt64 (2 ^ 200 + 5) 0 = 5 := by decide +kernel
example : Nat.getUInt64 (2 ^ 200 - 1) 17 = 2 ^ 64 - 1 := by decide +kernel
example : Nat.getUInt64 (2 ^ 200 - 1) 22 = 2 ^ 24 - 1 := by decide +kernel
example : Nat.getUInt64 (2 ^ 200 - 1) (2 ^ 100) = 0 := by decide +kernel
example : Nat.getUInt64 (2 ^ 62 + 3) 3 = 2 ^ 38 := by decide +kernel

/-! ## Small programs -/

/-- Sums the bytes of input 0, whose length is input 1, and asserts the sum equals input 2. -/
def sumBytes : Prog where
  body :=
    .seq (.while (.bin .ult (.reg 0) (.input 1 (.const 0)))
      (.seq (.set 1 (.bin .add (.reg 1) (.bin .and (.input 0 (.reg 0)) (.const 255))))
        (.set 0 (.bin .add (.reg 0) (.const 1)))))
    (.assert (.bin .eq (.reg 1) (.input 2 (.const 0))))

example : run sumBytes [0x010203, 3, 6] 100 = true := by decide +kernel
example : run sumBytes [0x010203, 3, 7] 100 = false := by decide +kernel
-- The loop needs four levels of fuel for three iterations, plus the levels around it.
example : run sumBytes [0x010203, 3, 6] 3 = false := by decide +kernel

/-- Fills memory with `0..n-1` and sums it back up, for `n` = input 0. -/
def memSum : Prog where
  body :=
    .seq (.while (.bin .ult (.reg 0) (.input 0 (.const 0)))
      (.seq (.store (.reg 0) (.reg 0)) (.set 0 (.bin .add (.reg 0) (.const 1)))))
    (.seq (.set 0 (.const 0))
    (.seq (.while (.bin .ult (.reg 0) (.input 0 (.const 0)))
      (.seq (.set 1 (.bin .add (.reg 1) (.load (.reg 0)))) (.set 0 (.bin .add (.reg 0) (.const 1)))))
    (.assert (.bin .eq (.reg 1) (.input 1 (.const 0))))))

example : run memSum [100000, 4999950000] 1000000 = true := by decide +kernel

-- Signed arithmetic fails on overflow.
example : run ⟨.assert (.bin .sadd (.const (2 ^ 63 - 1)) (.const 1))⟩ [] 10 = false := by decide +kernel
example : run ⟨.assert (.bin .smul (.const (2 ^ 62)) (.const (2 ^ 64 - 2)))⟩ [] 10 = true := by
  decide +kernel
example : run ⟨.assert (.bin .eq (.bin .sdiv (.const (2 ^ 64 - 7)) (.const 2)) (.const (2 ^ 64 - 4)))⟩
    [] 10 = true := by decide +kernel
example : run ⟨.assert (.bin .eq (.bin .smod (.const (2 ^ 64 - 7)) (.const (2 ^ 64 - 2))) (.const 1))⟩
    [] 10 = true := by decide +kernel

/-! ## Differential test against the compiled reference semantics -/

deriving instance Inhabited for BinOp, Exp, Stmt
deriving instance ToExpr for BinOp
deriving instance ToExpr for Exp
deriving instance ToExpr for Stmt
deriving instance ToExpr for Prog

/-- A tiny linear congruential generator. -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) (n : Nat) : Nat × Rng :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % n, ⟨s⟩)

abbrev GenM := StateM Rng

def pick (n : Nat) : GenM Nat := modifyGet fun g => g.next n

def interesting : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 63, 64, 255, 2 ^ 31, 2 ^ 32, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1,
    2 ^ 64 - 2, 2 ^ 64 - 7, 2 ^ 64, 2 ^ 65 + 5]

def ops : Array BinOp :=
  #[.add, .sub, .mul, .udiv, .umod, .and, .or, .xor, .shl, .shr, .eq, .ult, .ule, .slt, .sle,
    .sadd, .ssub, .smul, .sdiv, .smod]

def genExp : Nat → GenM Exp
  | 0 => do
    match ← pick 3 with
    | 0 => return .const interesting[← pick interesting.size]!
    | 1 => return .const (← pick 20)
    | _ => return .reg (← pick 4)
  | d + 1 => do
    match ← pick 6 with
    | 0 => return .const interesting[← pick interesting.size]!
    | 1 => return .reg (← pick 4)
    | 2 => return .load (← genExp d)
    | 3 => return .input (← pick 3) (← genExp d)
    | _ => return .bin ops[← pick ops.size]! (← genExp d) (← genExp d)

def genStmt : Nat → GenM Stmt
  | 0 => do
    match ← pick 3 with
    | 0 => return .set (← pick 4) (← genExp 2)
    | 1 => return .store (.bin .and (← genExp 2) (.const 15)) (← genExp 2)
    | _ => return .skip
  | d + 1 => do
    match ← pick 7 with
    | 0 => return .set (← pick 4) (← genExp 3)
    | 1 => return .store (.bin .and (← genExp 2) (.const 15)) (← genExp 2)
    | 2 => return .seq (← genStmt d) (← genStmt d)
    | 3 => return .ite (← genExp 2) (← genStmt d) (← genStmt d)
    | 4 => return .assert (.bin .ule (← genExp 2) (← genExp 2))
    | 5 =>
      -- A counting loop on register 3, which may or may not terminate within the fuel.
      let n ← pick 6
      return .while (.bin .ult (.reg 3) (.const n))
        (.seq (← genStmt d) (.set 3 (.bin .add (.reg 3) (.const 1))))
    | _ => return .seq (← genStmt d) (← genStmt d)

def genInput : GenM Nat := do
  match ← pick 3 with
  | 0 => return interesting[← pick interesting.size]!
  | 1 => return 2 ^ (← pick 300) * (← pick 1000) + (← pick 1000)
  | _ => return (← pick 100000)

/-- Compares the compiled reference semantics with the kernel on `n` random programs. -/
def diffTest (n : Nat) : MetaM Unit := do
  let mut g : Rng := ⟨2026⟩
  let mut results : Array Nat := #[0, 0]
  for _ in 0...n do
    let ((p, ins, fuel), g') := (do
      let p : Prog := ⟨← genStmt 4⟩
      let ins ← (List.range 3).mapM fun _ => genInput
      let fuel ← pick 40
      return (p, ins, fuel)).run g
    g := g'
    let expected := run p ins fuel
    let e := mkApp3 (mkConst ``run) (toExpr p) (toExpr ins) (toExpr fuel)
    match Kernel.whnf (← getEnv) {} e with
    | .ok r =>
      let actual := r == mkConst ``Bool.true
      unless r == mkConst ``Bool.true || r == mkConst ``Bool.false do
        throwError "kernel did not evaluate {p.body.ctorIdx}"
      if actual != expected then
        throwError "mismatch on {repr ins} {fuel}: reference {expected}, kernel {actual}\n{toExpr p}"
      results := results.modify (if actual then 1 else 0) (· + 1)
    | .error ex => throwError "kernel error: {← ex.toMessageData {} |>.toString}"
  logInfo m!"agreed on {n} programs: {results[1]!} succeeded, {results[0]!} failed"

/-- info: agreed on 3000 programs: 2385 succeeded, 615 failed -/
#guard_msgs in
#eval diffTest 3000
