import Lean
/-!
`lia` encodes `a % k` as `a` and `a / k` as `0`, for a numeral `k`, when the stored constraints
bound `a` to `0 ≤ a < k`. The bound can come from a chain of constraints. Without this bound,
`lia` uses the general encoding `a = k * (a / k) + a % k` with `0 ≤ a % k < k`
(`Int.Internal.Linear.ediv_emod`, `emod_nonneg` and `emod_le`).

This matters for `BitVec` goals. The `grind` homomorphism rules translate `(x + 1).toNat` to
`(x.toNat + 1) % 2^64`. If the context bounds `x`, the sum cannot wrap around, and the general
encoding adds a quotient variable with the coefficient `2^64` that `lia` must then eliminate.
-/

set_option linter.unusedVariables false

open Lean in
/--
The number of distinct applications of `c` in the proof of `thm`, including the auxiliary
lemmas `thm._proof_*` that the proof refers to.
-/
partial def countIn (thm c : Name) : CoreM Nat := do
  let env ← getEnv
  let rec go (e : Expr) : StateM (Std.HashSet Expr) Unit := do
    if (← get).contains e then return
    modify (·.insert e)
    match e with
    | .const n _ =>
      if thm.isPrefixOf n && n != thm then
        if let some (.thmInfo info) := env.find? n then go info.value
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  let some (.thmInfo info) := env.find? thm | throwError "unknown theorem {thm}"
  let ((), s) := (go info.value).run {}
  return s.fold (fun n e => if e.isAppOf c then n + 1 else n) 0

/-! The bound of `x` follows from `0 ≤ x < y ≤ 10`. -/

/--
trace: [grind.lia.assert.boundedDivMod] x % 16
-/
#guard_msgs in
set_option trace.grind.lia.assert.boundedDivMod true in
example (x y : Int) (h₁ : 0 ≤ x) (h₂ : x < y) (h₃ : y ≤ 10) : x % 16 = x := by
  lia

/--
trace: [grind.lia.assert.boundedDivMod] x / 16
-/
#guard_msgs in
set_option trace.grind.lia.assert.boundedDivMod true in
example (x y : Int) (h₁ : 0 ≤ x) (h₂ : x < y) (h₃ : y ≤ 10) : x / 16 = 0 := by
  lia

-- `x` can be `16`, so `lia` uses the general encoding of `x % 16`.
#guard_msgs in
set_option trace.grind.lia.assert.boundedDivMod true in
example (x : Int) (h₁ : x ≤ 16) (h₂ : x % 16 = x) : x < 16 := by
  lia

-- The disequality refines `x ≤ 16` to `x ≤ 15`.
/--
trace: [grind.lia.assert.boundedDivMod] x % 16
-/
#guard_msgs in
set_option trace.grind.lia.assert.boundedDivMod true in
example (x : Int) (h₁ : 0 ≤ x) (h₂ : x ≤ 16) (h₃ : x ≠ 16) : x % 16 = x := by
  lia

/-!
One step of a loop `i += 128` that runs while `i < c`, where `c ≤ n < 2^32`. The sum `i + 128`
cannot wrap around, so `(i.toNat + 128) % 2^64` gets the bounded encoding. The alignment
`i.toNat % 128` keeps the general encoding.
-/

/--
trace: [grind.lia.assert.boundedDivMod] (↑i.toNat + 128) % 18446744073709551616
-/
#guard_msgs in
set_option trace.grind.lia.assert.boundedDivMod true in
example (i c n : BitVec 64) (hn : n.toNat < 2^32) (hc : c.toNat ≤ n.toNat)
    (hi : i.toNat < c.toNat) (ha : i.toNat % 128 = 0) (hca : c.toNat % 128 = 0) :
    (i + 128).toNat ≤ c.toNat ∧ (i + 128).toNat % 128 = 0 := by
  grind

/-!
Eight counters below a common bound `n < 2^32`. None of the eight sums `xᵢ + 1` can wrap around,
so the proof has no instance of the general encoding. With the general encoding, the proof has
17 instances of `Int.Internal.Linear.ediv_emod`.
-/

theorem counters (n x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : BitVec 64) (hn : n.toNat < 2^32)
    (h₀ : x₀.toNat < n.toNat) (h₁ : x₁.toNat < n.toNat) (h₂ : x₂.toNat < n.toNat)
    (h₃ : x₃.toNat < n.toNat) (h₄ : x₄.toNat < n.toNat) (h₅ : x₅.toNat < n.toNat)
    (h₆ : x₆.toNat < n.toNat) (h₇ : x₇.toNat < n.toNat) :
    (x₀ + 1).toNat + (x₁ + 1).toNat + (x₂ + 1).toNat + (x₃ + 1).toNat +
      (x₄ + 1).toNat + (x₅ + 1).toNat + (x₆ + 1).toNat + (x₇ + 1).toNat =
    x₀.toNat + x₁.toNat + x₂.toNat + x₃.toNat + x₄.toNat + x₅.toNat + x₆.toNat + x₇.toNat + 8 := by
  grind

/-- info: 0 -/
#guard_msgs in
#eval countIn ``counters ``Int.Internal.Linear.ediv_emod
