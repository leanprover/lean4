import Lean

open Lean Elab Tactic

-- Without any of these: fast
run_meta do logInfo m!"indicator fvar ID: {(← Lean.mkFreshFVarId).name}" -- still fast
run_meta do logInfo m!"indicator fvar ID: {(← Lean.mkFreshFVarId).name}" -- still fast
run_meta do logInfo m!"indicator fvar ID: {(← Lean.mkFreshFVarId).name}" -- slow
-- run_meta do logInfo m!"indicator fvar ID: {(← Lean.mkFreshFVarId).name}" -- fast again
-- run_meta do logInfo m!"indicator fvar ID: {(← Lean.mkFreshFVarId).name}" -- still fast
-- run_meta do logInfo m!"indicator fvar ID: {(← Lean.mkFreshFVarId).name}" -- slow again

-- #check Lean.Elab.Tactic.getFVarId
-- elab "showFVarId" id:ident : tactic => do
--   -- Resolve the identifier `id` to its FVarId
--   let fvarId ← getFVarId id

--   -- FVarId has a `.name` field which is its unique internal name.
--   -- We can log it to the infoview.
--   logInfo m!"The identifier '{id}' corresponds to the FVarId: {fvarId.name}"

-- set_option trace.profiler true
-- set_option trace.omegaImpl true
-- set_option trace.contradictionHandling true
-- set_option trace.splitting true
-- set_option trace.preparation true
-- set_option trace.proof true
-- set_option trace.proveFalse true
-- set_option trace.proveAssumption true
-- set_option trace.linearComboPrf true

-- set_option trace.Meta.instantiateMVars true
--set_option trace.Meta.isDefEq true
-- set_option trace.Meta.synthInstance true

--set_option trace.omega true

set_option maxHeartbeats 0
theorem memcpy_extracted_2 (six0 s0x0 : BitVec 64)
(h_six0_nonzero : six0 ≠ 0)
(h_s0x1 : s0x1 + 16#64 * (s0x0 - six0) + 16#64 = s0x1 + 16#64 * (s0x0 - (six0 - 1#64)))
(h_s0x2 : s0x2 + 16#64 * (s0x0 - six0) + 16#64 = s0x2 + 16#64 * (s0x0 - (six0 - 1#64)))
(h_assert_1 : six0 ≤ s0x0)
(_h_assert_3 : six1 = s0x1 + 16#64 * (s0x0 - six0))
(h_assert_4 : six2 = s0x2 + 16#64 * (s0x0 - six0))
(n : Nat)
(addr : BitVec 64)
(h_le : (s0x0 - (six0 - 1#64)).toNat ≤ s0x0.toNat)
(h_upper_bound : addr.toNat + n ≤ 2 ^ 64)
(h_upper_bound₂ : s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(h_upper_bound₃ : s0x2.toNat + (16#64 * (s0x0 - (six0 - 1#64))).toNat ≤ 2 ^ 64)
(h_width_lt : (16#64).toNat * (s0x0 - (six0 - 1#64)).toNat < 2 ^ 64)
(_hmemSeparate_omega : s0x1.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 ∧
  s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64 ∧
    (s0x1.toNat + s0x0.toNat * 16 ≤ s0x2.toNat ∨ s0x1.toNat ≥ s0x2.toNat + s0x0.toNat * 16))
(_hmemLegal_omega : s0x1.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(_hmemLegal_omega : s0x2.toNat + s0x0.toNat * 16 ≤ 2 ^ 64)
(_hmemSeparate_omega : s0x2.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - (2 ^ 64 - 1 % 2 ^ 64 + six0.toNat) % 2 ^ 64 + s0x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤
    2 ^ 64 ∧
  addr.toNat + n ≤ 2 ^ 64 ∧
    (s0x2.toNat +
          16 % 2 ^ 64 * ((2 ^ 64 - (2 ^ 64 - 1 % 2 ^ 64 + six0.toNat) % 2 ^ 64 + s0x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤
        addr.toNat ∨
      s0x2.toNat ≥ addr.toNat + n))
(hmemLegal_omega : s0x2.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - (2 ^ 64 - 1 % 2 ^ 64 + six0.toNat) % 2 ^ 64 + s0x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤
  2 ^ 64)
(hmemLegal_omega : addr.toNat + n ≤ 2 ^ 64) :
 s0x2.toNat + (16#64 * (s0x0 - six0)).toNat ≤ 2 ^ 64 ∧
  addr.toNat + n ≤ 2 ^ 64 ∧
    (s0x2.toNat + (16#64 * (s0x0 - six0)).toNat ≤ addr.toNat ∨ s0x2.toNat ≥ addr.toNat + n) := by
    bv_omega
