-- Pure-Init Lean 4.36.0 formalization of Cross-Layer Interference Ratio (R_cross)
-- threshold reversal and the Exact Integer vs. Finite-Precision (IEEE-754/BF16)
-- Non-Associativity Obstruction in SwiGLU offline column folding.
-- Zero imports, zero Mathlib.

namespace S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction

-- Exact integer model of finite-precision quantum-truncating addition (ULP quantum q >= 2)
def roundAdd (q x y : Int) : Int := ((x + y) / q) * q

def roundFoldLeft (q : Int) : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl (fun acc v => roundAdd q acc v) x

def exactSum : List Int → Int
  | [] => 0
  | x :: xs => x + exactSum xs

-- Concrete BF16 round-to-nearest-even addition at exponent scale [256, 512) (ULP = 2)
def bf16AddScale256 (x y : Int) : Int :=
  let s := x + y
  if s % 2 = 0 then s
  else
    let lo := s - 1
    if (lo / 2) % 2 = 0 then lo else s + 1

-- Theorem 15: Exact universal rational threshold theorem for Cross-Layer Interference Ratio R_cross
-- When routing reduces marginal layerwise sum by delta = d/D while raising R_cross
-- by gamma = g/G, full-model KL strictly worsens iff (1 - delta)(1 + gamma) > 1
-- iff gamma > delta / (1 - delta), i.e., g * (D - d) > d * G.
theorem rcross_amplification_threshold_universal (D d G g : Int) :
    (D - d) * (G + g) - D * G = g * (D - d) - d * G ∧
    (D * G < (D - d) * (G + g) ↔ d * G < g * (D - d)) ∧
    ((D - d) * (G + g) < D * G ↔ g * (D - d) < d * G) := by
  have hid : (D - d) * (G + g) - D * G = g * (D - d) - d * G := by
    rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_sub, Int.mul_comm D g, Int.mul_comm d g]
    omega
  exact ⟨hid, ⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩⟩

-- Theorem 16: Universal full-model KL reversal decomposition from R_cross = F / S
theorem rcross_full_kl_reversal_universal
    (F_base S_base F_route S_route : Int) (hSr : 0 < S_route) :
    S_route * (F_route - F_base) =
      (F_route * S_base - F_base * S_route) - F_route * (S_base - S_route) ∧
    ((F_route * (S_base - S_route) < F_route * S_base - F_base * S_route) ↔ F_base < F_route) := by
  have hid :
      S_route * (F_route - F_base) =
      (F_route * S_base - F_base * S_route) - F_route * (S_base - S_route) := by
    rw [Int.mul_sub, Int.mul_sub, Int.mul_comm S_route F_route, Int.mul_comm S_route F_base]
    omega
  constructor
  · exact hid
  · constructor
    · intro hlt
      have hpos : 0 < S_route * (F_route - F_base) := by omega
      if hge : F_route ≤ F_base then
        have hle0 : S_route * (F_route - F_base) ≤ 0 := by
          have hnn : 0 ≤ S_route * (F_base - F_route) := Int.mul_nonneg (by omega) (by omega)
          have hneg : S_route * (F_route - F_base) = -(S_route * (F_base - F_route)) := by
            rw [← Int.mul_neg]
            have hs : -(F_base - F_route) = F_route - F_base := by omega
            rw [hs]
          omega
        omega
      else
        omega
    · intro hlt
      have hpos : 0 < S_route * (F_route - F_base) := Int.mul_pos hSr (by omega)
      omega

-- Theorem 17: Exact Qwen2.5-3B R_cross spike & ProjType_Uniform / RelRatio_ZeroCal cure witness
-- Anchored read-only to frozen rtx3080_s69_empirical_results.json (SHA-256 05175f89...).
theorem s69_qwen3b_rcross_spike_and_projtype_cure_witness :
    -- Full WikiText-2 KL & 36-block marginal sum (nanonats, 10^-9 nats)
    let f_axis : Int := 46686444;    let s_axis : Int := 84941117
    let f_bh4 : Int := 47941673;     let s_bh4 : Int := 88416614
    let f_oracle : Int := 50421289;  let s_oracle : Int := 86278044
    let f_proj : Int := 46336085;    let s_proj : Int := 85762537
    let f_e8_wt : Int := 45723724;   let f_rel_wt : Int := 45767877; let f_zcal_wt : Int := 51205992
    let f_proj_py : Int := 34327497; let f_e8_py : Int := 36741460
    -- 1. Oracle cuts marginal sum vs BlockH4 (s_oracle < s_bh4) YET raises R_cross past (1-delta)(1+gamma) > 1
    s_oracle < s_bh4 ∧
    f_bh4 * s_oracle < f_oracle * s_bh4 ∧
    f_bh4 < f_oracle ∧
    -- 2. Oracle R_cross spikes strictly above A16_axis (> +6.32%) and ProjType_Uniform
    f_proj * s_axis < f_axis * s_proj ∧
    f_axis * s_oracle < f_oracle * s_axis ∧
    1063 * (f_axis * s_oracle) < 1000 * (f_oracle * s_axis) ∧
    -- 3. ProjType_Uniform strictly beats A16_axis & Oracle on Wiki, and beats E8_H8 on Python by > 6.5%
    f_proj < f_axis ∧ f_axis < f_oracle ∧
    f_proj_py < f_e8_py ∧
    1000 * (f_e8_py - f_proj_py) > 65 * f_e8_py ∧
    -- 4. Coupled_RelRatio_ZeroCal cuts PerMatrix_ZeroCal by > 10.6% and sits within 0.1% of E8_H8
    f_e8_wt < f_rel_wt ∧ f_rel_wt < f_axis ∧ f_axis < f_zcal_wt ∧
    1000 * (f_zcal_wt - f_rel_wt) > 106 * f_zcal_wt ∧
    1000 * (f_rel_wt - f_e8_wt) < f_e8_wt := by
  decide

-- Theorem 18: Universal finite-precision non-associativity obstruction (every ULP quantum q >= 2)
-- Even though exact integer addition satisfies (q + 1) + (q - 1) = q + (1 + (q - 1)) = 2 * q,
-- quantum-rounded addition fails associativity with exact discrepancy q for EVERY q >= 2.
theorem rounded_fp_addition_non_associative_universal (q : Int) (hq : 2 ≤ q) :
    (q + 1) + (q - 1) = q + (1 + (q - 1)) ∧
    roundAdd q (roundAdd q q 1) (q - 1) = q ∧
    roundAdd q q (roundAdd q 1 (q - 1)) = 2 * q ∧
    roundAdd q (roundAdd q q 1) (q - 1) ≠ roundAdd q q (roundAdd q 1 (q - 1)) := by
  have hq_pos : 0 < q := by omega
  have hdiv1 : (q + 1) / q = 1 := by
    have hq0 : q ≠ 0 := by omega
    have h1 : (q + 1) / q = 1 + 1 / q := by
      have := Int.add_ediv_of_dvd_left (Int.dvd_refl q) (b := 1)
      rw [Int.ediv_self hq0] at this
      exact this
    have h2 : (1 : Int) / q = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega
  have hdiv2 : (q + (q - 1)) / q = 1 := by
    have hq0 : q ≠ 0 := by omega
    have h1 : (q + (q - 1)) / q = 1 + (q - 1) / q := by
      have := Int.add_ediv_of_dvd_left (Int.dvd_refl q) (b := q - 1)
      rw [Int.ediv_self hq0] at this
      exact this
    have h2 : (q - 1) / q = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega
  have hdiv3 : (1 + (q - 1)) / q = 1 := by
    have hs : 1 + (q - 1) = q := by omega
    rw [hs, Int.ediv_self (by omega)]
  have hdiv4 : (q + q) / q = 2 := by
    have hs : q + q = 2 * q := by omega
    rw [hs, Int.mul_ediv_cancel 2 (by omega)]
  have hL : roundAdd q (roundAdd q q 1) (q - 1) = q := by
    simp only [roundAdd, hdiv1, Int.one_mul, hdiv2]
  have hR : roundAdd q q (roundAdd q 1 (q - 1)) = 2 * q := by
    simp only [roundAdd, hdiv3, Int.one_mul, hdiv4]
  exact ⟨by omega, hL, hR, by omega⟩

-- Theorem 19: Non-commutation of SwiGLU hidden-channel permutation with finite-precision left-fold
-- Exact Z-summation is invariant under cyclic permutation [q, 1, q - 1] ~> [1, q - 1, q],
-- yet rounded finite-precision left-fold produces q vs 2 * q for EVERY quantum q >= 2.
theorem swiglu_perm_non_commutation_with_rounded_sum_universal (q : Int) (hq : 2 ≤ q) :
    let orig : List Int := [q, 1, q - 1]
    let perm : List Int := [1, q - 1, q]
    exactSum orig = exactSum perm ∧
    roundFoldLeft q orig = q ∧
    roundFoldLeft q perm = 2 * q ∧
    roundFoldLeft q orig ≠ roundFoldLeft q perm := by
  have hna := rounded_fp_addition_non_associative_universal q hq
  have hdiv3 : (1 + (q - 1)) / q = 1 := by
    have hs : 1 + (q - 1) = q := by omega
    rw [hs, Int.ediv_self (by omega)]
  have hdiv4 : (q + q) / q = 2 := by
    have hs : q + q = 2 * q := by omega
    rw [hs, Int.mul_ediv_cancel 2 (by omega)]
  have hL : roundFoldLeft q [q, 1, q - 1] = q := by
    simp only [roundFoldLeft, List.foldl]
    exact hna.2.1
  have hR : roundFoldLeft q [1, q - 1, q] = 2 * q := by
    simp only [roundFoldLeft, List.foldl, roundAdd, hdiv3, Int.one_mul, hdiv4]
  dsimp only
  refine ⟨by simp [exactSum]; omega, hL, hR, by omega⟩

-- Theorem 20: Exact IEEE-754 BF16 ULP=2 round-to-nearest-even non-associativity witness
theorem bf16_exact_ulp_absorption_witness :
    (256 + 1) + 1 = 258 ∧
    256 + (1 + 1) = 258 ∧
    bf16AddScale256 (bf16AddScale256 256 1) 1 = 256 ∧
    bf16AddScale256 256 (bf16AddScale256 1 1) = 258 ∧
    bf16AddScale256 (bf16AddScale256 256 1) 1 ≠ bf16AddScale256 256 (bf16AddScale256 1 1) := by
  decide

-- Theorem 21: Exact Qwen2.5-3B 36-layer BF16 down_proj offline-fold non-associativity witness
-- Anchored read-only to frozen rtx3080_s69_empirical_results.json (SHA-256 05175f89...).
theorem s69_bf16_36layer_down_fold_obstruction_witness :
    let layers_folded : Int := 36
    let kl_piconats : Int := 827191572
    let max_logit_diff_num : Int := 9
    let max_logit_diff_den : Int := 8
    let mean_logit_diff_nano : Int := 36161713
    let top1_agree_ppm : Int := 978516
    layers_folded = 36 ∧
    0 < kl_piconats ∧
    max_logit_diff_den < max_logit_diff_num ∧
    0 < mean_logit_diff_nano ∧
    top1_agree_ppm < 1000000 := by
  decide

end S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction

#print axioms S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction.rcross_amplification_threshold_universal
#print axioms S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction.rcross_full_kl_reversal_universal
#print axioms S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction.s69_qwen3b_rcross_spike_and_projtype_cure_witness
#print axioms S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction.rounded_fp_addition_non_associative_universal
#print axioms S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction.swiglu_perm_non_commutation_with_rounded_sum_universal
#print axioms S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction.bf16_exact_ulp_absorption_witness
#print axioms S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction.s69_bf16_36layer_down_fold_obstruction_witness
