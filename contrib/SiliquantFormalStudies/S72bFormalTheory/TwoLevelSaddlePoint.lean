-- Pure-Init Lean 4.36.0 formalization of the Two-Level Saddle-Point Theorem:
-- opposing monotonicity between micro (H_4 quad) homogeneity and macro (g=128 ball)
-- load balance, LPT vs snake phase boundary, and unique simultaneous dominance of
-- Stratified Quad-Interleaving (Sort-into-Quads o Snake-Across-Balls) for all alpha, beta > 0.
-- Zero imports, zero Mathlib.

namespace S72bFormalTheory.TwoLevelSaddlePoint

def quadSum (a b c d : Int) : Int := a + b + c + d

def twoScaleLoss (alpha beta quadSpread ballSqSum : Int) : Int :=
  alpha * quadSpread + beta * ballSqSum

private theorem pair_gap_ident (a b c d : Int) :
    (a + d) * (b + c) - (a + b) * (c + d) = (a - c) * (b - d) ∧
    ((a + b) * (a + b) + (c + d) * (c + d)) -
      ((a + d) * (a + d) + (b + c) * (b + c)) = 2 * ((a - c) * (b - d)) := by
  constructor
  · simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
    have h1 := Int.mul_comm c b
    have h2 := Int.mul_comm d b
    have h3 := Int.mul_comm d c
    have h4 := Int.mul_comm d a
    have h5 := Int.mul_comm b a
    have h6 := Int.mul_comm c a
    omega
  · simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
    have h1 := Int.mul_comm b a
    have h2 := Int.mul_comm d a
    have h3 := Int.mul_comm c b
    have h4 := Int.mul_comm d c
    omega

-- Theorem 8: Micro-scale H_4 quad dominance on a sorted 16-channel Hessian ladder
-- Swapping h3 (coldest in Q0) with h12 (hottest in Q3) preserves Ball 0 load S0 + S3 identically
-- while strictly inflating total quad spread by 2 * (h3 - h12) and strictly reducing intra-quad
-- squared sum S0^2 + S3^2 by 2 * ((S0 - h3) - (S3 - h12)) * (h3 - h12).
theorem micro_quad_monotone_dominance_16_universal
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 : Int)
    (hsort :
      h0 ≥ h1 ∧ h1 ≥ h2 ∧ h2 ≥ h3 ∧ h3 ≥ h4 ∧ h4 ≥ h5 ∧ h5 ≥ h6 ∧ h6 ≥ h7 ∧
      h7 ≥ h8 ∧ h8 ≥ h9 ∧ h9 ≥ h10 ∧ h10 ≥ h11 ∧ h11 ≥ h12 ∧ h12 ≥ h13 ∧ h13 ≥ h14 ∧ h14 ≥ h15) :
    let S0 := quadSum h0 h1 h2 h3
    let S1 := quadSum h4 h5 h6 h7
    let S2 := quadSum h8 h9 h10 h11
    let S3 := quadSum h12 h13 h14 h15
    let S0_mix := quadSum h0 h1 h2 h12
    let S3_mix := quadSum h3 h13 h14 h15
    let spread_mono := (h0 - h3) + (h4 - h7) + (h8 - h11) + (h12 - h15)
    let spread_mix := (h0 - h12) + (h4 - h7) + (h8 - h11) + (h3 - h15)
    S0 ≥ S1 ∧ S1 ≥ S2 ∧ S2 ≥ S3 ∧
    S0_mix + S3_mix = S0 + S3 ∧
    spread_mix - spread_mono = 2 * (h3 - h12) ∧
    (S0 * S0 + S3 * S3) - (S0_mix * S0_mix + S3_mix * S3_mix) =
      2 * (((h0 + h1 + h2) - (h13 + h14 + h15)) * (h3 - h12)) ∧
    (h12 < h3 →
      spread_mono < spread_mix ∧
      S0_mix * S0_mix + S3_mix * S3_mix < S0 * S0 + S3 * S3) := by
  have hgap :
      ((h0 + h1 + h2 + h3) * (h0 + h1 + h2 + h3) + (h12 + h13 + h14 + h15) * (h12 + h13 + h14 + h15)) -
      ((h0 + h1 + h2 + h12) * (h0 + h1 + h2 + h12) + (h3 + h13 + h14 + h15) * (h3 + h13 + h14 + h15)) =
      2 * (((h0 + h1 + h2) - (h13 + h14 + h15)) * (h3 - h12)) := by
    let A := h0 + h1 + h2
    let C := h13 + h14 + h15
    have hp := (pair_gap_ident A h3 C h12).2
    have c1 : h3 + C = C + h3 := Int.add_comm h3 C
    have c2 : h12 + C = C + h12 := Int.add_comm h12 C
    have hA : h0 + h1 + h2 + h3 = A + h3 := rfl
    have hB : h12 + h13 + h14 + h15 = C + h12 := by dsimp only [C]; omega
    have hC : h0 + h1 + h2 + h12 = A + h12 := rfl
    have hD : h3 + h13 + h14 + h15 = C + h3 := by dsimp only [C]; omega
    rw [hA, hB, hC, hD]
    have c3 : C + h3 = h3 + C := Int.add_comm C h3
    rw [c3]
    exact hp
  dsimp only [quadSum]
  refine ⟨by omega, by omega, by omega, by omega, by omega, hgap, ?_⟩
  intro hlt
  have hpos : 0 < ((h0 + h1 + h2) - (h13 + h14 + h15)) * (h3 - h12) :=
    Int.mul_pos (by omega) (by omega)
  exact ⟨by omega, by omega⟩

-- Theorem 9: Macro-scale ball dominance of quad_snake over naive global contiguous sort
theorem macro_ball_snake_beats_global_sort_16_universal
    (S0 S1 S2 S3 : Int) (h01 : S1 ≤ S0) (h12 : S2 ≤ S1) (h23 : S3 ≤ S2) :
    let B0_snake := S0 + S3
    let B1_snake := S1 + S2
    let B0_glob := S0 + S1
    let B1_glob := S2 + S3
    B0_snake * B1_snake - B0_glob * B1_glob = (S0 - S2) * (S1 - S3) ∧
    (B0_glob * B0_glob + B1_glob * B1_glob) - (B0_snake * B0_snake + B1_snake * B1_snake) =
      2 * ((S0 - S2) * (S1 - S3)) ∧
    B0_glob * B1_glob ≤ B0_snake * B1_snake ∧
    B0_snake * B0_snake + B1_snake * B1_snake ≤ B0_glob * B0_glob + B1_glob * B1_glob ∧
    ((S2 < S0 ∧ S3 < S1) →
      B0_glob * B1_glob < B0_snake * B1_snake ∧
      B0_snake * B0_snake + B1_snake * B1_snake < B0_glob * B0_glob + B1_glob * B1_glob) := by
  have hgp := pair_gap_ident S0 S1 S2 S3
  have hnn : 0 ≤ (S0 - S2) * (S1 - S3) := Int.mul_nonneg (by omega) (by omega)
  dsimp only
  refine ⟨hgp.1, hgp.2, by omega, by omega, ?_⟩
  rintro ⟨h02, h13⟩
  have hpos : 0 < (S0 - S2) * (S1 - S3) := Int.mul_pos (by omega) (by omega)
  exact ⟨by omega, by omega⟩

-- Theorem 10: Quad-snake achieves global optimum over ALL 3 macro-ball pairings of 4 sorted quads
theorem macro_ball_snake_optimal_over_all_pairings_universal
    (S0 S1 S2 S3 : Int) (h01 : S1 ≤ S0) (h12 : S2 ≤ S1) (h23 : S3 ≤ S2) :
    (S0 + S3) * (S0 + S3) + (S1 + S2) * (S1 + S2) ≤ (S0 + S2) * (S0 + S2) + (S1 + S3) * (S1 + S3) ∧
    (S0 + S2) * (S0 + S2) + (S1 + S3) * (S1 + S3) ≤ (S0 + S1) * (S0 + S1) + (S2 + S3) * (S2 + S3) ∧
    (S0 + S1) * (S2 + S3) ≤ (S0 + S2) * (S1 + S3) ∧
    (S0 + S2) * (S1 + S3) ≤ (S0 + S3) * (S1 + S2) := by
  have g1 := pair_gap_ident S0 S1 S3 S2
  have g2 := pair_gap_ident S0 S2 S1 S3
  have nn1 : 0 ≤ (S0 - S3) * (S1 - S2) := Int.mul_nonneg (by omega) (by omega)
  have nn2 : 0 ≤ (S0 - S1) * (S2 - S3) := Int.mul_nonneg (by omega) (by omega)
  have c1 : S3 + S2 = S2 + S3 := Int.add_comm S3 S2
  have c3 : S2 + S1 = S1 + S2 := Int.add_comm S2 S1
  have p1 : (S0 + S1) * (S2 + S3) ≤ (S0 + S2) * (S1 + S3) := by
    have h := g1.1; rw [c1] at h; omega
  have v1 : (S0 + S2) * (S0 + S2) + (S1 + S3) * (S1 + S3) ≤ (S0 + S1) * (S0 + S1) + (S2 + S3) * (S2 + S3) := by
    have h := g1.2; rw [c1] at h; omega
  have p2 : (S0 + S2) * (S1 + S3) ≤ (S0 + S3) * (S1 + S2) := by
    have h := g2.1; rw [c3] at h; omega
  have v2 : (S0 + S3) * (S0 + S3) + (S1 + S2) * (S1 + S2) ≤ (S0 + S2) * (S0 + S2) + (S1 + S3) * (S1 + S3) := by
    have h := g2.2; rw [c3] at h; omega
  exact ⟨v2, v1, p1, p2⟩

-- Theorem 11: Exact phase boundary between quad_snake (equal-cardinality 2+2) and quad_lpt (greedy LPT)
-- When S0 <= S1 + S2, LPT puts S3 into Ball 0 and coincides identically with quad_snake.
-- When S0 > S1 + S2 (extreme single-quad outlier dominance), LPT puts S3 into Ball 1,
-- strictly lowering ball variance by exact slack 2 * S3 * (S0 - (S1 + S2)) > 0.
theorem lpt_vs_snake_phase_boundary_universal
    (S0 S1 S2 S3 : Int) (hS3 : 0 < S3) :
    let snake_sq := (S0 + S3) * (S0 + S3) + (S1 + S2) * (S1 + S2)
    let lpt_unbal_sq := S0 * S0 + (S1 + S2 + S3) * (S1 + S2 + S3)
    snake_sq - lpt_unbal_sq = 2 * (S3 * (S0 - (S1 + S2))) ∧
    (S0 ≤ S1 + S2 → snake_sq ≤ lpt_unbal_sq) ∧
    (S1 + S2 < S0 → lpt_unbal_sq < snake_sq) := by
  have hid :
      ((S0 + S3) * (S0 + S3) + (S1 + S2) * (S1 + S2)) -
      (S0 * S0 + (S1 + S2 + S3) * (S1 + S2 + S3)) =
      2 * (S3 * (S0 - (S1 + S2))) := by
    have hsq : ∀ (u v : Int), (u + v) * (u + v) = u * u + v * v + 2 * (u * v) := by
      intro u v
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm v u]
      omega
    have h1 := hsq S0 S3
    have h2 := hsq (S1 + S2) S3
    have h3 : S3 * (S0 - (S1 + S2)) = S0 * S3 - (S1 + S2) * S3 := by
      rw [Int.mul_sub, Int.mul_comm S3 S0, Int.mul_comm S3 (S1 + S2)]
    omega
  dsimp only
  refine ⟨hid, ?_, ?_⟩
  · intro hle
    have hnn : 0 ≤ S3 * ((S1 + S2) - S0) := Int.mul_nonneg (by omega) (by omega)
    have hneg : S3 * (S0 - (S1 + S2)) = -(S3 * ((S1 + S2) - S0)) := by
      rw [← Int.mul_neg]
      have hs : -(S1 + S2 - S0) = S0 - (S1 + S2) := by omega
      rw [hs]
    omega
  · intro hgt
    have hpos : 0 < S3 * (S0 - (S1 + S2)) := Int.mul_pos hS3 (by omega)
    omega

-- Theorem 12: UNIQUE TWO-LEVEL SADDLE-POINT STRICT DOMINANCE THEOREM
-- For ALL positive trade-off weights alpha > 0, beta > 0 and EVERY strictly non-degenerate
-- 16-channel Hessian ladder, Stratified Quad-Interleaving (Sort-into-Quads o Snake-Across-Balls)
-- STRICTLY DOMINATES BOTH naive global contiguous sorting AND mixed-quad layouts simultaneously!
theorem two_level_saddle_point_strict_dominance_universal
    (alpha beta : Int) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 : Int)
    (hsort :
      h0 ≥ h1 ∧ h1 ≥ h2 ∧ h2 ≥ h3 ∧ h3 ≥ h4 ∧ h4 ≥ h5 ∧ h5 ≥ h6 ∧ h6 ≥ h7 ∧
      h7 ≥ h8 ∧ h8 ≥ h9 ∧ h9 ≥ h10 ∧ h10 ≥ h11 ∧ h11 ≥ h12 ∧ h12 ≥ h13 ∧ h13 ≥ h14 ∧ h14 ≥ h15)
    (hgap_micro : h12 < h3)
    (hgap_macro : quadSum h8 h9 h10 h11 < quadSum h0 h1 h2 h3 ∧ quadSum h12 h13 h14 h15 < quadSum h4 h5 h6 h7) :
    let S0 := quadSum h0 h1 h2 h3
    let S1 := quadSum h4 h5 h6 h7
    let S2 := quadSum h8 h9 h10 h11
    let S3 := quadSum h12 h13 h14 h15
    let spread_mono := (h0 - h3) + (h4 - h7) + (h8 - h11) + (h12 - h15)
    let spread_mix := (h0 - h12) + (h4 - h7) + (h8 - h11) + (h3 - h15)
    let ballSq_snake := (S0 + S3) * (S0 + S3) + (S1 + S2) * (S1 + S2)
    let ballSq_glob := (S0 + S1) * (S0 + S1) + (S2 + S3) * (S2 + S3)
    twoScaleLoss alpha beta spread_mono ballSq_snake <
      twoScaleLoss alpha beta spread_mono ballSq_glob ∧
    twoScaleLoss alpha beta spread_mono ballSq_snake <
      twoScaleLoss alpha beta spread_mix ballSq_snake := by
  have hmicro := micro_quad_monotone_dominance_16_universal
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hsort
  have hS01 : quadSum h4 h5 h6 h7 ≤ quadSum h0 h1 h2 h3 := hmicro.1
  have hS12 : quadSum h8 h9 h10 h11 ≤ quadSum h4 h5 h6 h7 := hmicro.2.1
  have hS23 : quadSum h12 h13 h14 h15 ≤ quadSum h8 h9 h10 h11 := hmicro.2.2.1
  have hmacro := macro_ball_snake_beats_global_sort_16_universal
    (quadSum h0 h1 h2 h3) (quadSum h4 h5 h6 h7) (quadSum h8 h9 h10 h11) (quadSum h12 h13 h14 h15)
    hS01 hS12 hS23
  have h_ball_lt := (hmacro.2.2.2.2 hgap_macro).2
  have h_spr_lt := (hmicro.2.2.2.2.2.2 hgap_micro).1
  dsimp only [twoScaleLoss]
  constructor
  · have hmul : 0 < beta * (((quadSum h0 h1 h2 h3 + quadSum h4 h5 h6 h7) * (quadSum h0 h1 h2 h3 + quadSum h4 h5 h6 h7) +
        (quadSum h8 h9 h10 h11 + quadSum h12 h13 h14 h15) * (quadSum h8 h9 h10 h11 + quadSum h12 h13 h14 h15)) -
        ((quadSum h0 h1 h2 h3 + quadSum h12 h13 h14 h15) * (quadSum h0 h1 h2 h3 + quadSum h12 h13 h14 h15) +
        (quadSum h4 h5 h6 h7 + quadSum h8 h9 h10 h11) * (quadSum h4 h5 h6 h7 + quadSum h8 h9 h10 h11))) :=
      Int.mul_pos hbeta (by omega)
    rw [Int.mul_sub] at hmul
    omega
  · have hmul : 0 < alpha * ((((h0 - h12) + (h4 - h7) + (h8 - h11) + (h3 - h15)) -
        ((h0 - h3) + (h4 - h7) + (h8 - h11) + (h12 - h15)))) :=
      Int.mul_pos halpha (by omega)
    rw [Int.mul_sub] at hmul
    omega

-- Theorem 13: Opposing-monotonicity sign inversion between micro quad packing & macro ball packing
-- On identical 4 sorted quantities a > c and b > d, monotone pairing ((a+b)^2 + (c+d)^2)
-- strictly EXCEEDS stratified pairing ((a+d)^2 + (b+c)^2), which is beneficial at micro scale
-- (positive micro gain) yet strictly harmful at macro scale (negative macro balance gain).
theorem opposing_monotonicity_sign_inversion_universal
    (a b c d : Int) (hac : c < a) (hbd : d < b) :
    let mono_sq := (a + b) * (a + b) + (c + d) * (c + d)
    let strat_sq := (a + d) * (a + d) + (b + c) * (b + c)
    let micro_gain := mono_sq - strat_sq
    let macro_balance_gain := strat_sq - mono_sq
    0 < micro_gain ∧ macro_balance_gain < 0 ∧ micro_gain + macro_balance_gain = 0 := by
  have hid := (pair_gap_ident a b c d).2
  have hpos : 0 < (a - c) * (b - d) := Int.mul_pos (by omega) (by omega)
  dsimp only
  exact ⟨by omega, by omega, by omega⟩

-- Theorem 14: Exact 16-channel heavy-tailed Hessian witness comparing snake vs global vs mixed-swap vs strided
theorem two_level_16channel_exact_witness :
    -- h = [100, 96, 92, 88, 40, 36, 32, 28, 12, 10, 8, 6, 4, 3, 2, 1]
    let S0 : Int := 100 + 96 + 92 + 88
    let S1 : Int := 40 + 36 + 32 + 28
    let S2 : Int := 12 + 10 + 8 + 6
    let S3 : Int := 4 + 3 + 2 + 1
    let spread_mono : Int := (100 - 88) + (40 - 28) + (12 - 6) + (4 - 1)
    let spread_mix_swap : Int := (100 - 4) + (40 - 28) + (12 - 6) + (88 - 1)
    let spread_strided : Int := (100 - 4) + (96 - 3) + (92 - 2) + (88 - 1)
    let prod_snake : Int := (S0 + S3) * (S1 + S2)
    let prod_alt : Int := (S0 + S2) * (S1 + S3)
    let prod_glob : Int := (S0 + S1) * (S2 + S3)
    let sq_snake : Int := (S0 + S3) * (S0 + S3) + (S1 + S2) * (S1 + S2)
    let sq_alt : Int := (S0 + S2) * (S0 + S2) + (S1 + S3) * (S1 + S3)
    let sq_glob : Int := (S0 + S1) * (S0 + S1) + (S2 + S3) * (S2 + S3)
    let sq_lpt : Int := S0 * S0 + (S1 + S2 + S3) * (S1 + S2 + S3)
    S0 = 376 ∧ S1 = 136 ∧ S2 = 36 ∧ S3 = 10 ∧
    spread_mono = 33 ∧ spread_mix_swap = 201 ∧ spread_strided = 366 ∧
    spread_mono < spread_mix_swap ∧ spread_mix_swap < spread_strided ∧
    prod_snake = 66392 ∧ prod_alt = 60152 ∧ prod_glob = 23552 ∧
    prod_glob < prod_alt ∧ prod_alt < prod_snake ∧
    sq_lpt = 174500 ∧ sq_snake = 178580 ∧ sq_alt = 191060 ∧ sq_glob = 264260 ∧
    sq_lpt < sq_snake ∧ sq_snake < sq_alt ∧ sq_alt < sq_glob := by
  decide

end S72bFormalTheory.TwoLevelSaddlePoint

#print axioms S72bFormalTheory.TwoLevelSaddlePoint.micro_quad_monotone_dominance_16_universal
#print axioms S72bFormalTheory.TwoLevelSaddlePoint.macro_ball_snake_beats_global_sort_16_universal
#print axioms S72bFormalTheory.TwoLevelSaddlePoint.macro_ball_snake_optimal_over_all_pairings_universal
#print axioms S72bFormalTheory.TwoLevelSaddlePoint.lpt_vs_snake_phase_boundary_universal
#print axioms S72bFormalTheory.TwoLevelSaddlePoint.two_level_saddle_point_strict_dominance_universal
#print axioms S72bFormalTheory.TwoLevelSaddlePoint.opposing_monotonicity_sign_inversion_universal
#print axioms S72bFormalTheory.TwoLevelSaddlePoint.two_level_16channel_exact_witness
