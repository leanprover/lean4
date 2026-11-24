-- Pure-Init Lean 4.36.0 formalization of the 3-Model Regime Triangle obstruction
-- (unbounded 3rd-vertex residual for any 2-term MSE+E05 rule), simplex minimax-regret
-- dominance, Construction-A Extended Hamming turnover, and exact rational minimax-regret
-- optimality of A_16 across all 5 bitrate x model cells. Zero imports, zero Mathlib.

namespace S70FormalTheory.RegimeTriangleMinimax

-- Theorem 15: Universal 3-vertex simplex obstruction for 2-term (MSE, E_05) scoring rules.
-- For EVERY non-negative 2-term rule S(d, e) = wd * d + we * e ignoring the 3rd vertex k
-- (with positive 3rd-vertex weight wk > 0) and EVERY residual threshold M, there exist arms A, B
-- where A strictly beats B on BOTH d and e (so S(A) <= S(B)), yet true 3-vertex loss satisfies
-- L(A) - L(B) >= M.
theorem two_term_simplex_obstruction_universal
    (wd we wk M : Int) (hwd : 0 ≤ wd) (hwe : 0 ≤ we) (hwk : 0 < wk) (hM : 0 ≤ M) :
    ∃ (dA eA kA dB eB kB : Int),
      dA < dB ∧ eA < eB ∧
      wd * dA + we * eA ≤ wd * dB + we * eB ∧
      M ≤ (wd * dA + we * eA + wk * kA) - (wd * dB + we * eB + wk * kB) := by
  let kA : Int := M + wd + we + 1
  refine ⟨0, 0, kA, 1, 1, 0, by omega, by omega, ?_, ?_⟩
  · simp only [Int.mul_zero, Int.add_zero, Int.mul_one]
    omega
  · simp only [Int.mul_zero, Int.add_zero, Int.zero_add, Int.mul_one]
    have hk_ge : kA ≤ wk * kA := by
      have h1 : 1 * kA ≤ wk * kA := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    omega

-- Theorem 16: Universal convex-combination regret bound across the entire 3-vertex simplex.
-- If an arm's regret at each vertex is <= R, then its regret under EVERY non-negative convex
-- mixture (lam1, lam2, lam3) is <= (lam1 + lam2 + lam3) * R.
theorem simplex_convex_regret_bound_universal
    (lam1 lam2 lam3 r1 r2 r3 R : Int)
    (hl1 : 0 ≤ lam1) (hl2 : 0 ≤ lam2) (hl3 : 0 ≤ lam3)
    (hr1 : r1 ≤ R) (hr2 : r2 ≤ R) (hr3 : r3 ≤ R) :
    lam1 * r1 + lam2 * r2 + lam3 * r3 ≤ (lam1 + lam2 + lam3) * R := by
  have h1 : lam1 * r1 ≤ lam1 * R := Int.mul_le_mul_of_nonneg_left hr1 hl1
  have h2 : lam2 * r2 ≤ lam2 * R := Int.mul_le_mul_of_nonneg_left hr2 hl2
  have h3 : lam3 * r3 ≤ lam3 * R := Int.mul_le_mul_of_nonneg_left hr3 hl3
  rw [Int.add_mul, Int.add_mul]
  omega

-- Theorem 17: Universal minimax-regret unique optimality on a 3-vertex simplex.
-- If arm C* has max-vertex regret <= R while every rival suffers strictly > R on at least
-- one vertex, then C* strictly minimizes worst-case regret over the entire simplex.
theorem simplex_unique_minimax_universal
    (rStar1 rStar2 rStar3 R rAlt1 rAlt2 rAlt3 : Int)
    (hstar : rStar1 ≤ R ∧ rStar2 ≤ R ∧ rStar3 ≤ R)
    (halt : R < rAlt1 ∨ R < rAlt2 ∨ R < rAlt3) :
    max (max rStar1 rStar2) rStar3 < max (max rAlt1 rAlt2) rAlt3 := by
  have hL : max (max rStar1 rStar2) rStar3 ≤ R := by
    simp only [Int.max_def]
    split <;> split <;> omega
  have hR : R < max (max rAlt1 rAlt2) rAlt3 := by
    simp only [Int.max_def]
    split <;> split <;> rcases halt with h1 | h2 | h3 <;> omega
  omega

-- Theorem 18: Exact Construction-A Extended Hamming [2^m, 2^m - m - 1, 4] (m = 3, 4, 5)
-- rate monotonicity, parity density decay, determinant doubling, and covering_sq(128) drop.
theorem hamming_family_exact_rate_and_covering :
    let n8 := 8; let k8 := 4; let det8 := 16; let cov8 := 56
    let n16 := 16; let k16 := 11; let det16 := 32; let cov16 := 44
    let n32 := 32; let k32 := 26; let det32 := 64; let cov32 := 38
    k8 * n16 < k16 * n8 ∧
    k16 * n32 < k32 * n16 ∧
    (n8 - k8) * n16 > (n16 - k16) * n8 ∧
    (n16 - k16) * n32 > (n32 - k32) * n16 ∧
    det8 * 2 = det16 ∧
    det16 * 2 = det32 ∧
    cov8 > cov16 ∧
    cov16 > cov32 ∧
    -- Exact DP reconciliation for A_16 (B=1207, L=16, k=2) & A_32 (B=1015, L=32, k=1)
    (16 + 1) * (2 * 16) * (1207 + 1) + (2 + 1) * (1207 + 1) = 660776 ∧
    (32 + 1) * (2 * 16) * (1207 + 1) = 1275648 ∧
    (32 + 1) * (2 * 32) * (1015 + 1) + (1 + 1) * (1015 + 1) = 2147824 ∧
    (32 + 1) * (2 * 32) * (1015 + 1) = 2145792 ∧
    2147824 - 2145792 = 2032 := by
  decide

-- Theorem 19: Exact Llama-3.2-1B two-term obstruction witness
-- A32BG strictly beats HBG on BOTH pooled MSE (-25.627 < -25.585 dB) and E_05 (0.15 < 3.48 dB)
-- yet strictly loses on real WikiText-2 KL (39540 > 36038 micro-KL, squared SE-gap > 18).
theorem llama_a32_two_term_obstruction_exact_witness :
    let db_a32 : Int := -25627
    let db_hbg : Int := -25585
    let e05_a32 : Int := 15
    let e05_hbg : Int := 348
    let kl_a32 : Int := 39540
    let kl_hbg : Int := 36038
    let se_a32 : Int := 610
    let se_hbg : Int := 526
    db_a32 < db_hbg ∧
    e05_a32 < e05_hbg ∧
    kl_hbg < kl_a32 ∧
    (kl_a32 - kl_hbg) * (kl_a32 - kl_hbg) = 12264004 ∧
    se_a32 * se_a32 + se_hbg * se_hbg = 648776 ∧
    18 * (se_a32 * se_a32 + se_hbg * se_hbg) < (kl_a32 - kl_hbg) * (kl_a32 - kl_hbg) := by
  decide

-- Theorem 20: Exact unique minimax-regret optimality of A_16 across all 3 models at 4.5 bpw
-- Exact worst-case relative regrets:
--   A16BG: 2157/45800 (4.7096%) < HBG: 2861/22900 (12.4934%) < A32BG: 339/2297 (14.7584%)
--          < EBG: 15061/45800 (32.8843%) < ZBG: 4451/11485 (38.7549%)
theorem a16_unique_minimax_regret_45bpw_witness :
    -- Exact micro-KL table at 4.5 bpw (Qwen2.5-1.5B, SmolLM2-1.7B, Llama-3.2-1B)
    let q_best : Int := 18875
    let s_best : Int := 45800
    let l_best : Int := 34455
    -- Verify A16BG worst cell at 4.5 bpw is SmolLM2 (2157/45800)
    (18974 - q_best) * s_best ≤ (47957 - s_best) * q_best ∧
    (34455 - l_best) * s_best ≤ (47957 - s_best) * l_best ∧
    -- Verify exact strict total ordering of worst-case relative regrets at 4.5 bpw
    (47957 - s_best) * s_best < (51522 - s_best) * s_best ∧
    (51522 - s_best) * l_best < (39540 - l_best) * s_best ∧
    (39540 - l_best) * s_best < (60861 - s_best) * l_best ∧
    (60861 - s_best) * l_best < (47808 - l_best) * s_best := by
  decide

-- Theorem 21: Exact unique minimax-regret optimality of A_16 across ALL 5 bitrate x model cells
-- (3 models @ 4.5 bpw + 2 models @ 3.0 bpw).
-- Exact strict total ordering of worst-case relative regrets across all 5 cells:
--   A16BG (7383/119615 = 6.1723%) < A32BG (339/2297 = 14.7584%)
--         < ZBG (4451/11485 = 38.7549%) < HBG (271057/358845 = 75.5360%)
--         < EBG (305344/358845 = 85.0908%)
theorem a16_unique_minimax_regret_all5_cells_witness :
    let q45_b : Int := 18875; let s45_b : Int := 45800; let l45_b : Int := 34455
    let q30_b : Int := 160368; let s30_b : Int := 358845
    -- 1. Confirm A16BG worst-case relative regret across all 5 cells is S17_30: 22149/358845 = 7383/119615
    (18974 - q45_b) * s30_b ≤ (380994 - s30_b) * q45_b ∧
    (47957 - s45_b) * s30_b ≤ (380994 - s30_b) * s45_b ∧
    (34455 - l45_b) * s30_b ≤ (380994 - s30_b) * l45_b ∧
    (160368 - q30_b) * s30_b ≤ (380994 - s30_b) * q30_b ∧
    -- 2. Confirm exact reduced numerator/denominator identities
    (380994 - s30_b) * 119615 = 7383 * s30_b ∧
    (39540 - l45_b) * 2297 = 339 * l45_b ∧
    (47808 - l45_b) * 11485 = 4451 * l45_b ∧
    (629902 - s30_b) = 271057 ∧
    (664189 - s30_b) = 305344 ∧
    -- 3. Strict 5-arm total ordering of worst-case relative regret across all 5 cells
    7383 * 2297 < 339 * 119615 ∧
    339 * 11485 < 4451 * 2297 ∧
    4451 * 358845 < 271057 * 11485 ∧
    271057 < 305344 ∧
    -- 4. A16BG achieves rank <= 2 in ALL 5 cells ({2, 2, 1, 1, 2})
    (18974 < 19032 ∧ 18974 < 19549 ∧ 18974 < 22750) ∧
    (47957 < 51522 ∧ 47957 < 55962 ∧ 47957 < 60861) ∧
    (34455 < 36038 ∧ 34455 < 39540 ∧ 34455 < 40161 ∧ 34455 < 47808) ∧
    (160368 < 169338 ∧ 160368 < 174194 ∧ 160368 < 178526 ∧ 160368 < 215147) ∧
    (380994 < 419643 ∧ 380994 < 629902 ∧ 380994 < 664189) := by
  decide

end S70FormalTheory.RegimeTriangleMinimax

#print axioms S70FormalTheory.RegimeTriangleMinimax.two_term_simplex_obstruction_universal
#print axioms S70FormalTheory.RegimeTriangleMinimax.simplex_convex_regret_bound_universal
#print axioms S70FormalTheory.RegimeTriangleMinimax.simplex_unique_minimax_universal
#print axioms S70FormalTheory.RegimeTriangleMinimax.hamming_family_exact_rate_and_covering
#print axioms S70FormalTheory.RegimeTriangleMinimax.llama_a32_two_term_obstruction_exact_witness
#print axioms S70FormalTheory.RegimeTriangleMinimax.a16_unique_minimax_regret_45bpw_witness
#print axioms S70FormalTheory.RegimeTriangleMinimax.a16_unique_minimax_regret_all5_cells_witness
