-- Pure-Init Lean 4.36.0 formalization of Group-Ball Hessian Budget-Transfer
-- Cannibalization: 2-ball AM-GM product/variance gap, product-vs-variance equivalence,
-- universal G-ball Cauchy-Schwarz floor with exact equality characterization,
-- 4-quad pairing ordering, and exact 4-model empirical witness.
-- Zero imports, zero Mathlib.

namespace S72bFormalTheory.BallBudgetCannibalization

def sumList : List Int → Int
  | [] => 0
  | x :: xs => x + sumList xs

def sumSq : List Int → Int
  | [] => 0
  | x :: xs => x * x + sumSq xs

def sumDiffSq (x : Int) : List Int → Int
  | [] => 0
  | y :: ys => (x - y) * (x - y) + sumDiffSq x ys

private theorem sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases x with
  | ofNat n =>
    change 0 ≤ Int.ofNat (n * n)
    exact Int.natCast_nonneg (n * n)
  | negSucc n =>
    change 0 ≤ Int.ofNat ((n + 1) * (n + 1))
    exact Int.natCast_nonneg ((n + 1) * (n + 1))

private theorem sumDiffSq_nonneg (x : Int) : ∀ (ys : List Int), 0 ≤ sumDiffSq x ys
  | [] => Int.le_refl 0
  | y :: ys => Int.add_nonneg (sq_nonneg (x - y)) (sumDiffSq_nonneg x ys)

private theorem sumDiffSq_expand (x : Int) :
    ∀ (ys : List Int),
      sumDiffSq x ys = (ys.length : Int) * (x * x) - 2 * (x * sumList ys) + sumSq ys
  | [] => by simp [sumDiffSq, sumList, sumSq]
  | y :: ys => by
    have ih := sumDiffSq_expand x ys
    simp only [sumDiffSq, sumList, sumSq, List.length_cons]
    have hlen : ((ys.length + 1 : Nat) : Int) = (ys.length : Int) + 1 := by omega
    rw [hlen, Int.add_mul, Int.one_mul, Int.mul_add]
    have hsq : (x - y) * (x - y) = x * x + y * y - 2 * (x * y) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y x]
      omega
    omega

private theorem sumDiffSq_eq_zero_imp (x : Int) :
    ∀ (ys : List Int), sumDiffSq x ys = 0 → ∀ y, y ∈ ys → y = x
  | [], _, _, hmem => nomatch hmem
  | z :: zs, hzero, y, hmem => by
    simp only [sumDiffSq] at hzero
    have h1 := sq_nonneg (x - z)
    have h2 := sumDiffSq_nonneg x zs
    have hz_sq : (x - z) * (x - z) = 0 := by omega
    have hzs : sumDiffSq x zs = 0 := by omega
    have hxz : x - z = 0 := by
      cases Int.mul_eq_zero.mp hz_sq with
      | inl h => exact h
      | inr h => exact h
    cases hmem with
    | head => omega
    | tail _ htail => exact sumDiffSq_eq_zero_imp x zs hzs y htail

-- Theorem 1: Universal 2-ball AM-GM product & variance cannibalization theorem
-- Packing loud loads into Ball 0 ((a+b, c+d)) strictly lowers the rate-distortion product
-- and raises variance relative to balanced stratification ((a+d, b+c)) with exact gap (a-c)(b-d).
theorem two_ball_product_and_variance_cannibalization_universal (a b c d : Int) :
    (a + d) * (b + c) - (a + b) * (c + d) = (a - c) * (b - d) ∧
    ((a + b) * (a + b) + (c + d) * (c + d)) -
      ((a + d) * (a + d) + (b + c) * (b + c)) = 2 * ((a - c) * (b - d)) ∧
    ((c ≤ a ∧ d ≤ b) →
      (a + b) * (c + d) ≤ (a + d) * (b + c) ∧
      (a + d) * (a + d) + (b + c) * (b + c) ≤ (a + b) * (a + b) + (c + d) * (c + d)) ∧
    ((c < a ∧ d < b) →
      (a + b) * (c + d) < (a + d) * (b + c) ∧
      (a + d) * (a + d) + (b + c) * (b + c) < (a + b) * (a + b) + (c + d) * (c + d)) := by
  have hprod : (a + d) * (b + c) - (a + b) * (c + d) = (a - c) * (b - d) := by
    simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
    have hbc := Int.mul_comm c b
    have hdb := Int.mul_comm d b
    have hdc := Int.mul_comm d c
    have hda := Int.mul_comm d a
    have hba := Int.mul_comm b a
    have hca := Int.mul_comm c a
    omega
  have hvar :
      ((a + b) * (a + b) + (c + d) * (c + d)) -
      ((a + d) * (a + d) + (b + c) * (b + c)) = 2 * ((a - c) * (b - d)) := by
    simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
    have hba := Int.mul_comm b a
    have hda := Int.mul_comm d a
    have hcb := Int.mul_comm c b
    have hdc := Int.mul_comm d c
    omega
  refine ⟨hprod, hvar, ?_, ?_⟩
  · rintro ⟨hca, hdb⟩
    have hnn : 0 ≤ (a - c) * (b - d) := Int.mul_nonneg (by omega) (by omega)
    exact ⟨by omega, by omega⟩
  · rintro ⟨hca, hdb⟩
    have hpos : 0 < (a - c) * (b - d) := Int.mul_pos (by omega) (by omega)
    exact ⟨by omega, by omega⟩

-- Theorem 2: Exact equivalence of maximizing 2-ball product and minimizing 2-ball variance at fixed load
theorem two_ball_product_variance_equivalence_universal
    (B0 B1 B0' B1' : Int) (htot : B0 + B1 = B0' + B1') :
    2 * (B0' * B1' - B0 * B1) = (B0 * B0 + B1 * B1) - (B0' * B0' + B1' * B1') ∧
    (B0 * B1 < B0' * B1' ↔ B0' * B0' + B1' * B1' < B0 * B0 + B1 * B1) := by
  have hsq_eq : (B0 + B1) * (B0 + B1) = (B0' + B1') * (B0' + B1') := by rw [htot]
  have hid : 2 * (B0' * B1' - B0 * B1) = (B0 * B0 + B1 * B1) - (B0' * B0' + B1' * B1') := by
    simp only [Int.add_mul, Int.mul_add] at hsq_eq
    have c1 := Int.mul_comm B1 B0
    have c2 := Int.mul_comm B1' B0'
    omega
  exact ⟨hid, ⟨fun h => by omega, fun h => by omega⟩⟩

private theorem step_rhs_expand (n : Nat) (x q : Int) :
    ((n + 1 : Nat) : Int) * (x * x + q) = (n : Int) * (x * x) + (n : Int) * q + x * x + q := by
  have hlen : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
  rw [hlen, Int.add_mul, Int.one_mul, Int.mul_add]
  omega

-- Theorem 3: Universal G-ball Cauchy-Schwarz / Jensen variance floor over arbitrary list length G
theorem g_ball_cauchy_schwarz_variance_floor_universal :
    ∀ (loads : List Int), sumList loads * sumList loads ≤ (loads.length : Int) * sumSq loads
  | [] => by simp [sumList, sumSq]
  | x :: xs => by
    have ih := g_ball_cauchy_schwarz_variance_floor_universal xs
    have hdiff := sumDiffSq_nonneg x xs
    have hexp := sumDiffSq_expand x xs
    simp only [sumList, sumSq, List.length_cons]
    have hrhs := step_rhs_expand xs.length x (sumSq xs)
    have hsq : (x + sumList xs) * (x + sumList xs) =
        x * x + sumList xs * sumList xs + 2 * (x * sumList xs) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (sumList xs) x]
      omega
    omega

-- Theorem 4: Exact equality in G-ball Cauchy-Schwarz holds iff all ball loads are equal
theorem g_ball_variance_floor_equality_iff_balanced_universal :
    ∀ (loads : List Int),
      ((loads.length : Int) * sumSq loads = sumList loads * sumList loads) ↔
      (∀ x y, x ∈ loads → y ∈ loads → x = y)
  | [] => ⟨(fun _ _ _ hx => nomatch hx), (fun _ => by simp [sumList, sumSq])⟩
  | x :: xs => by
    constructor
    · intro heq
      have ih_ge := g_ball_cauchy_schwarz_variance_floor_universal xs
      have hdiff_nn := sumDiffSq_nonneg x xs
      have hexp := sumDiffSq_expand x xs
      simp only [sumList, sumSq, List.length_cons] at heq
      have hrhs := step_rhs_expand xs.length x (sumSq xs)
      have hsq : (x + sumList xs) * (x + sumList xs) =
          x * x + sumList xs * sumList xs + 2 * (x * sumList xs) := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (sumList xs) x]
        omega
      have hdiff0 : sumDiffSq x xs = 0 := by omega
      have hall_eq : ∀ z, z ∈ xs → z = x := sumDiffSq_eq_zero_imp x xs hdiff0
      intro u v hu hv
      cases hu with
      | head =>
        cases hv with
        | head => rfl
        | tail _ hvt => exact (hall_eq v hvt).symm
      | tail _ hut =>
        have hux := hall_eq u hut
        cases hv with
        | head => exact hux
        | tail _ hvt => rw [hux, hall_eq v hvt]
    · intro hall
      have hxs_all : ∀ u v, u ∈ xs → v ∈ xs → u = v :=
        fun u v hu hv => hall u v (List.Mem.tail x hu) (List.Mem.tail x hv)
      have ih_eq : (xs.length : Int) * sumSq xs = sumList xs * sumList xs :=
        (g_ball_variance_floor_equality_iff_balanced_universal xs).mpr hxs_all
      have hdiff0 : ∀ (ys : List Int), (∀ z, z ∈ ys → z = x) → sumDiffSq x ys = 0 := by
        intro ys
        induction ys with
        | nil => intro _; rfl
        | cons w ws ihw =>
          intro hw
          have hwx : w = x := hw w (List.Mem.head ws)
          have hws : ∀ z, z ∈ ws → z = x := fun z hz => hw z (List.Mem.tail w hz)
          simp only [sumDiffSq, hwx, Int.sub_self, Int.zero_mul, Int.zero_add]
          exact ihw hws
      have hxs_x : ∀ z, z ∈ xs → z = x :=
        fun z hz => hall z x (List.Mem.tail x hz) (List.Mem.head xs)
      have hd0 := hdiff0 xs hxs_x
      have hexp := sumDiffSq_expand x xs
      simp only [sumList, sumSq, List.length_cons]
      have hrhs := step_rhs_expand xs.length x (sumSq xs)
      have hsq : (x + sumList xs) * (x + sumList xs) =
          x * x + sumList xs * sumList xs + 2 * (x * sumList xs) := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm (sumList xs) x]
        omega
      omega

-- Theorem 5: Exact quadratic penalty of shifting load by delta away from balanced 2-ball split
theorem ball_transfer_imbalance_penalty_universal (B delta : Int) :
    B * B - (B + delta) * (B - delta) = delta * delta ∧
    ((B + delta) * (B + delta) + (B - delta) * (B - delta)) - (B * B + B * B) = 2 * (delta * delta) := by
  have h1 : (B + delta) * (B - delta) = B * B - delta * delta := by
    rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm delta B]
    omega
  have h2 : (B + delta) * (B + delta) + (B - delta) * (B - delta) = 2 * (B * B) + 2 * (delta * delta) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm delta B]
    omega
  exact ⟨by omega, by omega⟩

-- Theorem 6: Global contiguous sort minimizes product & maximizes variance among ALL 3 pairings of 4 quads
theorem global_sort_worst_among_three_4quad_pairings_universal
    (Q0 Q1 Q2 Q3 : Int) (h01 : Q1 ≤ Q0) (h12 : Q2 ≤ Q1) (h23 : Q3 ≤ Q2) :
    (Q0 + Q1) * (Q2 + Q3) ≤ (Q0 + Q2) * (Q1 + Q3) ∧
    (Q0 + Q2) * (Q1 + Q3) ≤ (Q0 + Q3) * (Q1 + Q2) ∧
    (Q0 + Q3) * (Q0 + Q3) + (Q1 + Q2) * (Q1 + Q2) ≤ (Q0 + Q2) * (Q0 + Q2) + (Q1 + Q3) * (Q1 + Q3) ∧
    (Q0 + Q2) * (Q0 + Q2) + (Q1 + Q3) * (Q1 + Q3) ≤ (Q0 + Q1) * (Q0 + Q1) + (Q2 + Q3) * (Q2 + Q3) := by
  have h_step1 := (two_ball_product_and_variance_cannibalization_universal Q0 Q1 Q3 Q2).2.2.1 ⟨by omega, by omega⟩
  have h_step2 := (two_ball_product_and_variance_cannibalization_universal Q0 Q2 Q1 Q3).2.2.1 ⟨by omega, by omega⟩
  have c1 : Q3 + Q2 = Q2 + Q3 := Int.add_comm Q3 Q2
  have h1_prod : (Q0 + Q1) * (Q2 + Q3) ≤ (Q0 + Q2) * (Q1 + Q3) := by
    have hp := h_step1.1
    rw [c1] at hp
    exact hp
  have h1_var : (Q0 + Q2) * (Q0 + Q2) + (Q1 + Q3) * (Q1 + Q3) ≤ (Q0 + Q1) * (Q0 + Q1) + (Q2 + Q3) * (Q2 + Q3) := by
    have hv := h_step1.2
    rw [c1] at hv
    exact hv
  have c3 : Q2 + Q1 = Q1 + Q2 := Int.add_comm Q2 Q1
  have h2_prod : (Q0 + Q2) * (Q1 + Q3) ≤ (Q0 + Q3) * (Q1 + Q2) := by
    have hp := h_step2.1
    rw [c3] at hp
    exact hp
  have h2_var : (Q0 + Q3) * (Q0 + Q3) + (Q1 + Q2) * (Q1 + Q2) ≤ (Q0 + Q2) * (Q0 + Q2) + (Q1 + Q3) * (Q1 + Q3) := by
    have hv := h_step2.2
    rw [c3] at hv
    exact hv
  exact ⟨h1_prod, h2_prod, h2_var, h1_var⟩

-- Theorem 7: Exact 4-model global-sort cannibalization falsification witness (nanonats, 10^-9 nats)
-- Anchored read-only to frozen rtx3080_s69_empirical_results.json (SHA-256 05175f89...).
theorem s69_four_model_global_sort_cannibalization_witness :
    -- SmolLM2-360M WikiText-2 nanonats
    let s360_real : Int := 28206886
    let s360_grp128 : Int := 30635795
    let s360_sort : Int := 45765950
    -- Qwen2.5-0.5B WikiText-2 nanonats
    let q05_grp128 : Int := 27189940
    let q05_real : Int := 29412649
    let q05_sort : Int := 32504237
    -- Qwen2.5-1.5B WikiText-2 & Python nanonats
    let q15_wt_grp128 : Int := 23176037
    let q15_wt_h2 : Int := 23281449
    let q15_wt_real : Int := 23411598
    let q15_wt_sort : Int := 26786727
    let q15_py_grp128 : Int := 14083191
    let q15_py_h2 : Int := 14356267
    let q15_py_real : Int := 15128765
    let q15_py_sort : Int := 17099112
    -- Qwen2.5-3B WikiText-2 nanonats
    let q3_real : Int := 24774488
    let q3_grp128 : Int := 24917616
    let q3_sort : Int := 26025440
    -- 4/4 models: global sort strictly worsens over unpermuted real AND local grp128 beats global sort
    s360_real < s360_sort ∧ s360_grp128 < s360_sort ∧
    q05_grp128 < q05_real ∧ q05_real < q05_sort ∧
    q15_wt_grp128 < q15_wt_h2 ∧ q15_wt_h2 < q15_wt_real ∧ q15_wt_real < q15_wt_sort ∧
    q15_py_grp128 < q15_py_h2 ∧ q15_py_h2 < q15_py_real ∧ q15_py_real < q15_py_sort ∧
    q3_real < q3_sort ∧ q3_grp128 < q3_sort := by
  decide

end S72bFormalTheory.BallBudgetCannibalization

#print axioms S72bFormalTheory.BallBudgetCannibalization.two_ball_product_and_variance_cannibalization_universal
#print axioms S72bFormalTheory.BallBudgetCannibalization.two_ball_product_variance_equivalence_universal
#print axioms S72bFormalTheory.BallBudgetCannibalization.g_ball_cauchy_schwarz_variance_floor_universal
#print axioms S72bFormalTheory.BallBudgetCannibalization.g_ball_variance_floor_equality_iff_balanced_universal
#print axioms S72bFormalTheory.BallBudgetCannibalization.ball_transfer_imbalance_penalty_universal
#print axioms S72bFormalTheory.BallBudgetCannibalization.global_sort_worst_among_three_4quad_pairings_universal
#print axioms S72bFormalTheory.BallBudgetCannibalization.s69_four_model_global_sort_cannibalization_witness
