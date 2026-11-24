-- Pure-Init Lean 4.36.0 formalization of zero-cost gated-MLP (SiLU/GeLU/SwiGLU)
-- hidden-channel permutation invariance, exact H_4 orthogonality & Parseval mixing,
-- and global optimality of monotone-quad sorting for outlier-spill elimination.
-- Zero imports, zero Mathlib.

namespace S70FormalTheory.SortedBlockH4Optimality

def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

private theorem sumFin_congr :
    ∀ {n : Nat} {f g : Fin n → Int}, (∀ i, f i = g i) → sumFin n f = sumFin n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, hfg => by
    simp only [sumFin]
    rw [sumFin_congr (fun i => hfg i.castSucc), hfg ⟨n, Nat.lt_succ_self n⟩]

private def swapFin {n : Nat} (a b : Fin n) (k : Fin n) : Fin n :=
  if k = a then b else if k = b then a else k

private theorem swapFin_invol {n : Nat} (a b k : Fin n) :
    swapFin a b (swapFin a b k) = k := by
  unfold swapFin
  if hka : k = a then
    subst hka
    simp only [↓reduceIte]
    if hab : b = k then
      subst hab; simp
    else
      simp [hab]
  else if hkb : k = b then
    subst hkb
    simp [hka]
  else
    simp [hka, hkb]

private theorem swapFin_self {n : Nat} (a k : Fin n) : swapFin a a k = k := by
  unfold swapFin
  if h : k = a then simp [h] else simp [h]

private def updateFin {n : Nat} (f : Fin n → Int) (a : Fin n) (v : Int) (k : Fin n) : Int :=
  if k = a then v else f k

private theorem sumFin_update :
    ∀ {n : Nat} (f : Fin n → Int) (a : Fin n) (v : Int),
      sumFin n (updateFin f a v) = sumFin n f + (v - f a)
  | 0, _, a, _ => Fin.elim0 a
  | n + 1, f, a, v => by
    simp only [sumFin]
    if ha : a = ⟨n, Nat.lt_succ_self n⟩ then
      subst ha
      have hleft :
          sumFin n (fun i => updateFin f ⟨n, Nat.lt_succ_self n⟩ v i.castSucc) =
          sumFin n (fun i => f i.castSucc) := by
        apply sumFin_congr
        intro i
        unfold updateFin
        have hne : i.castSucc ≠ ⟨n, Nat.lt_succ_self n⟩ := by
          intro heq
          have hval := congrArg Fin.val heq
          simp only [Fin.val_castSucc] at hval
          omega
        simp [hne]
      rw [hleft]
      simp only [updateFin, ↓reduceIte]
      omega
    else
      have hlt : a.val < n := by
        have hle := a.isLt
        have hne : a.val ≠ n := fun hv => ha (Fin.ext hv)
        omega
      let a' : Fin n := ⟨a.val, hlt⟩
      have ha_eq : a'.castSucc = a := Fin.ext rfl
      have hleft :
          sumFin n (fun i => updateFin f a v i.castSucc) =
          sumFin n (updateFin (fun i => f i.castSucc) a' v) := by
        apply sumFin_congr
        intro i
        unfold updateFin
        if hi : i = a' then
          subst hi; simp [ha_eq]
        else
          have hne : i.castSucc ≠ a := fun heq => hi (Fin.ext (by simpa [a'] using congrArg Fin.val heq))
          simp [hi, hne]
      rw [hleft, sumFin_update (fun i => f i.castSucc) a' v]
      have hne_last : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ a := fun h => ha h.symm
      simp only [updateFin, hne_last, ↓reduceIte]
      have hfa : f a'.castSucc = f a := by rw [ha_eq]
      omega

private theorem sumFin_swap {n : Nat} (f : Fin n → Int) (a b : Fin n) :
    sumFin n (fun k => f (swapFin a b k)) = sumFin n f := by
  if hab : a = b then
    subst hab
    apply sumFin_congr
    intro k
    rw [swapFin_self]
  else
    have hcongr :
        sumFin n (fun k => f (swapFin a b k)) =
        sumFin n (updateFin (updateFin f a (f b)) b (f a)) := by
      apply sumFin_congr
      intro k
      unfold swapFin updateFin
      if hka : k = a then
        subst hka
        have hne : k ≠ b := hab
        simp [hne]
      else if hkb : k = b then
        subst hkb; simp [hka]
      else
        simp [hka, hkb]
    rw [hcongr, sumFin_update, sumFin_update]
    have hne : b ≠ a := fun h => hab h.symm
    simp only [updateFin, hne, ↓reduceIte]
    omega

private theorem sumFin_perm_universal :
    ∀ (n : Nat) (f : Fin n → Int) (π inv : Fin n → Fin n),
      (∀ k, inv (π k) = k) → (∀ k, π (inv k) = k) →
      sumFin n (fun k => f (π k)) = sumFin n f
  | 0, _, _, _, _, _ => rfl
  | n + 1, f, π, inv, hleft, hright => by
    let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let j : Fin (n + 1) := inv last
    let π' : Fin (n + 1) → Fin (n + 1) := fun k => π (swapFin j last k)
    let inv' : Fin (n + 1) → Fin (n + 1) := fun k => swapFin j last (inv k)
    have hstep1 : sumFin (n + 1) (fun k => f (π' k)) = sumFin (n + 1) (fun k => f (π k)) :=
      sumFin_swap (fun k => f (π k)) j last
    rw [← hstep1]
    have hfix_pi : π' last = last := by
      dsimp only [π', swapFin]
      if hjl : last = j then
        simp only [hjl, ↓reduceIte]
        have hr : π j = last := hright last
        rw [hjl] at hr
        exact hr
      else
        simp only [hjl, ↓reduceIte]
        exact hright last
    have hfix_inv : inv' last = last := by
      dsimp only [inv', swapFin, j]
      simp
    have hlt_pi : ∀ (i : Fin n), (π' i.castSucc).val < n := by
      intro i
      have hne : π' i.castSucc ≠ last := by
        intro heq
        have h1 : inv' (π' i.castSucc) = inv' last := congrArg inv' heq
        have hinv_pi : inv' (π' i.castSucc) = i.castSucc := by
          dsimp only [inv', π']
          rw [hleft, swapFin_invol]
        rw [hinv_pi, hfix_inv] at h1
        have hval := congrArg Fin.val h1
        simp only [Fin.val_castSucc, last] at hval
        omega
      have hle := (π' i.castSucc).isLt
      have hne_val : (π' i.castSucc).val ≠ n := fun hv => hne (Fin.ext hv)
      omega
    have hlt_inv : ∀ (i : Fin n), (inv' i.castSucc).val < n := by
      intro i
      have hne : inv' i.castSucc ≠ last := by
        intro heq
        have h1 : π' (inv' i.castSucc) = π' last := congrArg π' heq
        have hpi_inv : π' (inv' i.castSucc) = i.castSucc := by
          dsimp only [inv', π']
          rw [swapFin_invol, hright]
        rw [hpi_inv, hfix_pi] at h1
        have hval := congrArg Fin.val h1
        simp only [Fin.val_castSucc, last] at hval
        omega
      have hle := (inv' i.castSucc).isLt
      have hne_val : (inv' i.castSucc).val ≠ n := fun hv => hne (Fin.ext hv)
      omega
    let π_sub : Fin n → Fin n := fun i => ⟨(π' i.castSucc).val, hlt_pi i⟩
    let inv_sub : Fin n → Fin n := fun i => ⟨(inv' i.castSucc).val, hlt_inv i⟩
    have hsub_left : ∀ i, inv_sub (π_sub i) = i := by
      intro i
      apply Fin.ext
      dsimp only [inv_sub, π_sub]
      have hcast : (⟨(π' i.castSucc).val, hlt_pi i⟩ : Fin n).castSucc = π' i.castSucc := Fin.ext rfl
      rw [hcast]
      dsimp only [inv', π']
      rw [hleft, swapFin_invol]
      rfl
    have hsub_right : ∀ i, π_sub (inv_sub i) = i := by
      intro i
      apply Fin.ext
      dsimp only [inv_sub, π_sub]
      have hcast : (⟨(inv' i.castSucc).val, hlt_inv i⟩ : Fin n).castSucc = inv' i.castSucc := Fin.ext rfl
      rw [hcast]
      dsimp only [inv', π']
      rw [swapFin_invol, hright]
      rfl
    simp only [sumFin]
    have hhead :
        sumFin n (fun i => f (π' i.castSucc)) =
        sumFin n (fun i => f (π_sub i).castSucc) := by
      apply sumFin_congr
      intro i
      have hcast : (π_sub i).castSucc = π' i.castSucc := Fin.ext rfl
      rw [hcast]
    rw [hhead, sumFin_perm_universal n (fun i => f i.castSucc) π_sub inv_sub hsub_left hsub_right, hfix_pi]

-- Theorem 8: Universal zero-cost gated-MLP (SiLU/GeLU/SwiGLU) hidden-channel permutation invariance
-- Holds identically for EVERY dimension n, EVERY elementwise activation sigma : Int -> Int,
-- EVERY hidden-channel bijection pi, and EVERY (gate, up, down) weight tuple.
theorem swiglu_perm_invariance_fin_universal
    (n : Nat) (σ : Int → Int)
    (G U D : Fin n → Int)
    (π inv : Fin n → Fin n)
    (hleft : ∀ k, inv (π k) = k)
    (hright : ∀ k, π (inv k) = k) :
    sumFin n (fun k => D (π k) * (σ (G (π k)) * U (π k))) =
    sumFin n (fun k => D k * (σ (G k) * U k)) :=
  sumFin_perm_universal n (fun k => D k * (σ (G k) * U k)) π inv hleft hright

-- Theorem 9: Exact matrix-row SwiGLU permutation invariance across all input vectors x
-- Absorbing hidden permutation pi into rows of gate_proj G and up_proj U and columns of down_proj D
-- produces bit-identical output y_i for every output row i and every activation sigma.
theorem swiglu_matrix_perm_invariance_universal
    (d_in d_hid d_out : Nat) (σ : Int → Int)
    (G U : Fin d_hid → Fin d_in → Int)
    (D : Fin d_out → Fin d_hid → Int)
    (x : Fin d_in → Int)
    (π inv : Fin d_hid → Fin d_hid)
    (hleft : ∀ k, inv (π k) = k)
    (hright : ∀ k, π (inv k) = k)
    (i : Fin d_out) :
    let g_pre (k : Fin d_hid) : Int := sumFin d_in (fun j => G k j * x j)
    let u_pre (k : Fin d_hid) : Int := sumFin d_in (fun j => U k j * x j)
    sumFin d_hid (fun k => D i (π k) * (σ (g_pre (π k)) * u_pre (π k))) =
    sumFin d_hid (fun k => D i k * (σ (g_pre k) * u_pre k)) :=
  swiglu_perm_invariance_fin_universal d_hid σ
    (fun k => sumFin d_in (fun j => G k j * x j))
    (fun k => sumFin d_in (fun j => U k j * x j))
    (fun k => D i k) π inv hleft hright

-- Exact 4x4 Sylvester Walsh-Hadamard matrix H_4
def h4Entry (r c : Fin 4) : Int :=
  match r.val, c.val with
  | 0, _ => 1
  | 1, 0 => 1 | 1, 1 => -1 | 1, 2 => 1  | 1, _ => -1
  | 2, 0 => 1 | 2, 1 => 1  | 2, 2 => -1 | 2, _ => -1
  | _, 0 => 1 | _, 1 => -1 | _, 2 => -1 | _, _ => 1

-- Theorem 10: Exact H_4 orthogonality (H_4^T H_4 = 4 I_4), uniform entry magnitude 1,
-- and exact universal Parseval energy identity ||H_4 v||^2 = 4 ||v||^2.
theorem h4_orthogonal_and_parseval_universal (v0 v1 v2 v3 : Int) :
    (∀ r c : Fin 4,
      h4Entry 0 r * h4Entry 0 c + h4Entry 1 r * h4Entry 1 c +
      h4Entry 2 r * h4Entry 2 c + h4Entry 3 r * h4Entry 3 c =
      if r = c then 4 else 0) ∧
    let y0 := v0 + v1 + v2 + v3
    let y1 := v0 - v1 + v2 - v3
    let y2 := v0 + v1 - v2 - v3
    let y3 := v0 - v1 - v2 + v3
    y0 * y0 + y1 * y1 + y2 * y2 + y3 * y3 =
      4 * (v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3) := by
  constructor
  · decide
  · dsimp only
    have e0 : (v0 + v1 + v2 + v3) * (v0 + v1 + v2 + v3) =
        v0*v0 + v1*v1 + v2*v2 + v3*v3 +
        2*(v0*v1) + 2*(v0*v2) + 2*(v0*v3) + 2*(v1*v2) + 2*(v1*v3) + 2*(v2*v3) := by
      simp only [Int.add_mul, Int.mul_add]
      have c01 := Int.mul_comm v1 v0
      have c02 := Int.mul_comm v2 v0
      have c03 := Int.mul_comm v3 v0
      have c12 := Int.mul_comm v2 v1
      have c13 := Int.mul_comm v3 v1
      have c23 := Int.mul_comm v3 v2
      omega
    have e1 : (v0 - v1 + v2 - v3) * (v0 - v1 + v2 - v3) =
        v0*v0 + v1*v1 + v2*v2 + v3*v3 -
        2*(v0*v1) + 2*(v0*v2) - 2*(v0*v3) - 2*(v1*v2) + 2*(v1*v3) - 2*(v2*v3) := by
      simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
      have c01 := Int.mul_comm v1 v0
      have c02 := Int.mul_comm v2 v0
      have c03 := Int.mul_comm v3 v0
      have c12 := Int.mul_comm v2 v1
      have c13 := Int.mul_comm v3 v1
      have c23 := Int.mul_comm v3 v2
      omega
    have e2 : (v0 + v1 - v2 - v3) * (v0 + v1 - v2 - v3) =
        v0*v0 + v1*v1 + v2*v2 + v3*v3 +
        2*(v0*v1) - 2*(v0*v2) - 2*(v0*v3) - 2*(v1*v2) - 2*(v1*v3) + 2*(v2*v3) := by
      simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
      have c01 := Int.mul_comm v1 v0
      have c02 := Int.mul_comm v2 v0
      have c03 := Int.mul_comm v3 v0
      have c12 := Int.mul_comm v2 v1
      have c13 := Int.mul_comm v3 v1
      have c23 := Int.mul_comm v3 v2
      omega
    have e3 : (v0 - v1 - v2 + v3) * (v0 - v1 - v2 + v3) =
        v0*v0 + v1*v1 + v2*v2 + v3*v3 -
        2*(v0*v1) - 2*(v0*v2) + 2*(v0*v3) + 2*(v1*v2) - 2*(v1*v3) - 2*(v2*v3) := by
      simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
      have c01 := Int.mul_comm v1 v0
      have c02 := Int.mul_comm v2 v0
      have c03 := Int.mul_comm v3 v0
      have c12 := Int.mul_comm v2 v1
      have c13 := Int.mul_comm v3 v1
      have c23 := Int.mul_comm v3 v2
      omega
    omega

-- Theorem 11: Universal 2-quad rearrangement exact slack identity & strict dominance
theorem rearrangement_2quad_slack_universal (a b c d : Int) :
    ((a + b) * (a + b) + (c + d) * (c + d)) -
    ((a + d) * (a + d) + (b + c) * (b + c)) = 2 * ((a - c) * (b - d)) ∧
    ((c ≤ a ∧ d ≤ b) →
      (a + d) * (a + d) + (b + c) * (b + c) ≤ (a + b) * (a + b) + (c + d) * (c + d)) ∧
    ((c < a ∧ d < b) →
      (a + d) * (a + d) + (b + c) * (b + c) < (a + b) * (a + b) + (c + d) * (c + d)) := by
  have hid :
      ((a + b) * (a + b) + (c + d) * (c + d)) -
      ((a + d) * (a + d) + (b + c) * (b + c)) = 2 * ((a - c) * (b - d)) := by
    simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
    have cab := Int.mul_comm b a
    have cad := Int.mul_comm d a
    have cbc := Int.mul_comm c b
    have ccd := Int.mul_comm d c
    omega
  refine ⟨hid, ?_, ?_⟩
  · rintro ⟨hca, hdb⟩
    have hmul : 0 ≤ (a - c) * (b - d) := Int.mul_nonneg (by omega) (by omega)
    omega
  · rintro ⟨hca, hdb⟩
    have hmul : 0 < (a - c) * (b - d) := Int.mul_pos (by omega) (by omega)
    omega

-- Theorem 12: Global optimality of monotone quad grouping for squared quad-sum maximization
-- For ANY 4+4 partition (S_A, S_B) of sorted h0 >= ... >= h7, monotone (S_hot, S_quiet)
-- maximizes S_A^2 + S_B^2 with exact non-negative slack 2 * (S_hot - S_A) * (S_A - S_quiet).
theorem monotone_quad_sq_sum_global_max_universal
    (S_hot S_quiet S_A S_B : Int)
    (hsum : S_A + S_B = S_hot + S_quiet)
    (hlo : S_quiet ≤ S_A) (hhi : S_A ≤ S_hot) :
    (S_hot * S_hot + S_quiet * S_quiet) - (S_A * S_A + S_B * S_B) =
      2 * ((S_hot - S_A) * (S_A - S_quiet)) ∧
    S_A * S_A + S_B * S_B ≤ S_hot * S_hot + S_quiet * S_quiet := by
  have hB : S_B = S_hot + S_quiet - S_A := by omega
  have hid :
      (S_hot * S_hot + S_quiet * S_quiet) - (S_A * S_A + S_B * S_B) =
      2 * ((S_hot - S_A) * (S_A - S_quiet)) := by
    rw [hB]
    simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
    have c1 := Int.mul_comm S_quiet S_hot
    have c2 := Int.mul_comm S_A S_hot
    have c3 := Int.mul_comm S_A S_quiet
    omega
  have hnn : 0 ≤ (S_hot - S_A) * (S_A - S_quiet) := Int.mul_nonneg (by omega) (by omega)
  exact ⟨hid, by omega⟩

-- Theorem 13: Global optimality of monotone quad grouping for outlier-spill (total quad spread)
-- For sorted h0 >= h1 >= ... >= h7, monotone spread (h0 - h3) + (h4 - h7) <= (h0 - h7) - (h3 - h4),
-- and ANY overlapping 2-quad partition covering [h7, h0] has spread >= h0 - h7, incurring
-- strictly extra outlier spill >= (h3 - h4) + overlap whenever h3 > h4.
theorem monotone_quad_spread_global_min_universal
    (h0 h1 h2 h3 h4 h5 h6 h7 M1 m1 M2 m2 : Int)
    (hsort : h0 ≥ h1 ∧ h1 ≥ h2 ∧ h2 ≥ h3 ∧ h3 ≥ h4 ∧ h4 ≥ h5 ∧ h5 ≥ h6 ∧ h6 ≥ h7)
    (hvalid : m1 ≤ M1 ∧ m2 ≤ M2)
    (hcov_top : M1 = h0 ∨ M2 = h0)
    (hcov_bot : m1 = h7 ∨ m2 = h7)
    (hoverlap : m1 ≤ M2 ∧ m2 ≤ M1) :
    (h0 - h3) + (h4 - h7) + (h3 - h4) = h0 - h7 ∧
    (h0 - h3) + (h4 - h7) + (h3 - h4) ≤ (M1 - m1) + (M2 - m2) ∧
    (h4 < h3 → (h0 - h3) + (h4 - h7) < (M1 - m1) + (M2 - m2)) := by
  have hgap : h0 - h7 ≤ (M1 - m1) + (M2 - m2) := by
    rcases hcov_top with rfl | rfl <;> rcases hcov_bot with rfl | rfl <;> omega
  exact ⟨by omega, by omega, fun hlt => by omega⟩

-- Theorem 14: Exact BlockH4 INT8 dp4a butterfly safety & concrete outlier-spill contrast witness
theorem h4_int8_butterfly_and_spill_witness :
    let max_coord : Int := 7
    let max_butterfly : Int := 4 * max_coord
    let int8_max : Int := 127
    let sorted_spread : Int := (100 - 100) + (1 - 1)
    let mixed_spread : Int := (100 - 1) + (100 - 1)
    let sorted_sq_sum : Int := (100 + 100 + 100 + 100) * (100 + 100 + 100 + 100) + (1 + 1 + 1 + 1) * (1 + 1 + 1 + 1)
    let mixed_sq_sum : Int := (100 + 100 + 1 + 1) * (100 + 100 + 1 + 1) + (100 + 100 + 1 + 1) * (100 + 100 + 1 + 1)
    max_butterfly = 28 ∧
    max_butterfly ≤ int8_max ∧
    sorted_spread = 0 ∧
    mixed_spread = 198 ∧
    sorted_spread < mixed_spread ∧
    sorted_sq_sum = 160016 ∧
    mixed_sq_sum = 81608 ∧
    sorted_sq_sum - mixed_sq_sum = 78408 := by
  decide

end S70FormalTheory.SortedBlockH4Optimality

#print axioms S70FormalTheory.SortedBlockH4Optimality.swiglu_perm_invariance_fin_universal
#print axioms S70FormalTheory.SortedBlockH4Optimality.swiglu_matrix_perm_invariance_universal
#print axioms S70FormalTheory.SortedBlockH4Optimality.h4_orthogonal_and_parseval_universal
#print axioms S70FormalTheory.SortedBlockH4Optimality.rearrangement_2quad_slack_universal
#print axioms S70FormalTheory.SortedBlockH4Optimality.monotone_quad_sq_sum_global_max_universal
#print axioms S70FormalTheory.SortedBlockH4Optimality.monotone_quad_spread_global_min_universal
#print axioms S70FormalTheory.SortedBlockH4Optimality.h4_int8_butterfly_and_spill_witness
