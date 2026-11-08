module

import all Init.Data.ByteArray.Basic
import all Init.Data.ByteArray.Extra
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2
public import Verif.Init.Data.Nat.Big.Algo

/-! Correctness of decimal conversion. -/

namespace Nat.Big


/-! ## Correctness of parsing -/

/-- The value of the decimal digits among the first `k` bytes of `b`. -/
@[expose] public def decVal (b : ByteArray) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if ('0'.toUInt8 ≤ b[k]! && b[k]! ≤ '9'.toUInt8) = true then decVal b k * 10 + (b[k]!.toNat - 48)
    else decVal b k

public theorem decVal_lt (b : ByteArray) (k : Nat) : decVal b k < 10 ^ k := by
  induction k with
  | zero => simp [decVal]
  | succ k ih =>
    simp only [decVal]
    split
    · next h =>
      have : b[k]!.toNat ≤ 57 := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact UInt8.le_iff_toNat_le.mp h.2
      rw [Nat.pow_succ]; omega
    · rw [Nat.pow_succ]; omega

public theorem pow10_spec (n acc : UInt32) (h : acc.toNat * 10 ^ n.toNat < 2 ^ 32) :
    (pow10 n acc).toNat = acc.toNat * 10 ^ n.toNat := by
  fun_induction pow10 n acc with
  | case1 acc => simp
  | case2 n acc h0 ih =>
    have hn : n.toNat ≠ 0 := fun h' => h0 (UInt32.toNat_inj.mp (by simpa using h'))
    have hn1 : (n - 1).toNat = n.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; simp
    have hpow : 10 ^ n.toNat = 10 * 10 ^ (n.toNat - 1) := by
      have e : n.toNat = (n.toNat - 1) + 1 := by omega
      conv => lhs; rw [e]
      rw [Nat.pow_succ, Nat.mul_comm]
    have hacc : (acc * 10).toNat = acc.toNat * 10 := by
      rw [UInt32.toNat_mul]
      have : acc.toNat * 10 ≤ acc.toNat * 10 ^ n.toNat := by
        rw [hpow]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
      exact Nat.mod_eq_of_lt (by simp; omega)
    rw [ih (by rw [hacc, hn1, Nat.mul_assoc, ← hpow]; exact h), hacc, hn1, Nat.mul_assoc, ← hpow]

/-- The loop invariant: the digits so far are `acc` followed by the `ndig` digits of `chunk`. -/
public structure DecimalState.Inv (st : DecimalState) (v : Nat) : Prop where
  val : st.acc.val * 10 ^ st.ndig.toNat + st.chunk.toNat = v
  ndig : st.ndig.toNat < 9
  chunk : st.chunk.toNat < 10 ^ st.ndig.toNat
  norm : st.acc.IsNorm

public theorem ofDecimalStep_spec (st : DecimalState) (b : ByteArray) (k : Nat) (hst : st.Inv (decVal b k))
    (hfit : (k + 2) * 4 ≤ maxBytes) :
    (ofDecimalStep st b[k]!).Inv (decVal b (k + 1)) := by
  obtain ⟨hv, hn, hc, ha⟩ := hst
  have hacc : st.acc.val ≤ decVal b k := by
    rw [← hv]; exact Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
      (Nat.le_add_right _ _)
  unfold ofDecimalStep
  simp only [decVal]
  split
  · next hd =>
    have hd' := hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd'
    have h48 : 48 ≤ b[k]!.toNat := UInt8.le_iff_toNat_le.mp hd'.1
    have h57 : b[k]!.toNat ≤ 57 := UInt8.le_iff_toNat_le.mp hd'.2
    have hc8 : st.chunk.toNat < 10 ^ 8 := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega))
    have hch : (st.chunk * 10 + (b[k]! - '0'.toUInt8).toUInt32).toNat =
        st.chunk.toNat * 10 + (b[k]!.toNat - 48) := by
      have e : (b[k]! - '0'.toUInt8).toNat = b[k]!.toNat - 48 := by
        rw [UInt8.toNat_sub_of_le _ _ hd'.1]; rfl
      rw [UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, e]
      simp only [show (10 : UInt32).toNat = 10 from rfl]
      have : (10 : Nat) ^ 8 = 100000000 := rfl
      rw [Nat.mod_eq_of_lt (show st.chunk.toNat * 10 < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega)]
    split
    · next h9 =>
      have h9' : st.ndig.toNat = 8 := by
        have := congrArg UInt32.toNat (beq_iff_eq.mp h9)
        rw [UInt32.toNat_add] at this; simp at this; omega
      have hsz : st.acc.n ≤ k := st.acc.n_le_of_val_lt ha k (Nat.lt_of_le_of_lt hacc
        (Nat.lt_of_lt_of_le (decVal_lt b k) (by
          rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) k)))
      obtain ⟨v, nm⟩ := val_mulAddSmall st.acc 1000000000 (st.chunk * 10 + (b[k]! - '0'.toUInt8).toUInt32)
        (by omega)
      refine ⟨?_, by simp, by simp, nm⟩
      simp only [UInt32.toNat_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
      rw [v, hch, ← hv, h9']
      simp only [show (1000000000 : UInt32).toNat = 1000000000 from rfl]
      omega
    · next h9 =>
      have h9' : st.ndig.toNat + 1 ≠ 9 := fun h' => h9 (beq_iff_eq.mpr (UInt32.toNat_inj.mp (by
        rw [UInt32.toNat_add]; simp; omega)))
      have hn1 : (st.ndig + 1).toNat = st.ndig.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
      refine ⟨?_, by simp only [hn1]; omega, ?_, ha⟩
      · simp only [hn1, hch, Nat.pow_succ]
        rw [← hv]; grind
      · simp only [hn1, hch, Nat.pow_succ]; omega
  · exact ⟨hv, hn, hc, ha⟩

public theorem ofDecimalLoop_spec (b : ByteArray) (hfit : (b.size + 2) * 4 ≤ maxBytes) (i : Nat)
    (st : DecimalState) (hi : i ≤ b.size) (hst : st.Inv (decVal b i)) :
    (ofDecimalLoop b i st).Inv (decVal b b.size) := by
  fun_induction ofDecimalLoop b i st with
  | case1 i st h ih =>
    refine ih (by omega) ?_
    rw [← getElem!_pos b i h]
    exact ofDecimalStep_spec st b i hst (by omega)
  | case2 i st h => rw [show i = b.size by omega] at hst; exact hst

/-- `ofDecimal` computes the value of the decimal digits of `s`. -/
public theorem ofDecimal_spec (s : String) (hfit : (s.toUTF8.size + 2) * 4 ≤ maxBytes) :
    (ofDecimal s).val = decVal s.toUTF8 s.toUTF8.size ∧ (ofDecimal s).IsNorm := by
  unfold ofDecimal
  dsimp only
  obtain ⟨hv, hn, hc, ha⟩ := ofDecimalLoop_spec s.toUTF8 hfit 0 ⟨Mag.empty, 0, 0⟩ (Nat.zero_le _)
    ⟨by simp [decVal], by simp, by simp, Mag.isNorm_empty⟩
  generalize ofDecimalLoop s.toUTF8 0 ⟨Mag.empty, 0, 0⟩ = st at hv hn hc ha ⊢
  have hacc : st.acc.val ≤ decVal s.toUTF8 s.toUTF8.size := by
    rw [← hv]; exact Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
      (Nat.le_add_right _ _)
  have hsz : st.acc.n ≤ s.toUTF8.size := st.acc.n_le_of_val_lt ha _ (Nat.lt_of_le_of_lt hacc
    (Nat.lt_of_lt_of_le (decVal_lt _ _) (by rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) _)))
  have hp : (pow10 st.ndig 1).toNat = 10 ^ st.ndig.toNat := by
    rw [pow10_spec _ _ (by
      simp only [UInt32.toNat_one, Nat.one_mul]
      exact Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hn) (by decide))]
    simp
  obtain ⟨v, nm⟩ := val_mulAddSmall st.acc (pow10 st.ndig 1) st.chunk (by omega)
  exact ⟨by rw [v, hp, hv], nm⟩


/-! ## Correctness of printing -/

public theorem toNat_natToUInt32 (n : Nat) (h : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  show (UInt32.ofNat n).toNat = n
  rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

public theorem back!_eq_getLast {α} [Inhabited α] (arr : Array α) (h : arr.toList ≠ []) :
    arr.back! = arr.toList.getLast h := by
  rcases arr with ⟨l⟩
  have hl : 0 < l.length := List.length_pos_iff.mpr h
  simp only [Array.back!, List.getLast_eq_getElem] at *
  rw [getElem!_pos ({ toList := l } : Array α) _ (by simp; omega)]
  simp

/-- The base-`10^9` digits of `n`, least significant first. -/
@[expose] public def chunkList (n : Nat) : List UInt32 :=
  if h : n = 0 then [] else (n % 1000000000).toUInt32 :: chunkList (n / 1000000000)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

public theorem chunksLoop_spec (j : Nat) : ∀ (fuel : Nat) (a : Mag) (acc : Array UInt32), a.IsNorm →
    a.val < 2 ^ (29 * j) → j ≤ fuel → (chunksLoop fuel a acc).toList = acc.toList ++ chunkList a.val := by
  induction j with
  | zero =>
    intro fuel a acc ha hlt _
    have hv : a.val = 0 := by simpa using hlt
    have hc : chunkList a.val = [] := by rw [hv, chunkList]; simp
    rw [hc, List.append_nil]
    rcases fuel with _ | f
    · rfl
    · have : a.usize = 0 := by
        have := a.n_le_of_val_lt ha 0 (by rw [hv]; decide)
        exact USize.toNat_inj.mp (by rw [a.usize_toNat]; simp; omega)
      simp [chunksLoop, this]
  | succ j ih =>
    intro fuel a acc ha hlt hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [chunksLoop]
    split
    · next h =>
      have : a.n = 0 := by have := a.usize_toNat; rw [beq_iff_eq.mp h] at this; simpa using this.symm
      have hv : a.val = 0 := by rw [Mag.val, this]; rfl
      rw [hv, chunkList]; simp
    · next h =>
      have hn : 0 < a.n := by
        have : a.usize.toNat ≠ 0 := fun h' => h (beq_iff_eq.mpr (USize.toNat_inj.mp (by simpa using h')))
        rw [a.usize_toNat] at this; omega
      have hpos : a.val ≠ 0 := by
        have := a.pow_le_val ha hn; have := Nat.two_pow_pos (32 * (a.n - 1)); omega
      obtain ⟨hq, hr, hqn⟩ := val_divModSmall a 1000000000 (by decide)
      simp only [show (1000000000 : UInt32).toNat = 1000000000 from rfl] at hq hr
      have hql : (divModSmall a 1000000000).1.val < 2 ^ (29 * j) := by
        rw [hq, Nat.div_lt_iff_lt_mul (by decide)]
        have : 2 ^ (29 * (j + 1)) = 2 ^ (29 * j) * 2 ^ 29 := by
          rw [← Nat.pow_add, Nat.mul_succ]
        have : 2 ^ (29 * j) * 2 ^ 29 ≤ 2 ^ (29 * j) * 1000000000 := Nat.mul_le_mul_left _ (by decide)
        omega
      rw [ih f _ _ hqn hql (by omega), Array.toList_push, List.append_assoc,
        chunkList.eq_def a.val, dite_eq_right hpos, hq, List.singleton_append]
      congr 2
      apply UInt32.toNat_inj.mp
      rw [hr, toNat_natToUInt32 _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

/-- The last `k` decimal digits of `r`, zero-padded. -/
@[expose] public def padDigits : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, r => padDigits k (r / 10) ++ [(r % 10).digitChar]

public theorem toDigits_mul_add (q : Nat) (hq : 0 < q) (k r : Nat) (hr : r < 10 ^ k) :
    Nat.toDigits 10 (q * 10 ^ k + r) = Nat.toDigits 10 q ++ padDigits k r := by
  induction k generalizing r with
  | zero => simp at hr; subst hr; simp [padDigits]
  | succ k ih =>
    have hge : 10 ≤ q * 10 ^ (k + 1) + r := by
      have : 10 ≤ 10 ^ (k + 1) := by
        rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
      have : 10 ^ (k + 1) ≤ q * 10 ^ (k + 1) := Nat.le_mul_of_pos_left _ hq
      omega
    rw [Nat.toDigits_eq_ite (by decide), ite_eq_right (by omega), padDigits]
    have hd : (q * 10 ^ (k + 1) + r) / 10 = q * 10 ^ k + r / 10 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide),
        Nat.add_comm]
    have hm : (q * 10 ^ (k + 1) + r) % 10 = r % 10 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [hd, hm, ih (r / 10) (by rw [Nat.pow_succ] at hr; omega), List.append_assoc]

public theorem padDigits_zero (k : Nat) : padDigits k 0 = List.replicate k '0' := by
  induction k with
  | zero => rfl
  | succ k ih => rw [padDigits, Nat.zero_div, ih, Nat.zero_mod, List.replicate_succ']; simp

public theorem padDigits_eq (k : Nat) (hk : 0 < k) (r : Nat) (hr : r < 10 ^ k) :
    padDigits k r = List.replicate (k - (Nat.toDigits 10 r).length) '0' ++ Nat.toDigits 10 r := by
  induction k generalizing r with
  | zero => omega
  | succ k ih =>
    rw [padDigits]
    by_cases h10 : 10 ≤ r
    · have hk' : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at hr; omega
        · exact h
      rw [ih hk' (r / 10) (by rw [Nat.pow_succ] at hr; omega),
        Nat.toDigits_eq_ite (n := r) (by decide), ite_eq_right (by omega), List.length_append,
        List.length_singleton, List.append_assoc]
      congr 2
      omega
    · rw [show r / 10 = 0 by omega, padDigits_zero, Nat.toDigits_of_lt_base (by omega),
        show r % 10 = r by omega]
      simp

public theorem toList_toString_uint32 (c : UInt32) : (toString c).toList = Nat.toDigits 10 c.toNat := by
  show (toString c.toNat).toList = _
  rw [Nat.toString_eq_repr, Nat.toList_repr]

public theorem toList_pushn (s : String) (c : Char) (n : Nat) :
    (s.pushn c n).toList = s.toList ++ List.replicate n c := by
  induction n with
  | zero => rw [String.pushn_eq_repeat_push]; simp [Nat.repeat]
  | succ n ih =>
    rw [String.pushn_eq_repeat_push] at *
    rw [Nat.repeat, String.toList_push, ih, List.replicate_succ', List.append_assoc]

/-- The digits of the chunks, most significant chunk first, padding all but the top one. -/
@[expose] public def renderChunks : List UInt32 → List Char
  | [] => []
  | [c] => Nat.toDigits 10 c.toNat
  | c :: rest => renderChunks rest ++ padDigits 9 c.toNat

public theorem renderChunks_chunkList (n : Nat) (hn : 0 < n) :
    renderChunks (chunkList n) = Nat.toDigits 10 n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [chunkList.eq_def, dite_eq_right (by omega)]
    have hr : ((n % 1000000000).toUInt32).toNat = n % 1000000000 := by
      exact toNat_natToUInt32 _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    by_cases hq : n / 1000000000 = 0
    · rw [hq, chunkList.eq_def, dite_eq_left rfl, renderChunks, hr, Nat.mod_eq_of_lt (by omega)]
    · have hq' : 0 < n / 1000000000 := Nat.pos_of_ne_zero hq
      have hne : chunkList (n / 1000000000) ≠ [] := by
        rw [chunkList.eq_def, dite_eq_right hq]; simp
      obtain ⟨c, rest, hcr⟩ : ∃ c rest, chunkList (n / 1000000000) = c :: rest :=
        match h : chunkList (n / 1000000000), hne with
        | c :: rest, _ => ⟨c, rest, rfl⟩
      rw [hcr, renderChunks.eq_3 _ _ (by simp), ← hcr, ih _ (Nat.div_lt_self (by omega) (by decide)) hq', hr]
      conv => rhs; rw [← Nat.div_add_mod n 1000000000]
      rw [Nat.mul_comm, show (1000000000 : Nat) = 10 ^ 9 from rfl,
        toDigits_mul_add _ hq' 9 _ (Nat.mod_lt _ (by decide))]

public theorem foldr_render (L : List UInt32) (hL : L ≠ []) :
    List.foldr (fun c s => s ++ padDigits 9 c.toNat) (Nat.toDigits 10 (L.getLast hL).toNat)
      L.dropLast = renderChunks L := by
  induction L with
  | nil => contradiction
  | cons c rest ih =>
    rcases rest with _ | ⟨d, rest⟩
    · simp [renderChunks]
    · rw [List.dropLast_cons_cons, List.foldr_cons, List.getLast_cons (by simp),
        ih (by simp)]
      exact (renderChunks.eq_3 c (d :: rest) (by simp)).symm

public theorem padDigits_chunk (c : UInt32) (hc : c.toNat < 10 ^ 9) :
    ("".pushn '0' (9 - (toString c).length) ++ toString c).toList = padDigits 9 c.toNat := by
  rw [String.toList_append, toList_pushn, ← String.length_toList, toList_toString_uint32,
    padDigits_eq 9 (by decide) _ hc]
  simp

public theorem chunkList_lt (n : Nat) : ∀ c ∈ chunkList n, c.toNat < 10 ^ 9 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro c hc
    rw [chunkList.eq_def] at hc
    split at hc
    · simp at hc
    · rcases List.mem_cons.mp hc with h | h
      · subst h
        rw [toNat_natToUInt32 _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
        exact Nat.mod_lt _ (by decide)
      · exact ih _ (Nat.div_lt_self (by omega) (by decide)) c h

public theorem foldr_string (L : List UInt32) (hL : ∀ c ∈ L, c.toNat < 10 ^ 9) (top : UInt32) :
    (List.foldr (fun c s => s ++ "".pushn '0' (9 - (toString c).length) ++ toString c)
      (toString top) L).toList =
    List.foldr (fun c s => s ++ padDigits 9 c.toNat) (Nat.toDigits 10 top.toNat) L := by
  induction L with
  | nil => exact toList_toString_uint32 top
  | cons c rest ih =>
    rw [List.foldr_cons, List.foldr_cons, String.append_assoc, String.toList_append,
      padDigits_chunk c (hL c (by simp)), ih (fun d hd => hL d (by simp [hd]))]

/-- `toDecimal` produces the decimal representation, as `toString` does on `Nat`. -/
public theorem toDecimal_spec (a : Mag) (ha : a.IsNorm) : (toDecimal a).toList = Nat.toDigits 10 a.val := by
  unfold toDecimal
  have hc := chunksLoop_spec (2 * a.n) (2 * a.n) a #[] ha
    (Nat.lt_of_lt_of_le a.val_lt (Nat.pow_le_pow_right (by decide) (by omega))) (Nat.le_refl _)
  rw [List.nil_append] at hc
  dsimp only
  generalize chunksLoop (2 * a.n) a #[] = arr at hc ⊢
  split
  · next h =>
    have : chunkList a.val = [] := by rw [← hc]; simpa using h
    have h0 : a.val = 0 := by
      rw [chunkList.eq_def] at this; split at this
      · assumption
      · simp at this
    rw [h0, Nat.toDigits_zero]; rfl
  · next h =>
    have hne : arr.toList ≠ [] := by simpa using h
    have hpos : 0 < a.val := by
      rcases Nat.eq_zero_or_pos a.val with h0 | h0
      · rw [h0, chunkList.eq_def, dite_eq_left rfl] at hc; exact absurd hc hne
      · exact h0
    rw [← Array.foldr_toList, Array.toList_pop, back!_eq_getLast arr hne]
    rw [← renderChunks_chunkList _ hpos, ← hc, ← foldr_render _ hne]
    exact foldr_string _ (fun c h => chunkList_lt a.val c (hc ▸ List.dropLast_subset _ h)) _

end Nat.Big
