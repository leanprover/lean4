/-!
Linear integer arithmetic goals from real proofs: each goal was closed by Rocq's `lia` in
[theorem-labs/oss-verify-proofs](https://github.com/theorem-labs/oss-verify-proofs)
(release 2026.10.0, commit `98e995d`), Rocq proofs about OSS-Fuzz harnesses compiled to RISC-V.

A goal is an `assert (H : P) by lia` fact, the side condition of `replace a with b by lia`, or a
lemma proved by `lia` alone, together with the arithmetic hypotheses that are visible in the source
before it. Subterms that `lia` does not interpret (memory accessors, bit-vector conversions,
non-literal powers) are universally quantified symbols over opaque types. Rocq's `Z.div` and
`Z.modulo` floor, so they become `Int.fdiv` and `Int.fmod`, or `/` and `%` when the divisor is a
positive literal. Each goal was checked again by Rocq's `lia` in this abstracted form.

Part 1 of 4. `lia_oss_verify_failing.lean` has the goals that `lia` does not prove yet.
-/

set_option linter.unusedVariables false

-- boost-beast/http_request: lib/As/AsMainFacts.v (assert)
example
    (sp0z : Int)
    (v0 : Int)
    (q : Int)
    (w : Int)
    (cls : Nat)
    (qlo : Nat → Int)
    (qhi : Nat → Int)
    (wlo : Nat → Int)
    (whi : Nat → Int)
    (h1 : sp0z = (((32768 * v0) + (4096 * q)) + (16 * w)))
    (h2 : ((qlo cls) ≤ q ∧ q ≤ (qhi cls)))
    (h3 : ((wlo cls) ≤ w ∧ w ≤ (whi cls)))
    (h4 : cls ≤ 1) :
    (cls = 0 ∨ cls = 1) := by
  lia

-- boost-beast/http_request: lib/Bo/AS_InstLaws3.v (assert)
example
    (i : Int)
    (h1 : (i = 0 ∨ (i = 1 ∨ (i = 2 ∨ (i = 3 ∨ (i = 4 ∨ (i = 5 ∨ (i = 6 ∨ i = 7)))))))) :
    (i = 0 ∨ (i = 1 ∨ (i = 2 ∨ (i = 3 ∨ (i = 4 ∨ (i = 5 ∨ (i = 6 ∨ i = 7))))))) := by
  lia

-- boost-beast/http_request: lib/Bo/AXPRep2.v (replace)
example
    {T1 : Type}
    (it0 : Int)
    (bs : T1)
    (q : Int)
    (length : T1 → Nat)
    (h1 : (it0 ≤ q ∧ q ≤ (it0 + (((length bs) : Nat) : Int)))) :
    q = (it0 + (((Int.toNat (q - it0)) : Nat) : Int)) := by
  lia

-- boost-beast/http_request: lib/Bo/AllocTacX.v (lemma)
example
    (l : Int)
    (h_1 : Int)
    (l' : Int)
    (h' : Int)
    (x : Int)
    (h1 : l' ≤ l)
    (h2 : h_1 ≤ h')
    (h3 : (¬ (l' ≤ x ∧ x < h'))) :
    (¬ (l ≤ x ∧ x < h_1)) := by
  lia

-- boost-beast/http_request: lib/Bo/X8_F_insert.v (replace)
example {T1 : Type} (name : T1) (tv : T1) (length : T1 → Nat) :
    (((((length name) : Nat) : Int) + (((length tv) : Nat) : Int)) + 67) = ((((((length name) : Nat) : Int) + 2) + (((length tv) : Nat) : Int)) + 65) := by
  lia

-- boost-beast/http_request: lib/Common/LimSim/LimSimMv.v (replace)
example
    {T1 : Type}
    (kd : Int)
    (page_size : Int)
    (bv_unsigned : T1 → Int)
    (new_n : T1)
    (nnz : Int)
    (dlo : Int)
    (kn : Int)
    (h1 : (bv_unsigned new_n) = nnz)
    (h2 : dlo = (kd * page_size))
    (h3 : nnz = (kn * page_size))
    (h4 : (Int.fdiv ((dlo + page_size) - 1) page_size) = kd) :
    ((kd * page_size) + (page_size - 1)) = (((kd * page_size) + page_size) - 1) := by
  lia

-- boost-beast/http_request: lib/Ref/XP_ftab.v (replace)
example (i : Int) (G_FIELD_TABLE : Int) (h1 : (0 ≤ i ∧ i < 130)) :
    (G_FIELD_TABLE + (8 * (((2 * (Int.toNat i)) : Nat) : Int))) = (G_FIELD_TABLE + (16 * i)) := by
  lia

-- boost-beast/http_request: lib/Ref/XP_ftab.v (replace)
example (i : Int) (G_FIELD_TABLE : Int) (h1 : (0 ≤ i ∧ i < 130)) :
    (G_FIELD_TABLE + (8 * ((((2 * (Int.toNat i)) + 1) : Nat) : Int))) = ((G_FIELD_TABLE + (16 * i)) + 8) := by
  lia

-- boost-beast/http_request: lib/Ref/XP_ftab_rep.v (replace)
example (i : Nat) (h1 : (1 ≤ i ∧ i ≤ 129)) :
    (i - 1) = (i - 1) := by
  lia

-- boost-beast/http_request: lib/Spec/MI_WCreate.v (replace)
example
    {mstate aptr meta_1 T4 : Type}
    (st' : mstate)
    (p : aptr)
    (ai : Int)
    (mr' : meta_1)
    (snd : aptr → Int)
    (b : aptr)
    (m_freeable : meta_1 → Int)
    (m_maplen : meta_1 → Int)
    (last' : Int)
    (sc' : Int)
    (m_avail : meta_1 → Int)
    (m_freed : meta_1 → Int)
    (stride' : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (cnt : Int)
    (s_ctx : mstate → T4)
    (c_mmap_counter : T4 → Int)
    (i : Int)
    (h1 : (m_freeable mr') = 1)
    (h2 : 0 ≤ (m_maplen mr'))
    (h3 : (0 ≤ last' ∧ last' ≤ 31))
    (h4 : (0 ≤ ai ∧ ai ≤ last'))
    (h5 : (sc' = 0 → ai = last'))
    (h6 : (((0 ≤ sc' ∧ sc' < 48) ∧ (m_maplen mr') ≤ 256) ∨ (sc' = 63 ∧ (last' = 0 ∧ (m_maplen mr') ≠ 0))))
    (h7 : (sc' < 48 → ((stride' ≤ (UNIT * (size_class sc')) ∨ 28 ≤ sc') ∧ ((last' = 0 → ((m_maplen mr') ≠ 0 ∧ 27 ≤ sc')) ∧ (stride' * cnt) < (2 ^ (20 : Nat))))))
    (h8 : (16 ≤ stride' ∧ (stride' % 16) = 0))
    (h9 : (0 ≤ (snd p) ∧ (Int.fmod (snd p) UNIT) = 0))
    (h10 : (sc' = 63 → ((m_avail mr') = 0 ∧ (m_freed mr') = 0)))
    (h11 : (0 ≤ (c_mmap_counter (s_ctx st')) ∧ (c_mmap_counter (s_ctx st')) < (2 ^ (32 : Nat))))
    (h12 : (stride' * 1) ≤ (stride' * i)) :
    ((snd b) + (15 - 16)) = ((snd b) - 1) := by
  lia

-- boost-beast/http_request: lib/Spec/MI_WCreate2.v (replace)
example (ml : Int) :
    (((ml * 256) - 1) * 16) = ((ml * 4096) - 16) := by
  lia

-- boost-beast/http_request: lib/Ub/CXXLib.v (lemma)
example (n : Int) (h1 : (0 ≤ n ∧ n ≤ 22)) :
    (0 ≤ (2 * n) ∧ (2 * n) < 256) := by
  lia

-- boost-beast/http_request: lib/Ub/RF_malloc_big.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (L : Int)
    (bv_unsigned : T1 → Int)
    (sp' : T1)
    (sp : T1)
    (st2 : Nat)
    (fst : T2 → Nat)
    (new_region : T3 → Int → Int → Nat → T2)
    (RKGroup : T3)
    (xa : Int)
    (n : Int)
    (IB : Int)
    (UNIT : Int)
    (st1 : Nat)
    (round_up_pg : Int → Int)
    (mmap_len : Int → Int)
    (Some : T4 → T5)
    (ranges_free : T6 → Int → Int → Bool)
    (ref_reserved : T6)
    (rid : Nat)
    (step_seq : Nat → Nat)
    (st3 : Nat)
    (pw : Nat → T5 → T1)
    (g : T4)
    (G : Int)
    (get_stride : T7 → Int)
    (big_meta : Nat → Int → T7)
    (q2 : Nat)
    (q : Nat)
    (s_next_rid : Nat → Nat)
    (big_ml : Int → Int)
    (h1 : (bv_unsigned sp') = ((bv_unsigned sp) + (-48)))
    (h2 : st2 = (fst (new_region RKGroup xa ((n + IB) + UNIT) st1)))
    (h3 : L = (round_up_pg ((n + IB) + UNIT)))
    (h4 : (mmap_len ((n + IB) + UNIT)) = L)
    (h5 : ((xa + L) ≤ 65536 ∨ 753664 ≤ xa))
    (h6 : (ranges_free ref_reserved xa L) = true)
    (h7 : (bv_unsigned (pw st3 (Some g))) = G)
    (h8 : (get_stride (big_meta rid n)) = (L - 16))
    (h9 : q2 ≠ q)
    (h10 : q ≠ rid)
    (h11 : (s_next_rid (step_seq st2)) = (rid + 1))
    (h12 : (32 ≤ (big_ml n) ∧ (big_ml n) < (2 ^ (40 : Nat))))
    (h13 : L ≤ (n + 4115)) :
    16 = ((0 + 16) + ((L - 16) * 0)) := by
  lia

-- boost-beast/http_request: lib/Ub/RMallocKit_B3.v (replace)
example
    {T1 T2 : Type}
    (o : Int)
    (snd : T1 → Int)
    (p : T1)
    (length : T2 → Nat)
    (bs : T2)
    (b : T1)
    (h1 : (((length bs) : Nat) : Int) = 8)
    (h2 : (snd b) ≠ (snd p))
    (h3 : (o < (snd p) ∨ ((snd p) + 8) ≤ o)) :
    o = ((snd p) + (o - (snd p))) := by
  lia

-- boost-beast/http_request: lib/Ub/XP_isl2.v (replace)
example
    {T1 : Type}
    (p0 : Int)
    (bs : T1)
    (a : Int)
    (n : Int)
    (length : T1 → Nat)
    (h1 : 0 ≤ a)
    (h2 : 0 ≤ n)
    (h3 : (a + n) ≤ (((length bs) : Nat) : Int)) :
    (Int.toNat a) = (Int.toNat ((p0 + a) - p0)) := by
  lia

-- boost-json/fuzz_parse: lib/As/AllocKit.v (replace)
example {T1 : Type} (off : Int) (c : Int) (as_space_beg : T1 → Int) (st : T1) :
    (off + (c * (2 ^ (32 : Nat)))) = ((((as_space_beg st) + (c * (2 ^ (32 : Nat)))) + off) - (as_space_beg st)) := by
  lia

-- boost-json/fuzz_parse: lib/AsMainIfaceArgs.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 : Type}
    (x : Int)
    (estart : T1 → T2 → Int)
    (E : T1)
    (SA : T3 → T4 → T2)
    (fst : T5 → T3)
    (e_atrb : T5)
    (snd : T5 → T4)
    (bv_unsigned : T6 → Int)
    (sp0 : T6)
    (length : T7 → Nat)
    (build_stack_bytes : T8 → T6 → T9 → T10 → T11 → T12 → T13 → T7)
    (APH : T8)
    (in_argv : T14 → T9)
    (inp : T14)
    (in_envp : T14 → T10)
    (in_uid : T14 → T11)
    (in_hwcap : T14 → T12)
    (rdraw : T13)
    (h1 : (estart E (SA (fst e_atrb) (snd e_atrb))) = (((bv_unsigned sp0) + (((length (build_stack_bytes APH sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw)) : Nat) : Int)) - 16)) :
    x = ((estart E (SA (fst e_atrb) (snd e_atrb))) + (x - (estart E (SA (fst e_atrb) (snd e_atrb))))) := by
  lia

-- boost-json/fuzz_parse: lib/BJ/BJKitStr.v (replace)
example (chars : Int) (n : Int) (cur : Int) :
    ((((((chars + n) + 23) / 24) + cur) + 1) + ((2 * cur) * (2 ^ (64 : Nat)))) = (((((chars + n) + 23) / 24) + ((3 * cur) * 12297829382473034411)) + 1) := by
  lia

-- boost-json/fuzz_parse: lib/BJ/L_push_null.v (replace)
example (n : Int) :
    (Int.toNat (24 * n)) = ((Int.toNat (24 * n)) + 0) := by
  lia

-- boost-json/fuzz_parse: lib/BJU/W_unum0.v (replace)
example (k : Int) (b : Int) :
    ((k + (2 ^ (31 : Nat))) + (Int.fmod b ((2 ^ (32 : Nat)) * (2 ^ (32 : Nat))))) = (((Int.fmod b ((2 ^ (32 : Nat)) * (2 ^ (32 : Nat)))) + k) + (2 ^ (31 : Nat))) := by
  lia

-- boost-json/fuzz_parse: lib/Bs/AS_SecSum.v (assert)
example
    (P : Int)
    (K : Int)
    (x : Int)
    (Wc : Int)
    (h1 : P ≤ ((32 + K) * x))
    (h2 : (64513 * ((32 + K) * x)) ≤ ((Wc - x) * x))
    (h3 : (4 * ((Wc - x) * x)) ≤ (Wc * Wc))
    (h4 : ((Wc * Wc) - (4 * ((Wc - x) * x))) = ((Wc - (2 * x)) * (Wc - (2 * x))))
    (h5 : (Wc * Wc) ≤ (4834967590 * 4834967590)) :
    (258052 * P) ≤ (4834967590 * 4834967590) := by
  lia

-- boost-json/fuzz_parse: lib/Bs/N6_quick.v (replace)
example {T1 : Type} (sh : T1 → Int) (d : T1) :
    (8 * ((sh d) / 8)) = (((8 * ((sh d) / 8)) + 8) - ((8 : Nat) : Int)) := by
  lia

-- boost-json/fuzz_parse: lib/Bs/N6_quick.v (replace)
example {T1 : Type} (sh : T1 → Int) (d : T1) :
    (8 * ((sh d) / 8)) = (((8 * (((sh d) / 8) + 1)) + 8) - ((16 : Nat) : Int)) := by
  lia

-- boost-json/fuzz_parse: lib/EH/XSegLib.v (replace)
example
    {T1 T2 T3 : Type}
    (n : Int)
    (w : Nat)
    (estart : T1 → T2 → Int)
    (E : T1)
    (SA : T3 → Int → T2)
    (sb : T3)
    (sk : Int)
    (db : T3)
    (dk : Int)
    (h1 : n = 0)
    (h2 : (estart E (SA sb (sk + ((w : Nat) : Int)))) = ((estart E (SA sb sk)) + ((w : Nat) : Int)))
    (h3 : (estart E (SA db (dk + ((w : Nat) : Int)))) = ((estart E (SA db dk)) + ((w : Nat) : Int))) :
    ((Int.toNat n) - w) = (Int.toNat (n - ((w : Nat) : Int))) := by
  lia

-- boost-json/fuzz_parse: lib/RefLayout.v (replace)
example
    {word list_list_byte T3 T4 : Type}
    (sp : word)
    (av : list_list_byte)
    (ev : list_list_byte)
    (k : Nat)
    (length : list_list_byte → Nat)
    (fst : T3 → list_list_byte)
    (string_addrs : T4 → list_list_byte → T3)
    (cat_env_base : word → list_list_byte → list_list_byte → T4)
    (h1 : k < (length ev))
    (h2 : k < (length (fst (string_addrs (cat_env_base sp av ev) ev)))) :
    (8 + ((8 * (length av)) + (8 + (8 * k)))) = ((8 + (8 * ((length av) + 1))) + (8 * k)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/A0_cmp_bsF.v (replace)
example {T1 : Type} (me_n : T1 → Int) (X : T1) :
    (me_n X) = ((me_n X) - 0) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/A0_cmp_msK.v (replace)
example (qsp' : Int) (h1 : qsp' ≤ 51) :
    (qsp' - 1) = (qsp' + (-1)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/A0_cmp_sdB3.v (replace)
example
    {eg est bw T4 T5 T6 T7 T8 : Type}
    (g : eg)
    (e : est)
    (LIM : Int)
    (A : Int)
    (nG : Int)
    (nSel : Int)
    (sc : Int)
    (gs : Int)
    (b : bw)
    (g_mtf : eg → Bool)
    (g_bs : eg → Bool)
    (e_nblock : est → Int)
    (ARR2_SIZE : Int)
    (zget : T4 → Int → Int)
    (ARR1_SIZE : Int)
    (e_arr1 : est → T5)
    (bw_numZ : T6 → Int)
    (sm_put_syms : Int → bw → T7 → T8 → T5 → Int → Int → T6)
    (e_len : est → T7)
    (e_code : est → T8)
    (SELA : T4)
    (h1 : (g_mtf g) = true)
    (h2 : (g_bs g) = true)
    (h3 : 0 ≤ (e_nblock e))
    (h4 : ((e_nblock e) + LIM) ≤ ARR2_SIZE)
    (h5 : (3 ≤ A ∧ A ≤ 258))
    (h6 : (2 ≤ nG ∧ nG ≤ 6))
    (h7 : (1 ≤ nSel ∧ nSel ≤ 18002))
    (h8 : (0 ≤ sc ∧ sc < nSel))
    (h9 : 0 ≤ gs)
    (h10 : (2 * (gs + 50)) ≤ ARR1_SIZE)
    (h11 : (bw_numZ (sm_put_syms 8 b (e_len e) (e_code e) (e_arr1 e) (zget SELA sc) (gs + 17))) ≤ LIM) :
    (gs + 18) = ((gs + 17) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/A0_cmp_sdC2.v (replace)
example
    {eg est bw T4 T5 T6 T7 T8 : Type}
    (g : eg)
    (e : est)
    (LIM : Int)
    (A : Int)
    (nG : Int)
    (nSel : Int)
    (sc : Int)
    (gs : Int)
    (b : bw)
    (g_mtf : eg → Bool)
    (g_bs : eg → Bool)
    (e_nblock : est → Int)
    (ARR2_SIZE : Int)
    (zget : T4 → Int → Int)
    (ARR1_SIZE : Int)
    (e_arr1 : est → T5)
    (bw_numZ : T6 → Int)
    (sm_put_syms : Int → bw → T7 → T8 → T5 → Int → Int → T6)
    (e_len : est → T7)
    (e_code : est → T8)
    (SELA : T4)
    (h1 : (g_mtf g) = true)
    (h2 : (g_bs g) = true)
    (h3 : 0 ≤ (e_nblock e))
    (h4 : ((e_nblock e) + LIM) ≤ ARR2_SIZE)
    (h5 : (3 ≤ A ∧ A ≤ 258))
    (h6 : (2 ≤ nG ∧ nG ≤ 6))
    (h7 : (1 ≤ nSel ∧ nSel ≤ 18002))
    (h8 : (0 ≤ sc ∧ sc < nSel))
    (h9 : 0 ≤ gs)
    (h10 : (2 * (gs + 50)) ≤ ARR1_SIZE)
    (h11 : (bw_numZ (sm_put_syms 50 b (e_len e) (e_code e) (e_arr1 e) (zget SELA sc) gs)) ≤ LIM) :
    (gs + 9) = (gs + (((1 + 8) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/A0_cmp_sdC2.v (replace)
example
    {eg est bw T4 T5 T6 T7 T8 : Type}
    (g : eg)
    (e : est)
    (LIM : Int)
    (A : Int)
    (nG : Int)
    (nSel : Int)
    (sc : Int)
    (gs : Int)
    (b : bw)
    (g_mtf : eg → Bool)
    (g_bs : eg → Bool)
    (e_nblock : est → Int)
    (ARR2_SIZE : Int)
    (zget : T4 → Int → Int)
    (ARR1_SIZE : Int)
    (e_arr1 : est → T5)
    (bw_numZ : T6 → Int)
    (sm_put_syms : Int → bw → T7 → T8 → T5 → Int → Int → T6)
    (e_len : est → T7)
    (e_code : est → T8)
    (SELA : T4)
    (h1 : (g_mtf g) = true)
    (h2 : (g_bs g) = true)
    (h3 : 0 ≤ (e_nblock e))
    (h4 : ((e_nblock e) + LIM) ≤ ARR2_SIZE)
    (h5 : (3 ≤ A ∧ A ≤ 258))
    (h6 : (2 ≤ nG ∧ nG ≤ 6))
    (h7 : (1 ≤ nSel ∧ nSel ≤ 18002))
    (h8 : (0 ≤ sc ∧ sc < nSel))
    (h9 : 0 ≤ gs)
    (h10 : (2 * (gs + 50)) ≤ ARR1_SIZE)
    (h11 : (bw_numZ (sm_put_syms 50 b (e_len e) (e_code e) (e_arr1 e) (zget SELA sc) gs)) ≤ LIM) :
    (gs + 49) = (gs + (((((((((1 + 8) + 8) + 8) + 8) + 8) + 7) + 1) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/A0_cmp_sdC2.v (replace)
example
    {eg est bw T4 T5 T6 T7 T8 : Type}
    (g : eg)
    (e : est)
    (LIM : Int)
    (A : Int)
    (nG : Int)
    (nSel : Int)
    (sc : Int)
    (gs : Int)
    (b : bw)
    (g_mtf : eg → Bool)
    (g_bs : eg → Bool)
    (e_nblock : est → Int)
    (ARR2_SIZE : Int)
    (zget : T4 → Int → Int)
    (ARR1_SIZE : Int)
    (e_arr1 : est → T5)
    (bw_numZ : T6 → Int)
    (sm_put_syms : Int → bw → T7 → T8 → T5 → Int → Int → T6)
    (e_len : est → T7)
    (e_code : est → T8)
    (SELA : T4)
    (h1 : (g_mtf g) = true)
    (h2 : (g_bs g) = true)
    (h3 : 0 ≤ (e_nblock e))
    (h4 : ((e_nblock e) + LIM) ≤ ARR2_SIZE)
    (h5 : (3 ≤ A ∧ A ≤ 258))
    (h6 : (2 ≤ nG ∧ nG ≤ 6))
    (h7 : (1 ≤ nSel ∧ nSel ≤ 18002))
    (h8 : (0 ≤ sc ∧ sc < nSel))
    (h9 : 0 ≤ gs)
    (h10 : (2 * (gs + 50)) ≤ ARR1_SIZE)
    (h11 : (bw_numZ (sm_put_syms 50 b (e_len e) (e_code e) (e_arr1 e) (zget SELA sc) gs)) ≤ LIM) :
    gs = (gs + 0) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/A0_cmp_smBb.v (replace)
example
    {T1 T2 : Type}
    (ge : Int)
    (gs : Int)
    (sm_alpha : T1 → Int)
    (e : T1)
    (e_nInUse : T1 → Int)
    (sm_nmtf : T1 → T2)
    (smA_ng : T1 → Int)
    (fastb : Int → T2 → Int → Bool)
    (h1 : (sm_alpha e) = ((e_nInUse e) + 2))
    (h2 : (smA_ng e) = 6)
    (h3 : (ge - gs) = 49)
    (h4 : (fastb (smA_ng e) (sm_nmtf e) gs) = true)
    (h5 : (fastb (smA_ng e) (sm_nmtf e) gs) = false) :
    ((ge - gs) + 1) = ((ge + 1) - gs) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/A0_cmp_smS.v (replace)
example
    {T1 T2 T3 : Type}
    (P : Int)
    (sm_alpha : T1 → Int)
    (e0 : T1)
    (e_nInUse : T1 → Int)
    (zdef : T2 → Nat → Bool)
    (yy_init : Nat → T3 → Nat → T2)
    (smA_ng : T1 → Int)
    (znew : T3)
    (zget : T2 → Nat → Int)
    (p0 : T3)
    (h1 : (sm_alpha e0) = ((e_nInUse e0) + 2))
    (h2 : (zdef (yy_init (Int.toNat (smA_ng e0)) znew 0) 0) = true)
    (h3 : (zget (yy_init (Int.toNat (smA_ng e0)) znew 0) 0) = 0)
    (h4 : (zget (yy_init (Int.toNat (smA_ng e0)) p0 0) 0) = 0) :
    (P + 1344) = ((P + 1336) + ((8 : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/AsanKit.v (replace)
example
    (X : Int)
    (N_1 : Int)
    (h1 : (X % 8) = 0)
    (h2 : 0 ≤ X)
    (h3 : 0 ≤ N_1)
    (h4 : (X + N_1) ≤ (2 ^ (47 : Nat)))
    (h5 : (((X + (8 * (N_1 / 8))) + 7) / 8) = ((X / 8) + (N_1 / 8)))
    (h6 : X = (8 * (X / 8))) :
    (7 + (((X / 8) + (N_1 / 8)) * 8)) = (((8 * (X / 8)) + (8 * (N_1 / 8))) + 7) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/B0F_dec_U10F.v (replace)
example (mm : Int) :
    ((mm - 4) - 1) = (mm - 5) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/B0F_idx.v (replace)
example
    {word : Type}
    (sp : word)
    (CF : Int)
    (lo : Int)
    (k : Nat)
    (Zpow : Int → Int → Int)
    (mid : Int)
    (nb : Int)
    (bv_unsigned : word → Int)
    (h1 : (lo + 16) ≤ (bv_unsigned sp))
    (h2 : ((bv_unsigned sp) ≤ CF ∨ (CF + 1028) ≤ ((bv_unsigned sp) - 16)))
    (h3 : (CF % 4) = 0)
    (h4 : 6467584 ≤ lo)
    (h5 : 6467584 ≤ CF)
    (h6 : 0 < (Zpow 2 ((k : Nat) : Int)))
    (h7 : mid = (nb + (Zpow 2 ((k : Nat) : Int))))
    (h8 : ((CF + (4 * mid)) % 4) = 0) :
    (Zpow 2 ((k : Nat) : Int)) = (mid - nb) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/B0_cmp_cbG.v (replace)
example
    {T1 T2 : Type}
    (ac_P : T1 → Int)
    (Y : T1)
    (Z_land : Int → Nat → Int)
    (c_A1 : T2 → Int)
    (cx : T2)
    (ac_FB : T1 → Int)
    (CEIL : Int)
    (c_E : T2 → Int)
    (ESTATE_SIZE : Int)
    (ARR1_SIZE : Int)
    (c_A2 : T2 → Int)
    (ARR2_SIZE : Int)
    (h1 : (Z_land (c_A1 cx) 3) = 0)
    (h2 : 0 < (ac_FB Y))
    (h3 : ((ac_FB Y) + 352) ≤ CEIL)
    (h4 : (((ac_FB Y) + 352) ≤ (c_E cx) ∨ ((c_E cx) + ESTATE_SIZE) ≤ (ac_FB Y)))
    (h5 : (((ac_FB Y) + 352) ≤ (c_A1 cx) ∨ ((c_A1 cx) + ARR1_SIZE) ≤ (ac_FB Y)))
    (h6 : (((ac_FB Y) + 352) ≤ (c_A2 cx) ∨ ((c_A2 cx) + ARR2_SIZE) ≤ (ac_FB Y)))
    (h7 : CEIL ≤ (ac_P Y))
    (h8 : ((ac_P Y) + 184) ≤ 18446744073709551616) :
    ((ac_P Y) + 160) = (((ac_P Y) + 80) + 80) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/B0_cmp_msE.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : Type}
    (i : Int)
    (a1 : T1)
    (v1 : T2)
    (snd : T3 → Int)
    (mss_shift : Nat → T1 → T4 → T5 → T6 → T7 → T8 → Int → Int → T2 → T9 → T3)
    (lo : Int)
    (a2 : T4)
    (me_qo : T10 → T5)
    (X : T10)
    (me_n : T10 → T6)
    (d : T7)
    (h_1 : T8)
    (b : T9)
    (a1b : T1)
    (v2 : T2)
    (b1 : T9)
    (a1d : T1)
    (v3 : T2)
    (b2 : T9)
    (h1 : (-2147483648) < (snd (mss_shift ((Int.toNat (i - lo)) + 1) a1 a2 (me_qo X) (me_n X) d h_1 lo i v1 b)))
    (h2 : (-2147483648) < (snd (mss_shift ((Int.toNat ((i + 1) - lo)) + 1) a1b a2 (me_qo X) (me_n X) d h_1 lo (i + 1) v2 b1)))
    (h3 : (-2147483648) < (snd (mss_shift ((Int.toNat ((i + 2) - lo)) + 1) a1d a2 (me_qo X) (me_n X) d h_1 lo (i + 2) v3 b2))) :
    (i + 3) = ((i + 2) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/B0_cmp_sdC2.v (replace)
example
    {eg est bw T4 T5 T6 T7 T8 : Type}
    (g : eg)
    (e : est)
    (LIM : Int)
    (nG : Int)
    (A : Int)
    (nSel : Int)
    (sc : Int)
    (gs : Int)
    (b : bw)
    (g_mtf : eg → Bool)
    (g_bs : eg → Bool)
    (e_nblock : est → Int)
    (ARR2_SIZE : Int)
    (zget : T4 → Int → Int)
    (ARR1_SIZE : Int)
    (e_arr1 : est → T5)
    (bw_numZ : T6 → Int)
    (sm_put_syms : Int → bw → T7 → T8 → T5 → Int → Int → T6)
    (e_len : est → T7)
    (e_code : est → T8)
    (SELA : T4)
    (h1 : (g_mtf g) = true)
    (h2 : (g_bs g) = true)
    (h3 : 0 ≤ (e_nblock e))
    (h4 : ((e_nblock e) + LIM) ≤ ARR2_SIZE)
    (h5 : (3 ≤ A ∧ A ≤ 258))
    (h6 : (2 ≤ nG ∧ nG ≤ 6))
    (h7 : (1 ≤ nSel ∧ nSel ≤ 18002))
    (h8 : (0 ≤ sc ∧ sc < nSel))
    (h9 : 0 ≤ gs)
    (h10 : (2 * (gs + 50)) ≤ ARR1_SIZE)
    (h11 : (bw_numZ (sm_put_syms 50 b (e_len e) (e_code e) (e_arr1 e) (zget SELA sc) gs)) ≤ LIM) :
    (gs + 33) = (gs + ((((((1 + 8) + 8) + 8) + 8) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/B0_cmp_sdC2.v (replace)
example
    {eg est bw T4 T5 T6 T7 T8 : Type}
    (g : eg)
    (e : est)
    (LIM : Int)
    (nG : Int)
    (A : Int)
    (nSel : Int)
    (sc : Int)
    (gs : Int)
    (b : bw)
    (g_mtf : eg → Bool)
    (g_bs : eg → Bool)
    (e_nblock : est → Int)
    (ARR2_SIZE : Int)
    (zget : T4 → Int → Int)
    (ARR1_SIZE : Int)
    (e_arr1 : est → T5)
    (bw_numZ : T6 → Int)
    (sm_put_syms : Int → bw → T7 → T8 → T5 → Int → Int → T6)
    (e_len : est → T7)
    (e_code : est → T8)
    (SELA : T4)
    (h1 : (g_mtf g) = true)
    (h2 : (g_bs g) = true)
    (h3 : 0 ≤ (e_nblock e))
    (h4 : ((e_nblock e) + LIM) ≤ ARR2_SIZE)
    (h5 : (3 ≤ A ∧ A ≤ 258))
    (h6 : (2 ≤ nG ∧ nG ≤ 6))
    (h7 : (1 ≤ nSel ∧ nSel ≤ 18002))
    (h8 : (0 ≤ sc ∧ sc < nSel))
    (h9 : 0 ≤ gs)
    (h10 : (2 * (gs + 50)) ≤ ARR1_SIZE)
    (h11 : (bw_numZ (sm_put_syms 50 b (e_len e) (e_code e) (e_arr1 e) (zget SELA sc) gs)) ≤ LIM) :
    (gs + 49) = (gs + (((((((((1 + 8) + 8) + 8) + 8) + 8) + 7) + 1) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCFactsBs2.v (replace)
example
    {T1 T2 T3 : Type}
    (i' : Int)
    (bp_n : T1 → Int)
    (e : T1)
    (sk : Int)
    (zget : T2 → Int → Int)
    (bp_a2o : T1 → T2)
    (key : T3 → Int → Int → Int)
    (bp_a2 : T1 → T3)
    (h1 : (0 ≤ i' ∧ i' < (bp_n e)))
    (h2 : ((sk / 256) + (256 * (zget (bp_a2o e) i'))) = (key (bp_a2 e) (bp_n e) i')) :
    i' = ((i' - 1) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCFactsGm.v (replace)
example
    {est : Type}
    (e : est)
    (q : Int)
    (e_nblock : est → Int)
    (j : Int)
    (gp_nInUse : est → Int)
    (h1 : (0 ≤ q ∧ q < (e_nblock e)))
    (h2 : (0 ≤ j ∧ j < (e_nblock e)))
    (h3 : 1 < (gp_nInUse e)) :
    q = ((q + 1) - 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCFactsSmB3.v (replace)
example (v0 : Int) :
    ((258 * 4) + v0) = ((258 * (2 * 2)) + v0) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCHuffF6.v (replace)
example (A : Int) (h1 : (3 ≤ A ∧ A ≤ 258)) :
    (A - 1) = (((Int.toNat (A - 1)) : Nat) : Int) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCPermF2.v (replace)
example
    {T1 : Type}
    (fp_unHi : T1 → Int)
    (p : T1)
    (fp_unLo : T1 → Int)
    (h1 : (Int.toNat (((fp_unHi p) - (fp_unLo p)) + 1)) = ((Int.toNat ((((fp_unHi p) - 1) - (fp_unLo p)) + 1)) + 1))
    (h2 : (fp_unLo p) ≠ (fp_unHi p)) :
    (fp_unHi p) = ((fp_unLo p) + (((Int.toNat ((((fp_unHi p) - 1) - (fp_unLo p)) + 1)) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCPermF2.v (replace)
example (k : Nat) (Zpow : Int → Int → Int) (h1 : 0 < (Zpow 2 ((k : Nat) : Int))) :
    ((2 * ((k : Nat) : Int)) + 2) = (2 * (((k + 1) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCQsortM1.v (replace)
example
    {T1 : Type}
    (mp_unHi : T1 → Int)
    (p : T1)
    (mp_unLo : T1 → Int)
    (h1 : (Int.toNat (((mp_unHi p) - (mp_unLo p)) + 1)) = ((Int.toNat ((((mp_unHi p) - 1) - (mp_unLo p)) + 1)) + 1)) :
    (mp_unHi p) = ((mp_unLo p) + (((Int.toNat ((((mp_unHi p) - 1) - (mp_unLo p)) + 1)) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCQsortM1.v (replace)
example
    {T1 : Type}
    (mp_unHi : T1 → Int)
    (p2 : T1)
    (mp_unLo : T1 → Int)
    (p1 : T1)
    (sz : Nat)
    (h1 : (Int.toNat (((mp_unHi p1) - (mp_unLo p1)) + 1)) < (sz + 1))
    (h2 : (mp_unLo p2) < (mp_unHi p2))
    (h3 : (Int.toNat (((mp_unHi p2) - (mp_unLo p2)) + 1)) = (((Int.toNat ((((mp_unHi p2) - 1) - ((mp_unLo p2) + 1)) + 1)) + 1) + 1)) :
    (mp_unHi p2) = (((mp_unLo p2) + 1) + (((Int.toNat ((((mp_unHi p2) - 1) - ((mp_unLo p2) + 1)) + 1)) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCSewA.v (replace)
example (i : Int) :
    (((i + 1) + 1) + 1) = (i + ((3 : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCSewA.v (replace)
example
    (hp : Int)
    (hp0 : Int)
    (hi : Int)
    (lo : Int)
    (h_1 : Int)
    (h1 : (hp ≠ hp0 → 3 ≤ ((hi + 1) - (lo + h_1))))
    (h2 : (Int.fdiv (hi - lo) h_1) ≤ (Int.fdiv 899989 h_1)) :
    (hp + 2) = ((hp + 1) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzCShell.v (replace)
example
    (k : Nat)
    (s : Nat)
    (h_1 : Int)
    (i : Int)
    (h1 : ((i - (h_1 * ((s : Nat) : Int))) - h_1) = (i - (h_1 * (((s + 1) : Nat) : Int))))
    (h2 : k = s)
    (h3 : k ≠ s) :
    (((s : Nat) : Int) * h_1) = (i - (i - (h_1 * ((s : Nat) : Int)))) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzDU10.v (replace)
example
    {T1 T2 T3 : Type}
    (d : T1)
    (lno : T2)
    (k : Int)
    (zget : T3 → T2 → Int)
    (d_mtfbase : T1 → T3)
    (h1 : (zget (d_mtfbase d) lno) < k) :
    ((Int.toNat ((k - 1) - (zget (d_mtfbase d) lno))) + 1) = (Int.toNat (k - (zget (d_mtfbase d) lno))) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzDU10M.v (replace)
example {T1 : Type} (length : T1 → Nat) (rest : T1) :
    ((((((9 * (length rest)) + 78) + 1) + 1) + 1) + 1) = ((9 * (((length rest) + 1) + 1)) + 64) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzDU11.v (replace)
example (k : Int) (h1 : (1 ≤ k ∧ k ≤ 256)) :
    ((Int.toNat (257 - (k + 1))) + 1) = (Int.toNat (257 - k)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzDUM.v (replace)
example (nb : Int) (h1 : 0 ≤ nb) :
    nb = (((Int.toNat nb) : Nat) : Int) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR1b.v (replace)
example
    (p : Nat)
    (n : Nat)
    (L' : Int)
    (h1 : p = n)
    (h2 : p < n)
    (h3 : (L' = 1 ∨ (L' = 2 ∨ L' = 3))) :
    ((((p + 2) : Nat) : Int) + 1) = (((((p : Nat) : Int) + 1) + 1) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR1b.v (replace)
example
    {T1 : Type}
    (p : Nat)
    (n : Nat)
    (length : T1 → Nat)
    (rcode : Int → Int → T1)
    (c' : Int)
    (L' : Int)
    (sym : Nat → Int)
    (h1 : p = n)
    (h2 : p < n)
    (h3 : (L' = 1 ∨ (L' = 2 ∨ L' = 3)))
    (h4 : (length (rcode c' L')) = 5)
    (h5 : (sym ((p + 3) + 1)) = (L' - 4)) :
    ((p + 4) + 1) = (((p + 3) + 1) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR1b.v (replace)
example
    {T1 : Type}
    (p : Nat)
    (n : Nat)
    (length : T1 → Nat)
    (rcode : Int → Int → T1)
    (c' : Int)
    (L' : Int)
    (sym : Nat → Int)
    (h1 : p = n)
    (h2 : p < n)
    (h3 : (L' = 1 ∨ (L' = 2 ∨ L' = 3)))
    (h4 : (length (rcode c' L')) = 5)
    (h5 : (sym ((p + 3) + 1)) = (L' - 4)) :
    ((((p + 5) : Nat) : Int) + 1) = ((((((((p : Nat) : Int) + 1) + 1) + 1) + 1) + 1) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR1b.v (replace)
example (m : Nat) :
    1 = (min (((m : Nat) : Int) + 1) 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR1b.v (replace)
example (n : Nat) :
    (((n + 1) + 1) + 1) = (Int.toNat (((((n : Nat) : Int) + 1) + 3) - 1)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR2D.v (replace)
example :
    (0 : Nat) = (1 - 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR3aFs.v (replace)
example (k2 : Int) (k0 : Int) (nb : Int) (k1 : Int) (h1 : k0 < k1) (h2 : k1 < k2) (h3 : k2 ≤ nb) :
    k2 = ((k2 - 1) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR3aFs.v (replace)
example (x : Int) (h1 : 0 ≤ x) :
    (x + 1) = ((((Int.toNat x) + 1) : Nat) : Int) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR3aQs.v (replace)
example (i : Int) :
    (i + 1) = ((i - ((0 : Nat) : Int)) + 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR3bMq.v (replace)
example
    (x : Int)
    (lo : Int)
    (nn : Int)
    (e1 : Int)
    (a : Int)
    (h1 : (0 ≤ nn ∧ (nn ≤ e1 ∧ (nn ≤ a ∧ (nn = e1 ∨ nn = a))))) :
    x = (lo + (x - lo)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR5a.v (replace)
example
    (n : Int)
    (v : Int)
    (k : Int)
    (Zpow : Int → Int → Int)
    (live : Int)
    (Z_shiftl : Int → Int → Int)
    (h1 : (1 ≤ n ∧ n ≤ 24))
    (h2 : (0 ≤ v ∧ v < (Zpow 2 n)))
    (h3 : (1 ≤ k ∧ k ≤ 31))
    (h4 : (Zpow 2 (32 - live)) = ((Zpow 2 n) * (Zpow 2 k)))
    (h5 : ((Z_shiftl v k) % 4294967296) = (v * (Zpow 2 k))) :
    ((32 - k) + k) = 32 := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR5cF.v (replace)
example (i : Int) (j : Int) :
    (((i * 16) + j) + 1) = ((i * 16) + (j + 1)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/BzR5cG.v (replace)
example (j : Int) :
    0 = (Int.toNat (j - j)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/CmpCutCB.v (replace)
example
    {T1 : Type}
    (l : T1)
    (lo : Int)
    (j : Int)
    (length : T1 → Nat)
    (h1 : (lo ≤ j ∧ j < (lo + (((length l) : Nat) : Int)))) :
    (lo + (((Int.toNat (j - lo)) : Nat) : Int)) = j := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/CmpHmKit.v (replace)
example (P : Int) (N_1 : Int) (A : Int) (h1 : 0 ≤ A) (h2 : (1 + A) ≤ N_1) :
    (P + 4) = (P + (4 * (((min (Int.toNat 1) (Int.toNat N_1)) : Nat) : Int))) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/CmpMem.v (replace)
example (b0 : Int) (b1 : Int) (b2 : Int) (b3 : Int) :
    (b0 + (256 * (b1 + (256 * (b2 + (256 * b3)))))) = (((b0 + (256 * b1)) + ((256 * 256) * b2)) + ((256 * (256 * 256)) * b3)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/S0F_dec_U12SB.v (replace)
example {dsv : Type} (L : dsv) (sv_nblock : dsv → Int) (h1 : 1 ≤ (sv_nblock L)) :
    0 = (((sv_nblock L) - 1) - (((Int.toNat ((sv_nblock L) - 1)) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/S0F_glue10.v (replace)
example
    {dsh list_word dsm bzs : Type}
    (uspb : Int)
    (src : Int)
    (len : Int)
    (dst : Int)
    (dn : Int)
    (lo : Int)
    (B : Int)
    (h0 : dsh)
    (cf0 : list_word)
    (d0 : dsm)
    (b0 : bzs)
    (bs_ai : bzs → Int)
    (length : list_word → Nat)
    (sm_tt : dsm → Int)
    (sm_ll16 : dsm → Int)
    (sm_ll4 : dsm → Int)
    (sm_nInUse : dsm → Int)
    (bs_src : bzs → Int)
    (bs_len : bzs → Int)
    (bs_dst : bzs → Int)
    (bs_dlen : bzs → Int)
    (alloc_ceiling : Int)
    (bs_av : bzs → Int)
    (sh_strm : dsh → Int)
    (h1 : (length cf0) = 257)
    (h2 : (sm_tt d0) = 0)
    (h3 : (sm_ll16 d0) = 0)
    (h4 : (sm_ll4 d0) = 0)
    (h5 : (0 ≤ (sm_nInUse d0) ∧ (sm_nInUse d0) < (2 ^ (32 : Nat))))
    (h6 : (bs_src b0) = src)
    (h7 : (bs_len b0) = len)
    (h8 : (bs_dst b0) = dst)
    (h9 : (bs_dlen b0) = dn)
    (h10 : (bs_ai b0) = (bs_len b0))
    (h11 : alloc_ceiling ≤ lo)
    (h12 : lo ≤ (uspb - 8624))
    (h13 : (uspb + 128) ≤ B)
    (h14 : (bs_av b0) = (bs_dlen b0))
    (h15 : (sh_strm h0) = uspb) :
    2 = (Int.toNat (len - (((bs_ai b0) - 1) - 1))) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/S0_cmp_bs.v (replace)
example
    {T1 : Type}
    (e_nblock : T1 → Int)
    (e : T1)
    (QO : Int)
    (bp_qoff : T1 → Int)
    (h1 : 10000 ≤ (e_nblock e))
    (h2 : ((QO = ((e_nblock e) + 34) ∨ QO = ((e_nblock e) + 35)) ∧ (QO % 2) = 0))
    (h3 : (bp_qoff e) = QO)
    (h4 : (((e_nblock e) + 34) ≤ QO ∧ QO ≤ ((e_nblock e) + 35))) :
    ((e_nblock e) - 1) = ((e_nblock e) + (-1)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/S0_cmp_msB.v (replace)
example
    {T1 : Type}
    (i : Int)
    (ky1 : Int)
    (zget : T1 → Int → Int)
    (ky2 : Int)
    (a2 : T1)
    (ky3 : Int)
    (h1 : (0 ≤ ky1 ∧ ky1 < 65536))
    (h2 : (0 ≤ ky2 ∧ ky2 < 65536))
    (h3 : ((ky1 / 256) + (256 * (zget a2 (i - 1)))) = ky2)
    (h4 : (0 ≤ ky3 ∧ ky3 < 65536))
    (h5 : ((ky2 / 256) + (256 * (zget a2 (i - 2)))) = ky3) :
    (i - 3) = ((i - 2) - 1) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/S0_cmp_msB.v (replace)
example
    {T1 : Type}
    (i : Int)
    (q : Nat)
    (ky1 : Int)
    (zget : T1 → Int → Int)
    (ky2 : Int)
    (a2 : T1)
    (ky3 : Int)
    (ky4 : Int)
    (h1 : (0 ≤ ky1 ∧ ky1 < 65536))
    (h2 : (0 ≤ ky2 ∧ ky2 < 65536))
    (h3 : ((ky1 / 256) + (256 * (zget a2 (i - 1)))) = ky2)
    (h4 : (0 ≤ ky3 ∧ ky3 < 65536))
    (h5 : ((ky2 / 256) + (256 * (zget a2 (i - 2)))) = ky3)
    (h6 : (0 ≤ ky4 ∧ ky4 < 65536))
    (h7 : ((ky3 / 256) + (256 * (zget a2 (i - 3)))) = ky4) :
    ((i - 4) - (4 * ((q : Nat) : Int))) = (i - (4 * (((q + 1) : Nat) : Int))) := by
  lia

-- bzip2/bzip2_compress_target: lib/Bz/S2_dec_U5C.v (replace)
example (v : Int) :
    18446744078004518911 = ((18446744073709551616 - v) + (v + 4294967295)) := by
  lia

-- bzip2/bzip2_compress_target: lib/Heap/S0H_Entry.v (replace)
example
    (area : Int)
    (gm : Int)
    (brkv : Int)
    (mas : Int)
    (b : Bool)
    (h1 : ((mas = 0 ∧ brkv = (area + 4096)) ∨ (mas = 1 ∧ brkv = ((2 ^ (64 : Nat)) - 1))))
    (h2 : (b = false → ((area + 4096) ≤ gm ∨ (gm + 69632) ≤ (area - 4096)))) :
    (((gm + 16) - 2) + ((1 : Nat) : Int)) = (gm + 15) := by
  lia

-- bzip2/bzip2_compress_target: lib/Heap/S0H_Entry.v (replace)
example
    (area : Int)
    (gm : Int)
    (brkv : Int)
    (mas : Int)
    (b : Bool)
    (h1 : ((mas = 0 ∧ brkv = (area + 4096)) ∨ (mas = 1 ∧ brkv = ((2 ^ (64 : Nat)) - 1))))
    (h2 : (b = false → ((area + 4096) ≤ gm ∨ (gm + 69632) ≤ (area - 4096)))) :
    ((((gm + 16) + (16 * 1)) - 2) + ((1 : Nat) : Int)) = (gm + 31) := by
  lia

-- bzip2/bzip2_compress_target: lib/K/A/F_printf_core_flags.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (p : Int)
    (k : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 835584)
    (h5 : ((856512 ≤ Fp ∧ (Fp + 232) ≤ 864256) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6460704 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 6467584)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (p + k) < (zlength fmt))
    (h12 : (32 ≤ (znth fmt (p + k)) ∧ (znth fmt (p + k)) < 64)) :
    ((p + k) + 1) = (p + (k + 1)) := by
  lia

-- bzip2/bzip2_compress_target: lib/K/A/L_harn.v (replace)
example (a : Int) :
    (a + 16) = ((a + ((8 : Nat) : Int)) + (((8 + 0) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/L2B/L2Kit.v (replace)
example (F : Int) (q : Int) :
    (((F / 8) + 2147450880) + q) = (((F / 8) + q) + 2147450880) := by
  lia

-- bzip2/bzip2_compress_target: lib/S0Grow.v (replace)
example
    (spz : Int)
    (alloc_ceiling : Int)
    (h1 : ((140735340871680 ≤ spz ∧ spz ≤ 140737488355328) ∧ (spz % 16) = 0))
    (h2 : alloc_ceiling = (spz - 8388608)) :
    spz = ((spz - 8388608) + (((Int.toNat 8388608) : Nat) : Int)) := by
  lia

-- bzip2/bzip2_compress_target: lib/S0MainEntry.v (replace)
example
    {word list_byte list_list_byte : Type}
    (sp0 : word)
    (a0s : list_byte)
    (path : list_byte)
    (envv : list_list_byte)
    (tid : word)
    (bv_unsigned : word → Int)
    (rndp : word → list_byte → list_byte → list_list_byte → word)
    (i : Int)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat)))) :
    ((bv_unsigned (rndp sp0 a0s path envv)) + i) = (((bv_unsigned (rndp sp0 a0s path envv)) + 0) + i) := by
  lia

-- bzip2/bzip2_compress_target: lib/Spec/MI_Kit.v (replace)
example
    {T1 : Type}
    (p : T1)
    (stride : Int)
    (i : Int)
    (snd : T1 → Int)
    (UNIT : Int)
    (h1 : 0 < stride) :
    (i * stride) = ((((snd p) + (UNIT + (stride * i))) - (snd p)) - UNIT) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YA05.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : Type}
    (d : Int)
    (bv_unsigned : T1 → Int)
    (b : T1)
    (req : T1)
    (getr : T2 → Nat → T1)
    (regs : T2)
    (ms : T3)
    (model : T4)
    (bv_eqb : T1 → T5 → Bool)
    (vm_brk : T6 → T5)
    (m_vmmaps : T4 → T6)
    (sys_input : T7 → T3 → T1 → T8)
    (segs : T7)
    (refusal_b : T8 → T4 → T9 → Bool)
    (eff_ret : T10 → T9)
    (brk_eff_lazy : T3 → T4 → T1 → T10)
    (h1 : (bv_unsigned req) = ((bv_unsigned b) + d))
    (h2 : (bv_unsigned (getr regs 17)) = 214)
    (h3 : (bv_eqb req (vm_brk (m_vmmaps model))) = false)
    (h4 : (refusal_b (sys_input segs ms (getr regs 17)) model (eff_ret (brk_eff_lazy ms model req))) = false)
    (h5 : (bv_unsigned b) < (bv_unsigned req)) :
    d = (((bv_unsigned b) + d) - (bv_unsigned b)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YC8k.v (replace)
example {T1 T2 : Type} (bv_unsigned : T1 → Int) (getr : T2 → Int → T1) (regs0 : T2) :
    (bv_unsigned (getr regs0 2)) = (((bv_unsigned (getr regs0 2)) - 304) + 304) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YC8n.v (replace)
example (bb : Int) (a : Int) (h1 : (0 ≤ bb ∧ bb < (2 ^ (64 : Nat)))) (h2 : bb ≠ 0) :
    (bb + (a - bb)) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YC8z.v (replace)
example
    {T1 T2 : Type}
    (z_ld : T1 → Int)
    (cx : T1)
    (lp : Int)
    (z_tisz : T1 → Int)
    (lzw_MR : Int → Int → Int)
    (z_nP : T1 → Int)
    (z_idl : T1 → Int)
    (z_MR : T1 → Int)
    (c1 : Int)
    (K : Int)
    (length : T2 → Nat)
    (TI : T2)
    (h1 : (8 ≤ (z_tisz cx) ∧ (z_tisz cx) ≤ 131072))
    (h2 : (lzw_MR (z_nP cx) (z_idl cx)) = (z_MR cx))
    (h3 : (z_MR cx) ≤ 26055)
    (h4 : ((z_MR cx) * 3838) ≤ ((z_MR cx) * (4094 - (z_idl cx))))
    (h5 : (0 ≤ (c1 * (z_idl cx)) ∧ (c1 * (z_idl cx)) ≤ (255 * 256)))
    (h6 : ((Int.toNat K) < (length TI) ∧ ((2 * K) + 2) ≤ (z_tisz cx)))
    (h7 : K < ((z_idl cx) * (z_idl cx))) :
    ((z_ld cx) + ((2 * lp) + 1)) = (((z_ld cx) + (2 * lp)) + 1) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YC98.v (replace)
example
    {T1 T2 : Type}
    (j : Nat)
    (lzw_MR : T1 → Int → Int)
    (z_nP : T2 → T1)
    (cx : T2)
    (z_idl : T2 → Int)
    (z_MR : T2 → Int)
    (h1 : (lzw_MR (z_nP cx) (z_idl cx)) = (z_MR cx))
    (h2 : (z_MR cx) ≤ 26055)
    (h3 : ((z_MR cx) * 3838) ≤ ((z_MR cx) * (4094 - (z_idl cx)))) :
    (32 + (10 + j)) = (42 + j) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YC9w.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (ew : T2 → Int → T3)
    (idl : Int)
    (icl : Int)
    (rx_iclen : T4 → Int)
    (cxv : T4)
    (rx_idl : T4 → Int)
    (bv_unsigned : T3 → Int)
    (Ebase : T2)
    (ly_top : T5 → Int)
    (ly : T5)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (rg : T1)
    (h1 : icl = (rx_iclen cxv))
    (h2 : idl = (rx_idl cxv))
    (h3 : (bv_unsigned (ew Ebase 2)) = (spZ regs))
    (h4 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h5 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h6 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat))))
    (h7 : ((spZ regs) % 8) = 0)
    (h8 : (2 ≤ idl ∧ idl ≤ 256))
    (h9 : (spZ rg) = ((spZ regs) - 320)) :
    (((spZ regs) - 120) + 8) = ((spZ regs) + (-112)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCax.v (replace)
example
    (k : Int)
    (Zpow : Int → Int → Int)
    (h1 : ((0 : Int) ≤ 2 ∧ (2 : Int) ≤ 8))
    (h2 : (2 ^ (2 : Nat)) ≤ (Zpow 2 (max 2 1))) :
    k = (k + 0) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCaz.v (replace)
example
    {T1 T2 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (Zpow : Int → Int → Int)
    (ly_top : T2 → Int)
    (ly : T2)
    (alloc_ceiling : Int)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (h1 : ((0 : Int) ≤ 4 ∧ (4 : Int) ≤ 8))
    (h2 : (2 ^ (4 : Nat)) ≤ (Zpow 2 (max 4 1)))
    (h3 : (((spZ regs) - 192) % 16) = 0)
    (h4 : (spZ regs) < ((ly_top ly) - 16))
    (h5 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h6 : alloc_ceiling ≤ (spZ regs))
    (h7 : ((spZ regs) % 8) = 0)
    (h8 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h9 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat)))) :
    ((spZ regs) + (-8)) = ((spZ regs) - 8) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCb8.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (SB : Int)
    (F : Int)
    (o : Int)
    (sgct : Int)
    (TRAWNEW_STK : Int)
    (ly : T1)
    (spZ : T2 → Int)
    (regs : T2)
    (ew : T3 → Int → T4)
    (E : T3)
    (bv_unsigned : T4 → Int)
    (s0Z : T2 → Int)
    (ly_top : T1 → Int)
    (h1 : (0 ≤ sgct ∧ sgct ≤ 65535))
    (h2 : TRAWNEW_STK = 16576)
    (h3 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h4 : (((spZ regs) + 16) ≤ (s0Z regs) ∧ (s0Z regs) < ((ly_top ly) - 16)))
    (h5 : F = (32 * (F / 32)))
    (h6 : (F / 8) = (4 * (F / 32)))
    (h7 : 512 ≤ (F / 8))
    (h8 : (F / 8) < 17592186044416) :
    ((SB + (F / 8)) + o) = ((SB + (F / 8)) + o) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCb8.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (res : Int)
    (a : Int)
    (sgct : Int)
    (TRAWNEW_STK : Int)
    (ly : T1)
    (alloc_ceiling : Int)
    (spZ : T2 → Int)
    (regs : T2)
    (ew : T3 → Int → T4)
    (E : T3)
    (bv_unsigned : T4 → Int)
    (s0Z : T2 → Int)
    (ly_top : T1 → Int)
    (F : Int)
    (raZ : T2 → Int)
    (h1 : (0 ≤ sgct ∧ sgct ≤ 65535))
    (h2 : TRAWNEW_STK = 16576)
    (h3 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h4 : (((spZ regs) + 16) ≤ (s0Z regs) ∧ (s0Z regs) < ((ly_top ly) - 16)))
    (h5 : F = (32 * (F / 32)))
    (h6 : (F / 8) = (4 * (F / 32)))
    (h7 : 512 ≤ (F / 8))
    (h8 : (F / 8) < 17592186044416)
    (h9 : sgct ≤ 256)
    (h10 : alloc_ceiling ≤ (spZ regs))
    (h11 : ((spZ regs) % 8) = 0)
    (h12 : (spZ regs) < ((ly_top ly) - 16))
    (h13 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h14 : (((spZ regs) - 192) + 16) ≤ (spZ regs))
    (h15 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h16 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat)))) :
    (res + (a - res)) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCb8.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (res : Int)
    (a : Int)
    (sgct : Int)
    (TRAWNEW_STK : Int)
    (ESTACK : Int)
    (ly : T1)
    (alloc_ceiling : Int)
    (spZ : T2 → Int)
    (regs : T2)
    (cfgp : Int)
    (ew : T3 → Int → T4)
    (E : T3)
    (bv_unsigned : T4 → Int)
    (s0Z : T2 → Int)
    (ly_top : T1 → Int)
    (F : Int)
    (raZ : T2 → Int)
    (h1 : (0 ≤ sgct ∧ sgct ≤ 65535))
    (h2 : TRAWNEW_STK = 16576)
    (h3 : ESTACK = 4096)
    (h4 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h5 : (((spZ regs) + 16) ≤ (s0Z regs) ∧ (s0Z regs) < ((ly_top ly) - 16)))
    (h6 : F = (32 * (F / 32)))
    (h7 : (F / 8) = (4 * (F / 32)))
    (h8 : 512 ≤ (F / 8))
    (h9 : (F / 8) < 17592186044416)
    (h10 : sgct ≤ 256)
    (h11 : alloc_ceiling ≤ (spZ regs))
    (h12 : ((spZ regs) % 8) = 0)
    (h13 : (spZ regs) < ((ly_top ly) - 16))
    (h14 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h15 : (((spZ regs) - 192) + 16) ≤ (spZ regs))
    (h16 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h17 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat))))
    (h18 : (cfgp + 40) ≤ (((spZ regs) - 192) - ESTACK)) :
    (res + (a - res)) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCf1.v (replace)
example
    {T1 T2 T3 : Type}
    (F : Int)
    (bv_unsigned : T1 → Int)
    (ew : T2 → Int → T1)
    (E : T2)
    (sp1 : Int)
    (p : Int)
    (n : Int)
    (alloc_ceiling : Int)
    (spZ : T3 → Int)
    (regs : T3)
    (LLVMF_STK : Int)
    (cur1 : Int)
    (r1 : Int)
    (req_size : Int → Int)
    (cur2 : Int)
    (r2 : Int)
    (cur3 : Int)
    (r3 : Int)
    (cur4 : Int)
    (r4 : Int)
    (cur5 : Int)
    (r5 : Int)
    (attr : Int)
    (h1 : (bv_unsigned (ew E 70)) = sp1)
    (h2 : (bv_unsigned (ew E 75)) = F)
    (h3 : (4096 ≤ p ∧ (p + n) ≤ alloc_ceiling))
    (h4 : (alloc_ceiling ≤ ((spZ regs) - LLVMF_STK) ∧ (spZ regs) ≤ (2 ^ (47 : Nat))))
    (h5 : (0 ≤ cur1 ∧ cur1 ≤ n))
    (h6 : (req_size n) = n)
    (h7 : (0 ≤ r1 ∧ r1 < (2 ^ (64 : Nat))))
    (h8 : (0 ≤ cur2 ∧ cur2 ≤ n))
    (h9 : cur1 = 2)
    (h10 : (0 ≤ r2 ∧ r2 < (2 ^ (64 : Nat))))
    (h11 : (0 ≤ cur3 ∧ cur3 ≤ n))
    (h12 : cur2 = 4)
    (h13 : (0 ≤ r3 ∧ r3 < (2 ^ (64 : Nat))))
    (h14 : (0 ≤ cur4 ∧ cur4 ≤ n))
    (h15 : cur3 = 8)
    (h16 : (0 ≤ r4 ∧ r4 < (2 ^ (64 : Nat))))
    (h17 : (0 ≤ cur5 ∧ cur5 ≤ n))
    (h18 : cur4 = 12)
    (h19 : (0 ≤ r5 ∧ r5 < (2 ^ (64 : Nat))))
    (h20 : (0 ≤ attr ∧ attr < (2 ^ (32 : Nat)))) :
    ((F + 48) + 2) = ((F + 48) + 2) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCh3.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (pf : Int)
    (fr_ptr : T1 → Int)
    (f : T1)
    (a : Int)
    (g : Int)
    (bv_unsigned : T2 → Int)
    (ew : T3 → Int → T2)
    (E : T3)
    (sp0 : Int)
    (N_1 : Int)
    (EV_FLUSH : Int)
    (cg_raw : T4 → Int)
    (s : T4)
    (rg : T5)
    (spZ : T5 → Int)
    (ly_top : T6 → Int)
    (lyc : T6)
    (st_nev : T7 → Int)
    (Sc : T7)
    (EV_MAX : Int)
    (length : T8 → Nat)
    (frames : T7 → T8)
    (blocks_bytes : T7 → Int)
    (LIVE_FLUSH : Int)
    (LIVE_MAX : Int)
    (h1 : ((g + 96) ≤ pf ∨ (pf + 1264) ≤ g))
    (h2 : (bv_unsigned (ew E 2)) = (sp0 - 80))
    (h3 : (bv_unsigned (ew E 32)) = g)
    (h4 : 0 ≤ N_1)
    (h5 : EV_FLUSH = 35)
    (h6 : ((g + 96) ≤ (fr_ptr f) ∨ ((fr_ptr f) + 40) ≤ g))
    (h7 : ((g + 96) ≤ (cg_raw s) ∨ ((cg_raw s) + 48) ≤ g))
    (h8 : (spZ rg) = (sp0 + (-80)))
    (h9 : ((spZ rg) + 32) ≤ (ly_top lyc))
    (h10 : ((st_nev Sc) + EV_FLUSH) ≤ EV_MAX)
    (h11 : (((length (frames Sc)) : Nat) : Int) ≤ 7)
    (h12 : ((blocks_bytes Sc) + LIVE_FLUSH) ≤ LIVE_MAX) :
    ((fr_ptr f) + (a - (fr_ptr f))) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCh3.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : Type}
    (pf : Int)
    (cg_raw : T1 → Int)
    (s : T1)
    (a : Int)
    (g : Int)
    (bv_unsigned : T2 → Int)
    (ew : T3 → Int → T2)
    (E : T3)
    (sp0 : Int)
    (N_1 : Int)
    (EV_FLUSH : Int)
    (f : T4)
    (fr_ptr : T4 → Int)
    (rg : T5)
    (spZ : T5 → Int)
    (ly_top : T6 → Int)
    (lyc : T6)
    (st_nev : T7 → Int)
    (Sc : T7)
    (EV_MAX : Int)
    (length : T8 → Nat)
    (frames : T7 → T8)
    (blocks_bytes : T7 → Int)
    (LIVE_FLUSH : Int)
    (LIVE_MAX : Int)
    (concat : T9 → T8)
    (YO07_s_out : T10 → T9)
    (gs : T10)
    (FRAME_OUT : Int → Int)
    (SINK_MAX : Int)
    (h1 : ((g + 96) ≤ pf ∨ (pf + 1264) ≤ g))
    (h2 : (bv_unsigned (ew E 2)) = (sp0 - 80))
    (h3 : (bv_unsigned (ew E 32)) = g)
    (h4 : 0 ≤ N_1)
    (h5 : EV_FLUSH = 35)
    (h6 : ((g + 96) ≤ (fr_ptr f) ∨ ((fr_ptr f) + 40) ≤ g))
    (h7 : ((g + 96) ≤ (cg_raw s) ∨ ((cg_raw s) + 48) ≤ g))
    (h8 : (spZ rg) = (sp0 + (-80)))
    (h9 : ((spZ rg) + 32) ≤ (ly_top lyc))
    (h10 : ((st_nev Sc) + EV_FLUSH) ≤ EV_MAX)
    (h11 : (((length (frames Sc)) : Nat) : Int) ≤ 7)
    (h12 : ((blocks_bytes Sc) + LIVE_FLUSH) ≤ LIVE_MAX)
    (h13 : ((((length (concat (YO07_s_out gs))) : Nat) : Int) + (FRAME_OUT N_1)) ≤ SINK_MAX) :
    ((cg_raw s) + (a - (cg_raw s))) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCin.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (r : Int)
    (Wd : Int)
    (Nb : Int)
    (U : T1 → T2 → Int)
    (Ev : T1)
    (SAluw : T3 → T4 → T4 → T2)
    (ALU_SUB : T3)
    (SOff : Int → Int → T4)
    (h1 : (0 ≤ (r * Wd) ∧ ((r * Wd) + Wd) ≤ Nb))
    (h2 : (Int.fmod (U Ev (SAluw ALU_SUB (SOff 23 0) (SOff 27 0))) (2 ^ (32 : Nat))) = ((r - 1) * Wd)) :
    ((r - 1) * Wd) = ((r * Wd) - Wd) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCjc.v (replace)
example
    {T1 : Type}
    (sp1 : Int)
    (sp0 : Int)
    (pt : Int)
    (p : Int)
    (c : Int)
    (npt : Int)
    (bimg : Int)
    (idx : Int)
    (req_size : T1 → Int)
    (Nb : T1)
    (h1 : pt ≤ p)
    (h2 : (p + c) ≤ (pt + npt))
    (h3 : (bimg ≤ (bimg + idx) ∧ (bimg + idx) < (bimg + (req_size Nb)))) :
    sp1 = (sp0 + (sp1 - sp0)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCjg.v (replace)
example (a : Int) (b : Int) (h1 : (0 ≤ a ∧ a ≤ b)) (h2 : (b + 1) < (2 ^ (64 : Nat))) :
    (((b + 1) - a) + (a * (2 ^ (64 : Nat)))) = ((b + 1) + (a * 18446744073709551615)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCju.v (replace)
example
    {T1 T2 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (alloc_ceiling : Int)
    (ly_top : T2 → Int)
    (ly : T2)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (h1 : alloc_ceiling ≤ (spZ regs))
    (h2 : ((spZ regs) % 8) = 0)
    (h3 : (spZ regs) < ((ly_top ly) - 16))
    (h4 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h5 : (((spZ regs) - 192) + 16) ≤ (spZ regs))
    (h6 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h7 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat)))) :
    ((spZ regs) + (-8)) = ((spZ regs) - 8) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCju.v (replace)
example
    {T1 T2 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (alloc_ceiling : Int)
    (ly_top : T2 → Int)
    (ly : T2)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (h1 : alloc_ceiling ≤ (spZ regs))
    (h2 : ((spZ regs) % 8) = 0)
    (h3 : (spZ regs) < ((ly_top ly) - 16))
    (h4 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h5 : (((spZ regs) - 192) + 16) ≤ (spZ regs))
    (h6 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h7 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat)))) :
    ((spZ regs) - 16576) = (((spZ regs) + (-192)) - 16384) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCju.v (replace)
example
    {T1 T2 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (alloc_ceiling : Int)
    (ly_top : T2 → Int)
    (ly : T2)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (h1 : alloc_ceiling ≤ (spZ regs))
    (h2 : ((spZ regs) % 8) = 0)
    (h3 : (spZ regs) < ((ly_top ly) - 16))
    (h4 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h5 : (((spZ regs) - 192) + 16) ≤ (spZ regs))
    (h6 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h7 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat)))) :
    ((spZ regs) - 192) = ((spZ regs) + (-192)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YCk6.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (bv_unsigned : T2 → Int)
    (ew : T3 → Int → T2)
    (Ev : T3)
    (ly_top : T4 → Int)
    (ly : T4)
    (alloc_ceiling : Int)
    (h1 : (bv_unsigned (ew Ev 2)) = (spZ regs))
    (h2 : (((spZ regs) - 320) % 16) = 0)
    (h3 : (spZ regs) < ((ly_top ly) - 16))
    (h4 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h5 : alloc_ceiling ≤ (spZ regs))
    (h6 : ((spZ regs) % 8) = 0) :
    ((4 * ((spZ regs) / 32)) * 8) = (32 * ((spZ regs) / 32)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YD1f.v (replace)
example
    {T1 T2 : Type}
    (V : T1 → Int)
    (n : T1)
    (kLowShadowBeg : Int)
    (a : Int)
    (kHighShadowEnd : Int)
    (bv_unsigned : T2 → Int)
    (w64 : Int → T2)
    (h1 : (kLowShadowBeg ≤ a ∧ a < kHighShadowEnd))
    (h2 : (bv_unsigned (w64 a)) = a) :
    ((512 * (V n)) * 8) = (4096 * (V n)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YD25.v (replace)
example
    {T1 T2 : Type}
    (buf : Int)
    (i : Int)
    (len : Int)
    (cap : Int)
    (req_size : Int → Int)
    (regs : T1)
    (bv_unsigned : T2 → Int)
    (sp : T2)
    (spZ : T1 → Int)
    (h1 : cap ≤ (req_size cap))
    (h2 : (spZ regs) = ((bv_unsigned sp) - 128)) :
    (buf + i) = ((buf + len) + (i - len)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE27.v (replace)
example
    {T1 T2 : Type}
    (f : Int)
    (FILE_BLOCK : Int)
    (AFWRITE_STK : Int)
    (AFW_STK : Int)
    (req_size : Int → Int)
    (length : T1 → Nat)
    (P : T1)
    (spZ : T2 → Int)
    (regs : T2)
    (p : Int)
    (n : Int)
    (Wb : T1)
    (SINK_MAX : Int)
    (h1 : FILE_BLOCK = 1264)
    (h2 : AFWRITE_STK = 6352)
    (h3 : AFW_STK = 6352)
    (h4 : (req_size FILE_BLOCK) = FILE_BLOCK)
    (h5 : (f + FILE_BLOCK) ≤ (2 ^ (47 : Nat)))
    (h6 : (((length P) : Nat) : Int) ≤ 1024)
    (h7 : ((f + FILE_BLOCK) ≤ ((spZ regs) - AFW_STK) ∨ (spZ regs) ≤ f))
    (h8 : ((p + n) ≤ ((spZ regs) - AFW_STK) ∨ (spZ regs) ≤ p))
    (h9 : (((((length Wb) : Nat) : Int) + (((length P) : Nat) : Int)) + n) ≤ SINK_MAX)
    (h10 : ((p + n) ≤ f ∨ (f + FILE_BLOCK) ≤ p)) :
    (f + 1264) = ((f + 240) + 1024) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE2a.v (replace)
example
    {alayout word T3 : Type}
    (ly : alayout)
    (f : Int)
    (cval : Int)
    (v8 : Int)
    (v9 : Int)
    (v18 : Int)
    (v19 : Int)
    (fd : word)
    (a : Int)
    (sp0 : Int)
    (ly_stk_lo : alayout → Int)
    (FOP_WIN : Int)
    (ly_stk_hi : alayout → Int)
    (bv_unsigned : word → Int)
    (TFIB_IMG_LO : Int)
    (TFIB_IMG_END : Int)
    (ew : T3 → Int → word)
    (E : T3)
    (h1 : (sp0 % 16) = 0)
    (h2 : ((ly_stk_lo ly) + FOP_WIN) ≤ sp0)
    (h3 : sp0 ≤ (ly_stk_hi ly))
    (h4 : (bv_unsigned fd) < (2 ^ (31 : Nat)))
    (h5 : 4096 ≤ f)
    (h6 : (f + 4096) ≤ (2 ^ (47 : Nat)))
    (h7 : (f % 16) = 0)
    (h8 : ((f + 1264) ≤ (sp0 - FOP_WIN) ∨ sp0 ≤ f))
    (h9 : ((f + 1264) ≤ TFIB_IMG_LO ∨ TFIB_IMG_END ≤ f))
    (h10 : (0 ≤ cval ∧ cval < (2 ^ (64 : Nat))))
    (h11 : (0 ≤ v8 ∧ v8 < (2 ^ (64 : Nat))))
    (h12 : (0 ≤ v9 ∧ v9 < (2 ^ (64 : Nat))))
    (h13 : (0 ≤ v18 ∧ v18 < (2 ^ (64 : Nat))))
    (h14 : (0 ≤ v19 ∧ v19 < (2 ^ (64 : Nat))))
    (h15 : (bv_unsigned (ew E 2)) = (sp0 - 2240))
    (h16 : (bv_unsigned (ew E 8)) = f) :
    (f + (a - f)) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE2d.v (replace)
example
    {word T2 : Type}
    (sp0 : Int)
    (bv_unsigned : word → Int)
    (getr : T2 → Int → word)
    (regs1 : T2)
    (h1 : (bv_unsigned (getr regs1 17)) = 66) :
    (sp0 - 144) = (((sp0 - 128) + (-24)) + 8) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE2r.v (replace)
example
    {word T2 : Type}
    (d : Int)
    (n : Int)
    (SB : Int)
    (a : Int)
    (kHighMemBeg : Int)
    (kHighMemEnd : Int)
    (bv_unsigned : word → Int)
    (g0 : Int)
    (g1 : Int)
    (gu : Int)
    (du : Int)
    (ge : Int)
    (de : Int)
    (b1 : Int)
    (ew : T2 → Int → word)
    (EE : T2)
    (h1 : (0 ≤ n ∧ n < (2 ^ (32 : Nat))))
    (h2 : 0 ≤ d)
    (h3 : (d + n) ≤ (2 ^ (63 : Nat)))
    (h4 : 64 < n)
    (h5 : (kHighMemBeg ≤ d ∧ (d + n) ≤ (kHighMemEnd - 1)))
    (h6 : (0 ≤ g0 ∧ ((8 * g0) ≤ d ∧ d < ((8 * g0) + 8))))
    (h7 : ((8 * g1) ≤ ((d + n) - 1) ∧ ((d + n) - 1) < ((8 * g1) + 8)))
    (h8 : (((8 * gu) ≤ (d + 7) ∧ (d + 7) < ((8 * gu) + 8)) ∧ du = (8 * gu)))
    (h9 : (((8 * ge) ≤ (d + n) ∧ (d + n) < ((8 * ge) + 8)) ∧ de = (8 * ge)))
    (h10 : (0 ≤ b1 ∧ b1 < 8))
    (h11 : (bv_unsigned (ew EE 32)) = g0)
    (h12 : (bv_unsigned (ew EE 33)) = g1) :
    (SB + (a - SB)) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE2y.v (replace)
example (gu : Int) (ge : Int) (h1 : (0 ≤ gu ∧ gu ≤ ge)) (h2 : ge < (2 ^ (62 : Nat))) :
    ((-gu) + (gu * (2 ^ (64 : Nat)))) = (gu * ((2 ^ (64 : Nat)) - 1)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE30.v (replace)
example
    {bvmap_5_word T2 T3 word : Type}
    (regs : bvmap_5_word)
    (d : Int)
    (x : Int)
    (n : Int)
    (E : T2)
    (ss : T3)
    (spZ : bvmap_5_word → Int)
    (shapeD : T3 → Bool)
    (sp0 : Int)
    (bv_unsigned : word → Int)
    (ew : T2 → Int → word)
    (j : Nat)
    (az : Int)
    (h1 : (0 ≤ n ∧ n < (2 ^ (32 : Nat))))
    (h2 : 0 ≤ d)
    (h3 : (d + n) ≤ (2 ^ (63 : Nat)))
    (h4 : 0 ≤ x)
    (h5 : (x + n) ≤ (2 ^ (63 : Nat)))
    (h6 : ((d + n) ≤ x ∨ (x + n) ≤ d))
    (h7 : (shapeD ss) = true)
    (h8 : (bv_unsigned (ew E 2)) = (sp0 - 2160))
    (h9 : (j < 10 ∧ az = (32 + ((j : Nat) : Int)))) :
    (((spZ regs) - 2160) + 2112) = ((spZ regs) - 48) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE33.v (replace)
example
    {word T2 : Type}
    (p : Int)
    (n : Int)
    (SB : Int)
    (a : Int)
    (kLowMemEnd : Int)
    (bv_unsigned : word → Int)
    (g0 : Int)
    (g1 : Int)
    (b1 : Int)
    (gu : Int)
    (du : Int)
    (ge : Int)
    (de : Int)
    (ew : T2 → Int → word)
    (EE : T2)
    (h1 : (0 < n ∧ n < (2 ^ (31 : Nat))))
    (h2 : 0 ≤ p)
    (h3 : (p + n) ≤ (2 ^ (63 : Nat)))
    (h4 : 64 < n)
    (h5 : (p + n) ≤ (kLowMemEnd - 1))
    (h6 : (0 ≤ g0 ∧ ((8 * g0) ≤ p ∧ p < ((8 * g0) + 8))))
    (h7 : ((8 * g1) ≤ ((p + n) - 1) ∧ ((p + n) - 1) < ((8 * g1) + 8)))
    (h8 : g1 < (2 ^ (44 : Nat)))
    (h9 : (0 ≤ b1 ∧ b1 < 8))
    (h10 : (((8 * gu) ≤ (p + 7) ∧ (p + 7) < ((8 * gu) + 8)) ∧ du = (8 * gu)))
    (h11 : (((8 * ge) ≤ (p + n) ∧ (p + n) < ((8 * ge) + 8)) ∧ de = (8 * ge)))
    (h12 : (bv_unsigned (ew EE 32)) = g0)
    (h13 : (bv_unsigned (ew EE 33)) = g1) :
    (SB + (a - SB)) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE6x.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (sp0 : Int)
    (j : Nat)
    (x : Int)
    (k : Int)
    (length : T1 → Nat)
    (bs : T1)
    (a : Int)
    (MC_LO : Int)
    (MC_HI : Int)
    (spZ : T2 → Int)
    (regs2 : T2)
    (bv_unsigned : T3 → Int)
    (ew : T4 → Int → T3)
    (E4 : T4)
    (h1 : ((2 ^ (44 : Nat)) ≤ sp0 ∧ sp0 ≤ (2 ^ (47 : Nat))))
    (h2 : ((x + k) + 1) ≤ ((2 ^ (47 : Nat)) - 1))
    (h3 : (((length bs) : Nat) : Int) = k)
    (h4 : j = (length bs))
    (h5 : (MC_LO ≤ a ∧ a < MC_HI))
    (h6 : (spZ regs2) = (sp0 - 2128))
    (h7 : (0 ≤ (Int.fmod a (2 ^ (64 : Nat))) ∧ (Int.fmod a (2 ^ (64 : Nat))) < (2 ^ (64 : Nat))))
    (h8 : (bv_unsigned (ew E4 2)) = (sp0 - 2128)) :
    ((sp0 - 8) - (8 * ((j : Nat) : Int))) = ((sp0 - 2128) + (2120 - (8 * ((j : Nat) : Int)))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE6x.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (sp0 : Int)
    (x : Int)
    (k : Int)
    (length : T1 → Nat)
    (bs : T1)
    (j : Nat)
    (a : Int)
    (MC_LO : Int)
    (MC_HI : Int)
    (spZ : T2 → Int)
    (regs2 : T2)
    (bv_unsigned : T3 → Int)
    (ew : T4 → Int → T3)
    (E4 : T4)
    (h1 : ((2 ^ (44 : Nat)) ≤ sp0 ∧ sp0 ≤ (2 ^ (47 : Nat))))
    (h2 : ((x + k) + 1) ≤ ((2 ^ (47 : Nat)) - 1))
    (h3 : (((length bs) : Nat) : Int) = k)
    (h4 : j = (length bs))
    (h5 : (MC_LO ≤ a ∧ a < MC_HI))
    (h6 : (spZ regs2) = (sp0 - 2128))
    (h7 : (0 ≤ (Int.fmod a (2 ^ (64 : Nat))) ∧ (Int.fmod a (2 ^ (64 : Nat))) < (2 ^ (64 : Nat))))
    (h8 : (bv_unsigned (ew E4 2)) = (sp0 - 2128)) :
    (sp0 - 48) = ((sp0 - 8) - (8 * ((5 : Nat) : Int))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE6y.v (assert)
example
    {alayout bvmap_5_word : Type}
    (ly : alayout)
    (regs : bvmap_5_word)
    (p : Int)
    (n : Int)
    (spZ : bvmap_5_word → Int)
    (ly_stk_lo : alayout → Int)
    (RC_SCR : Int)
    (ly_stk_hi : alayout → Int)
    (h1 : ((spZ regs) % 16) = 0)
    (h2 : ((ly_stk_lo ly) + RC_SCR) ≤ (spZ regs))
    (h3 : (spZ regs) ≤ (ly_stk_hi ly))
    (h4 : 0 < p)
    (h5 : (1 ≤ n ∧ n < (2 ^ (32 : Nat))))
    (h6 : 0 ≤ p)
    (h7 : (p + n) ≤ (2 ^ (63 : Nat)))
    (h8 : n ≤ 64) :
    (1 ≤ n ∧ n ≤ 64) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE79.v (replace)
example
    {T1 T2 T3 T4 word T6 T7 T8 : Type}
    (d : Int)
    (a' : Int)
    (MS_SCR : Int)
    (sp0 : Int)
    (n : Int)
    (tfibsegs : T1)
    (mrestrict : T2 → T3 → T4)
    (H : T2)
    (mem1 : T3)
    (a : Int)
    (nn : Nat)
    (store_ok : T1 → T4 → word → Nat → Bool)
    (w64 : Int → word)
    (length : T6 → Nat)
    (repeat_1 : T7 → Nat → T6)
    (cb : T7)
    (bv_unsigned : word → Int)
    (ew : T8 → Int → word)
    (E2 : T8)
    (h1 : MS_SCR = 2216)
    (h2 : ((2 ^ (44 : Nat)) ≤ sp0 ∧ sp0 ≤ (2 ^ (47 : Nat))))
    (h3 : ((nn : Nat) : Int) = n)
    (h4 : (store_ok tfibsegs (mrestrict H mem1) (w64 d) nn) = true)
    (h5 : (((length (repeat_1 cb nn)) : Nat) : Int) = n)
    (h6 : (bv_unsigned (ew E2 2)) = (sp0 - 2144))
    (h7 : (0 ≤ (Int.fmod a (2 ^ (64 : Nat))) ∧ (Int.fmod a (2 ^ (64 : Nat))) < (2 ^ (64 : Nat)))) :
    (d + (a' - d)) = a' := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE79.v (replace)
example
    {T1 T2 word : Type}
    (d : Int)
    (n : Int)
    (E : T1)
    (ss : T2)
    (sp0 : Int)
    (tail_shape : T2 → Bool)
    (MS_SCR : Int)
    (bv_unsigned : word → Int)
    (MS_STK : Int)
    (ew : T1 → Int → word)
    (h1 : (0 ≤ n ∧ n < (2 ^ (32 : Nat))))
    (h2 : 0 ≤ d)
    (h3 : (d + n) ≤ (2 ^ (63 : Nat)))
    (h4 : (tail_shape ss) = true)
    (h5 : MS_SCR = 2216)
    (h6 : MS_STK = 2208)
    (h7 : (bv_unsigned (ew E 2)) = sp0) :
    (sp0 + (-64)) = (sp0 - 64) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YE7e.v (assert)
example
    {alayout bvmap_5_word : Type}
    (ly : alayout)
    (regs : bvmap_5_word)
    (p : Int)
    (n : Int)
    (m : Int)
    (spZ : bvmap_5_word → Int)
    (ly_stk_lo : alayout → Int)
    (RC_SCR : Int)
    (ly_stk_hi : alayout → Int)
    (h1 : ((spZ regs) % 16) = 0)
    (h2 : ((ly_stk_lo ly) + RC_SCR) ≤ (spZ regs))
    (h3 : (spZ regs) ≤ (ly_stk_hi ly))
    (h4 : (n < m ∧ m < (2 ^ (63 : Nat))))
    (h5 : 0 < p)
    (h6 : (1 ≤ n ∧ n < (2 ^ (32 : Nat))))
    (h7 : 0 ≤ p)
    (h8 : (p + n) ≤ (2 ^ (63 : Nat)))
    (h9 : n ≤ 64) :
    (1 ≤ n ∧ n ≤ 64) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFer.v (replace)
example {T1 : Type} (addr : T1 → Int) (b2 : T1) (j : Int) (pnp : Int) (h1 : pnp ≠ 0) :
    ((addr b2) + (8 + j)) = (((addr b2) + 8) + j) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFf2.v (replace)
example
    {alayout astate T3 list_Z : Type}
    (ly : alayout)
    (X : astate)
    (sp : Int)
    (ly_T : alayout → Int)
    (t_cache : Int)
    (kk : Nat)
    (need_new_batch : T3 → Bool)
    (st_qthread : astate → T3)
    (st_cache_inited : astate → Bool)
    (ly_stk_lo : alayout → Int)
    (QSTACK : Int)
    (ly_stk_hi : alayout → Int)
    (length : list_Z → Nat)
    (all_batches : astate → list_Z)
    (st_nev : astate → Int)
    (prim_user_mapped : astate → Int)
    (kUserMapSize : Int)
    (h1 : (need_new_batch (st_qthread X)) = true)
    (h2 : (st_cache_inited X) = true)
    (h3 : (((ly_stk_lo ly) + QSTACK) ≤ sp ∧ sp ≤ (ly_stk_hi ly)))
    (h4 : ((((length (all_batches X)) : Nat) : Int) + 1) ≤ (st_nev X))
    (h5 : ((prim_user_mapped X) + kUserMapSize) ≤ (kUserMapSize * (st_nev X))) :
    ((((ly_T ly) + t_cache) + 1920) + ((kk : Nat) : Int)) = (((ly_T ly) + (t_cache + (80 * 24))) + ((kk : Nat) : Int)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFf2.v (replace)
example
    {alayout astate T3 list_Z : Type}
    (ly : alayout)
    (X : astate)
    (sp : Int)
    (ly_NB : alayout → Int)
    (id_1 : Int)
    (kk : Nat)
    (need_new_batch : T3 → Bool)
    (st_qthread : astate → T3)
    (st_cache_inited : astate → Bool)
    (ly_stk_lo : alayout → Int)
    (QSTACK : Int)
    (ly_stk_hi : alayout → Int)
    (length : list_Z → Nat)
    (all_batches : astate → list_Z)
    (st_nev : astate → Int)
    (prim_user_mapped : astate → Int)
    (kUserMapSize : Int)
    (st_depot : astate → list_Z)
    (h1 : (need_new_batch (st_qthread X)) = true)
    (h2 : (st_cache_inited X) = true)
    (h3 : (((ly_stk_lo ly) + QSTACK) ≤ sp ∧ sp ≤ (ly_stk_hi ly)))
    (h4 : ((((length (all_batches X)) : Nat) : Int) + 1) ≤ (st_nev X))
    (h5 : ((prim_user_mapped X) + kUserMapSize) ≤ (kUserMapSize * (st_nev X)))
    (h6 : (((length (st_depot X)) : Nat) : Int) ≤ 4096) :
    (((ly_NB ly) + (16 * id_1)) + (8 + ((kk : Nat) : Int))) = ((((ly_NB ly) + (16 * id_1)) + 8) + ((kk : Nat) : Int)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFf7.v (replace)
example {alayout : Type} (ly : alayout) (a : Int) (ly_T : alayout → Int) (t_stats : Int) :
    a = ((((ly_T ly) + t_stats) + 48) + (a - (((ly_T ly) + t_stats) + 48))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFfu.v (replace)
example (w : Nat) (i : Int) (h1 : (0 ≤ i ∧ i < ((w : Nat) : Int))) :
    (((Int.toNat i) : Nat) : Int) = i := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFfu.v (replace)
example
    {alayout batch : Type}
    (ly : alayout)
    (lastb : batch)
    (YFgi_Bv : alayout → batch → Int)
    (a : Int) :
    (((YFgi_Bv ly lastb) + 8) + (a - ((YFgi_Bv ly lastb) + 8))) = a := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFfz.v (replace)
example
    {bvmap_5_word T2 : Type}
    (regs : bvmap_5_word)
    (bv_unsigned : T2 → Int)
    (getr : bvmap_5_word → Int → T2) :
    ((bv_unsigned (getr regs 2)) + ((-264) * 8)) = ((bv_unsigned (getr regs 2)) - 2112) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFfz.v (replace)
example
    {bvmap_5_word T2 : Type}
    (regs : bvmap_5_word)
    (bv_unsigned : T2 → Int)
    (getr : bvmap_5_word → Int → T2) :
    ((bv_unsigned (getr regs 2)) + ((-136) * 16)) = ((bv_unsigned (getr regs 2)) + (-2176)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFg3.v (replace)
example (TFIB_IAL_W : Int) (TFIB_IAL_LO : Int) :
    (TFIB_IAL_W + 16) = (TFIB_IAL_LO + ((TFIB_IAL_W - TFIB_IAL_LO) + 16)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFg7.v (assert)
example {chunk : Type} (k : chunk) (YFfr_rrz : chunk → Int) :
    ((YFfr_rrz k) = 16 ∨ (YFfr_rrz k) ≠ 16) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFgc.v (replace)
example
    {alayout bvmap_5_word list_____Z_Z_Z : Type}
    (ly : alayout)
    (regs0 : bvmap_5_word)
    (ch : list_____Z_Z_Z)
    (YFgi_LENv : alayout → bvmap_5_word → list_____Z_Z_Z → Int)
    (sp0 : Int)
    (h1 : (0 ≤ sp0 ∧ sp0 < (2 ^ (64 : Nat)))) :
    ((YFgi_LENv ly regs0 ch) + ((2 ^ (32 : Nat)) * 0)) = (YFgi_LENv ly regs0 ch) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFhg.v (replace)
example
    {bvmap_5_word T2 : Type}
    (regs0 : bvmap_5_word)
    (bv_unsigned : T2 → Int)
    (getr : bvmap_5_word → Int → T2) :
    (bv_unsigned (getr regs0 2)) = (((bv_unsigned (getr regs0 2)) - 112) + 112) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFhl.v (replace)
example
    (a : Int)
    (n : Nat)
    (a' : Int)
    (TFIB_IMG_END : Int)
    (h1 : (a ≤ a' ∧ a' < (a + ((n : Nat) : Int))))
    (h2 : (TFIB_IMG_END ≤ a' ∧ a' < (2 ^ (64 : Nat)))) :
    (a + (((Int.toNat (a' - a)) : Nat) : Int)) = a' := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFjm.v (replace)
example (qm : Int) (q8 : Int) :
    ((((qm * 512) + 1024) + q8) * 8) = ((((qm * 4096) + 6144) + (q8 * 8)) + 2048) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFk5.v (replace)
example
    {T1 T2 word T4 : Type}
    (i : Int)
    (cnt : Int)
    (store_ok : T1 → T2 → word → Nat → Bool)
    (tfibsegs : T1)
    (mr : T2)
    (Z_to_bv : Int → Int → word)
    (e : Int)
    (length : T4 → Nat)
    (bs : T4)
    (h1 : (store_ok tfibsegs mr (Z_to_bv 64 (e - (4 * cnt))) (Int.toNat (4 * (cnt - 0)))) = true)
    (h2 : (((length bs) : Nat) : Int) = (4 * cnt)) :
    i = (((((Int.toNat (cnt - 0)) : Nat) : Int) - 1) - ((cnt - 1) - i)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YFko.v (replace)
example
    {alayout : Type}
    (ly : alayout)
    (nf : Int)
    (mf : Int)
    (a : Int)
    (i : Int)
    (kFreeArrayMax : Int)
    (kFreeArrayMapSize : Int)
    (ly_stk_lo : alayout → Int)
    (RSTACK : Int)
    (sp0 : Int)
    (ly_stk_hi : alayout → Int)
    (h1 : (0 ≤ nf ∧ (4 * nf) ≤ mf))
    (h2 : ((0 ≤ mf ∧ mf ≤ kFreeArrayMax) ∧ (Int.fmod mf kFreeArrayMapSize) = 0))
    (h3 : (((ly_stk_lo ly) + RSTACK) ≤ sp0 ∧ (sp0 ≤ (ly_stk_hi ly) ∧ (sp0 % 16) = 0))) :
    (a + (1 + i)) = ((a + 1) + i) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YG0l.v (replace)
example (a : Int) (a' : Int) (b : Int) (k : Int) (h1 : 0 < b) (h2 : a' ≤ (a + (b * k))) :
    (((a + b) - 1) + (k * b)) = (((a + (b * k)) + b) - 1) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YG0s.v (replace)
example
    {asyms T2 T3 T4 T5 T6 : Type}
    (B : asyms)
    (ck_rz : T2 → Int)
    (k : T2)
    (i : Int)
    (ck_base : asyms → T3 → T2 → Int)
    (ly : T3)
    (req_size : T4 → Int)
    (ck_req : T2 → T4)
    (shadow_of_addr : T5 → Int → Int)
    (SHADOW_OFF : T5)
    (shadow_addr : T6 → Int)
    (g : T6)
    (h1 : (8 * (((req_size (ck_req k)) + 7) / 8)) ≤ ((req_size (ck_req k)) + 7))
    (h2 : ((shadow_of_addr SHADOW_OFF ((ck_base B ly k) + (ck_rz k))) + i) = (shadow_addr g)) :
    ((ck_rz k) + (i * 8)) = ((((ck_base B ly k) + (ck_rz k)) + (8 * i)) - (ck_base B ly k)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI1d.v (replace)
example (sp0 : Int) (j : Nat) (h1 : j < 11) :
    ((sp0 - 96) + (88 - (8 * ((j : Nat) : Int)))) = ((sp0 - 8) - (8 * ((j : Nat) : Int))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI1e.v (replace)
example
    {T1 T2 : Type}
    (sp0 : Int)
    (fn : Nat)
    (bv_unsigned : T1 → Int)
    (ew : T2 → Int → T1)
    (E : T2)
    (g : Int)
    (cfp : Int)
    (fr_ptr : Nat → Int)
    (h1 : (bv_unsigned (ew E 2)) = (sp0 - 96))
    (h2 : (bv_unsigned (ew E 8)) = g)
    (h3 : (bv_unsigned (ew E 9)) = cfp)
    (h4 : (bv_unsigned (ew E 18)) = (fr_ptr fn)) :
    (sp0 + ((-6) * 16)) = (sp0 - 96) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI1f.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 : Type}
    (nf : Int)
    (CGIF_SIZE : Int)
    (FRAME_SIZE : Int)
    (g : Int)
    (s : T1)
    (i : Nat)
    (bv_unsigned : T2 → Int)
    (ew : T3 → Int → T2)
    (E : T3)
    (sp0 : Int)
    (cfp : Int)
    (U : T3 → T4 → Int)
    (SAlu : T5 → T6 → T7 → T4)
    (ALU_AND : T5)
    (SExt : Bool → Int → T8 → T6)
    (SOff : Int → Int → T8)
    (SLit : Int → T7)
    (Z_land : T9 → Int → Int)
    (cg_attr : T1 → T9)
    (YO07_flag : T9 → Int → Bool)
    (h1 : CGIF_SIZE = 96)
    (h2 : FRAME_SIZE = 40)
    (h3 : i < 3)
    (h4 : (i - 1) < 3)
    (h5 : (bv_unsigned (ew E 2)) = (sp0 - 96))
    (h6 : (bv_unsigned (ew E 8)) = g)
    (h7 : (bv_unsigned (ew E 9)) = cfp)
    (h8 : (bv_unsigned (ew E 18)) = nf)
    (h9 : (U E (SAlu ALU_AND (SExt false 8 (SOff 56 0)) (SLit 8))) = (Z_land (cg_attr s) 8))
    (h10 : (YO07_flag (cg_attr s) 8) = true) :
    ((nf + 32) + ((1 : Nat) : Int)) = (nf + 33) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI1r.v (replace)
example
    {T1 T2 : Type}
    (bl : Int)
    (i : Int)
    (cbb_prefix : T1 → Nat → T2)
    (BL : T1)
    (length : T2 → Nat)
    (h1 : (((length (cbb_prefix BL (Int.toNat i))) : Nat) : Int) = (256 * i)) :
    (bl + (((255 * (Int.toNat i)) : Nat) : Int)) = (bl + (255 * i)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI1r.v (replace)
example
    {T1 T2 : Type}
    (i : Int)
    (bb : Int)
    (j : Int)
    (cbb_prefix : T1 → Nat → T2)
    (BL : T1)
    (length : T2 → Nat)
    (h1 : (((length (cbb_prefix BL (Int.toNat i))) : Nat) : Int) = (256 * i)) :
    (((256 * i) + (bb + 1)) + j) = (((bb + (256 * i)) + 1) + j) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI2h.v (replace)
example
    {T1 T2 : Type}
    (sp0 : Int)
    (w : Int)
    (h_1 : Int)
    (s : T1)
    (f : Nat)
    (cg_frames : T1 → T2)
    (i : Nat)
    (length : T2 → Nat)
    (N_1 : Int)
    (fr_ptr : Nat → Int)
    (h1 : i < (length (cg_frames s)))
    (h2 : (1 ≤ (h_1 * w) ∧ (h_1 * w) ≤ N_1))
    (h3 : ((fr_ptr f) % 8) = 0)
    (h4 : ((sp0 - 272) % 16) = 0) :
    (sp0 + ((-17) * 16)) = (sp0 - 272) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI2o.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (sp0 : Int)
    (f : Nat)
    (cg_frames : T1 → T2)
    (s : T1)
    (i : Nat)
    (length : T2 → Nat)
    (u : Int)
    (bv_unsigned : T3 → Int)
    (ew : T4 → Int → T3)
    (E : T4)
    (g : Int)
    (fr_ptr : Nat → Int)
    (spZ : T5 → Int)
    (ms_regs : T6 → T5)
    (msx : T6)
    (fr_attr : Nat → Int)
    (hastrans : Int)
    (j : Nat)
    (lay_shift : Nat → T7 → T2)
    (LAY_RawFrameConfig : T7)
    (Z_land : Int → Int → Int)
    (FILE_BLOCK : Int)
    (bytes : T2)
    (FRAME_OUT : T8 → Int)
    (N_1 : T8)
    (cg_file : T1 → Int)
    (a : Int)
    (k : Int)
    (h1 : i < (length (cg_frames s)))
    (h2 : (0 ≤ u ∧ u ≤ 1))
    (h3 : (bv_unsigned (ew E 2)) = (sp0 - 272))
    (h4 : (bv_unsigned (ew E 8)) = g)
    (h5 : (bv_unsigned (ew E 9)) = (fr_ptr f))
    (h6 : (u = 0 ∨ u = 1))
    (h7 : (spZ (ms_regs msx)) = (sp0 - 272))
    (h8 : (hastrans = 0 ∨ hastrans = 1))
    (h9 : j < (length (lay_shift 128 LAY_RawFrameConfig)))
    (h10 : u = 1)
    (h11 : (Z_land (fr_attr f) 1) ≠ 0)
    (h12 : FILE_BLOCK = 1264)
    (h13 : (((length bytes) : Nat) : Int) ≤ (FRAME_OUT N_1))
    (h14 : (¬ ((cg_file s) ≤ (a + k) ∧ (a + k) < ((cg_file s) + FILE_BLOCK))))
    (h15 : ((sp0 - 272) % 16) = 0) :
    (sp0 + ((-17) * 16)) = (sp0 - 272) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI2q.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (sp0 : Int)
    (f : T1)
    (cg_frames : T2 → T3)
    (s : T2)
    (i : Nat)
    (length : T3 → Nat)
    (bv_unsigned : T4 → Int)
    (ew : T5 → Int → T4)
    (E : T5)
    (fr_ptr : T1 → Int)
    (h1 : i < (length (cg_frames s)))
    (h2 : (bv_unsigned (ew E 2)) = (sp0 - 272))
    (h3 : (bv_unsigned (ew E 9)) = (fr_ptr f))
    (h4 : ((fr_ptr f) % 8) = 0) :
    (sp0 + ((-17) * 16)) = (sp0 - 272) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI3q.v (replace)
example
    (g : Int)
    (i : Int)
    (CGIF_SIZE : Int)
    (FILE_BLOCK : Int)
    (W : Int)
    (H : Int)
    (sp0 : Int)
    (a : Int)
    (alloc_ceiling : Int)
    (f : Int)
    (bb : Int)
    (n : Int)
    (h1 : CGIF_SIZE = 96)
    (h2 : FILE_BLOCK = 1264)
    (h3 : W = 0)
    (h4 : 1 ≤ W)
    (h5 : H = 0)
    (h6 : 1 ≤ H)
    (h7 : ((sp0 - 80) % 16) = 0)
    (h8 : (0 ≤ a ∧ a < alloc_ceiling))
    (h9 : ((f + FILE_BLOCK) ≤ g ∨ (g + CGIF_SIZE) ≤ f))
    (h10 : (0 ≤ (a - bb) ∧ (a - bb) < n))
    (h11 : ((0 ≤ a ∧ a < alloc_ceiling) ∧ (¬ (g ≤ a ∧ a < (g + 96))))) :
    (g + (24 + i)) = ((g + 24) + i) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI3q.v (replace)
example
    {T1 : Type}
    (pala : Int)
    (j : Nat)
    (k : Nat)
    (CGIF_SIZE : Int)
    (FILE_BLOCK : Int)
    (W : Int)
    (H : Int)
    (sp0 : Int)
    (a : Int)
    (alloc_ceiling : Int)
    (f : Int)
    (g : Int)
    (bb : Int)
    (n : Int)
    (Z_land : T1 → Int → Int)
    (attr : T1)
    (pal : Int)
    (ngp : Int)
    (h1 : CGIF_SIZE = 96)
    (h2 : FILE_BLOCK = 1264)
    (h3 : W = 0)
    (h4 : 1 ≤ W)
    (h5 : H = 0)
    (h6 : 1 ≤ H)
    (h7 : ((sp0 - 80) % 16) = 0)
    (h8 : (0 ≤ a ∧ a < alloc_ceiling))
    (h9 : ((f + FILE_BLOCK) ≤ g ∨ (g + CGIF_SIZE) ≤ f))
    (h10 : (0 ≤ (a - bb) ∧ (a - bb) < n))
    (h11 : ((0 ≤ a ∧ a < alloc_ceiling) ∧ (¬ (g ≤ a ∧ a < (g + 96)))))
    (h12 : j < 10)
    (h13 : (Z_land attr 4) ≠ 0)
    (h14 : (Z_land attr 4) = 0)
    (h15 : ((g + CGIF_SIZE) ≤ pal ∨ (pal + (3 * ngp)) ≤ g))
    (h16 : ((pal + (3 * ngp)) ≤ pala ∨ (pala + (3 * ngp)) ≤ pal))
    (h17 : ((f + FILE_BLOCK) ≤ pal ∨ (pal + (3 * ngp)) ≤ f)) :
    ((pala + ((j : Nat) : Int)) + ((k : Nat) : Int)) = (pala + (((j : Nat) : Int) + ((k : Nat) : Int))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI3s.v (replace)
example
    {T1 : Type}
    (sp0 : Int)
    (CGIF_SIZE : Int)
    (FILE_BLOCK : Int)
    (f : Int)
    (g : Int)
    (a : Int)
    (bb : Int)
    (n : Int)
    (sgct : Int)
    (ngp : Int)
    (PALMAX : Int)
    (j : Nat)
    (alloc_ceiling : Int)
    (Z_land : T1 → Int → Int)
    (attr : T1)
    (h1 : CGIF_SIZE = 96)
    (h2 : FILE_BLOCK = 1264)
    (h3 : ((f + FILE_BLOCK) ≤ g ∨ (g + CGIF_SIZE) ≤ f))
    (h4 : (0 ≤ (a - bb) ∧ (a - bb) < n))
    (h5 : (0 ≤ sgct ∧ sgct < 65536))
    (h6 : (0 ≤ (3 * ngp) ∧ (3 * ngp) ≤ PALMAX))
    (h7 : ((sp0 - 80) % 16) = 0)
    (h8 : ((sp0 - 80) % 8) = 0)
    (h9 : j < 17)
    (h10 : ((0 ≤ a ∧ a < alloc_ceiling) ∧ (¬ (g ≤ a ∧ a < (g + 96)))))
    (h11 : (Z_land attr 4) = 0) :
    sp0 = ((sp0 - 80) + 80) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI3z.v (replace)
example
    {T1 : Type}
    (a : Int)
    (c_raw : T1 → Int)
    (cx : T1)
    (FILE_BLOCK : Int)
    (c_f : T1 → Int)
    (c_g : T1 → Int)
    (bb : Int)
    (Lbb : Int)
    (h1 : FILE_BLOCK = 1264)
    (h2 : (((c_raw cx) + 48) ≤ (c_f cx) ∨ ((c_f cx) + FILE_BLOCK) ≤ (c_raw cx)))
    (h3 : (((c_g cx) + 96) ≤ (c_f cx) ∨ ((c_f cx) + FILE_BLOCK) ≤ (c_g cx)))
    (h4 : ((bb + Lbb) ≤ (c_f cx) ∨ ((c_f cx) + FILE_BLOCK) ≤ bb))
    (h5 : ((bb + Lbb) ≤ (c_raw cx) ∨ ((c_raw cx) + 48) ≤ bb))
    (h6 : (((c_g cx) + 96) ≤ (c_raw cx) ∨ ((c_raw cx) + 48) ≤ (c_g cx))) :
    a = ((c_raw cx) + (a - (c_raw cx))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI5g.v (replace)
example
    (b3 : Int)
    (b2 : Int)
    (b1 : Int)
    (b0 : Int)
    (hi : Int)
    (h1 : (0 ≤ b3 ∧ b3 < 256))
    (h2 : (0 ≤ b2 ∧ b2 < 256))
    (h3 : (0 ≤ b1 ∧ b1 < 256))
    (h4 : (0 ≤ b0 ∧ b0 < 256))
    (h5 : (0 ≤ hi ∧ ((hi * (2 ^ (24 : Nat))) + (2 ^ (24 : Nat))) ≤ (2 ^ (64 : Nat)))) :
    ((b2 + (256 * hi)) * (2 ^ (16 : Nat))) = ((b2 * (2 ^ (16 : Nat))) + (hi * (2 ^ (24 : Nat)))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI5k.v (replace)
example
    {T1 : Type}
    (sp0 : Int)
    (Z_land : T1 → Int → Int)
    (attr : T1)
    (pal0 : Int)
    (ngp : Int)
    (alloc_ceiling : Int)
    (h1 : ((sp0 - 192) % 16) = 0)
    (h2 : ((Z_land attr 4) = 0 → (4096 ≤ pal0 ∧ (pal0 + (3 * ngp)) ≤ alloc_ceiling))) :
    (sp0 - 8) = ((sp0 - 192) + 184) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YI5k.v (replace)
example
    {T1 : Type}
    (sp0 : Int)
    (Z_land : T1 → Int → Int)
    (attr : T1)
    (pal0 : Int)
    (ngp : Int)
    (alloc_ceiling : Int)
    (W : Int)
    (H : Int)
    (h1 : ((sp0 - 192) % 16) = 0)
    (h2 : ((Z_land attr 4) = 0 → (4096 ≤ pal0 ∧ (pal0 + (3 * ngp)) ≤ alloc_ceiling)))
    (h3 : (W * H) ≤ 100000000) :
    ((sp0 - 192) + 64) = (sp0 - 128) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YL0l.v (replace)
example
    {T1 T2 T3 : Type}
    (i : Int)
    (len : Int)
    (buf : Int)
    (cap : Int)
    (L : Int)
    (length : T1 → Nat)
    (E1 : T2)
    (bv_unsigned : T3 → Int)
    (ew : T2 → Int → T3)
    (w : Int)
    (bs : T1)
    (n : Int)
    (E2 : T2)
    (h1 : (0 ≤ buf ∧ buf < (2 ^ (62 : Nat))))
    (h2 : (0 ≤ len ∧ len ≤ cap))
    (h3 : (0 < cap ∧ cap ≤ (2 ^ (26 : Nat))))
    (h4 : (bv_unsigned (ew E1 46)) = w)
    (h5 : (((length bs) : Nat) : Int) = (min w (L - len)))
    (h6 : len = L)
    (h7 : (1 ≤ n ∧ n ≤ w))
    (h8 : ((len + n) ≤ L ∧ (len + n) ≤ cap))
    (h9 : (bv_unsigned (ew E2 47)) = n) :
    (Int.toNat i) = ((Int.toNat len) + (Int.toNat (i - len))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YL0o.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (i : Int)
    (dst : Int)
    (pl : Int)
    (src : Int)
    (length : T1 → Nat)
    (bs : T1)
    (bv_unsigned : T2 → Int)
    (Z_to_bv : Int → Int → T2)
    (src0segs : T3)
    (ms_mem : T4 → T5)
    (ms : T4)
    (store_ok : T3 → T5 → T2 → Nat → Bool)
    (h1 : ((dst + pl) ≤ src ∨ (src + pl) ≤ dst))
    (h2 : (length bs) = (Int.toNat pl))
    (h3 : (bv_unsigned (Z_to_bv 64 dst)) = dst)
    (h4 : (bv_unsigned (Z_to_bv 64 src)) = src)
    (h5 : (bv_unsigned (Z_to_bv 64 pl)) = (((length bs) : Nat) : Int))
    (h6 : (store_ok src0segs (ms_mem ms) (Z_to_bv 64 dst) (length bs)) = true) :
    i = ((dst + i) - dst) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YL0w.v (replace)
example
    {T1 : Type}
    (e : Int)
    (bv_unsigned : T1 → Int)
    (errno_ret : Int → T1)
    (h1 : (bv_unsigned (errno_ret e)) = ((2 ^ (64 : Nat)) - e)) :
    ((2 ^ (64 : Nat)) - e) = ((-e) + (1 * (2 ^ (64 : Nat)))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YM01.v (replace)
example
    {list___word_word : Type}
    (ivs : list___word_word)
    (nZ : Int)
    (j : Int)
    (slot28 : Int)
    (length : list___word_word → Nat)
    (ivs_bytes : list___word_word → Int)
    (JMAX : Int)
    (h1 : (0 < nZ ∧ nZ ≤ slot28))
    (h2 : ((2 * (((length ivs) : Nat) : Int)) + (Int.fdiv (ivs_bytes ivs) slot28)) < JMAX)
    (h3 : slot28 = 268435456)
    (h4 : (0 ≤ (j * slot28) ∧ (j * slot28) < (2 ^ (64 : Nat)))) :
    ((j * 65536) * 4096) = (j * 268435456) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN0e.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (a : T1)
    (getr : T2 → Int → T1)
    (regs : T2)
    (n : Int)
    (dlen : Int → Int)
    (Z_to_bv : Int → Int → T1)
    (g : Int)
    (mp : Int)
    (ctr64 : Int)
    (stride : Int → Int → Int → Int)
    (h1 : (bv_unsigned (getr regs 10)) = n)
    (h2 : (((bv_unsigned a) + 131072) ≤ 126976 ∨ 331776 ≤ (bv_unsigned a)))
    (h3 : (bv_unsigned (Z_to_bv 64 g)) = g)
    (h4 : ((g + 40) ≤ 126976 ∨ 331776 ≤ g))
    (h5 : ((g + 40) ≤ (bv_unsigned a) ∨ ((bv_unsigned a) + (dlen n)) ≤ g))
    (h6 : (0 ≤ ctr64 ∧ ctr64 < (2 ^ (64 : Nat))))
    (h7 : ((0 : Int) ≤ 0 ∧ (0 : Int) < 32))
    (h8 : ((0 : Int) ≤ 63 ∧ (63 : Int) < 64))
    (h9 : (0 ≤ mp ∧ mp < (2 ^ (52 : Nat))))
    (h10 : (0 ≤ n ∧ (n + 4) ≤ (stride 0 mp 0)))
    (h11 : (16 ≤ (bv_unsigned a) ∧ ((((bv_unsigned a) + 16) + ((stride 0 mp 0) * 0)) + (stride 0 mp 0)) ≤ (2 ^ (63 : Nat))))
    (h12 : (((stride 0 mp 0) * 0) + (((stride 0 mp 0) - 4) - n)) < (2 ^ (20 : Nat))) :
    ((bv_unsigned a) + 12) = (((bv_unsigned a) + 16) - 4) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN0e.v (replace)
example
    {T1 T2 T3 : Type}
    (g : Int)
    (k : Nat)
    (bv_unsigned : T1 → Int)
    (getr : T2 → Int → T1)
    (regs : T2)
    (n : Int)
    (a : T1)
    (dlen : Int → Int)
    (Z_to_bv : Int → Int → T1)
    (mp : Int)
    (A3 : T3)
    (ctr64 : Int)
    (stride : Int → Int → Int → Int)
    (q6 : Int)
    (e_off : Int → T3 → Int)
    (x : Int)
    (h1 : (bv_unsigned (getr regs 10)) = n)
    (h2 : (((bv_unsigned a) + 131072) ≤ 126976 ∨ 331776 ≤ (bv_unsigned a)))
    (h3 : (bv_unsigned (Z_to_bv 64 g)) = g)
    (h4 : ((g + 40) ≤ 126976 ∨ 331776 ≤ g))
    (h5 : ((g + 40) ≤ (bv_unsigned a) ∨ ((bv_unsigned a) + (dlen n)) ≤ g))
    (h6 : (0 ≤ ctr64 ∧ ctr64 < (2 ^ (64 : Nat))))
    (h7 : ((0 : Int) ≤ 0 ∧ (0 : Int) < 32))
    (h8 : ((0 : Int) ≤ 63 ∧ (63 : Int) < 64))
    (h9 : (0 ≤ mp ∧ mp < (2 ^ (52 : Nat))))
    (h10 : (0 ≤ n ∧ (n + 4) ≤ (stride 0 mp 0)))
    (h11 : (16 ≤ (bv_unsigned a) ∧ ((((bv_unsigned a) + 16) + ((stride 0 mp 0) * 0)) + (stride 0 mp 0)) ≤ (2 ^ (63 : Nat))))
    (h12 : (((stride 0 mp 0) * 0) + (((stride 0 mp 0) - 4) - n)) < (2 ^ (20 : Nat)))
    (h13 : q6 = (((bv_unsigned a) + 16) + (16 * (e_off n A3))))
    (h14 : (0 ≤ x ∧ x < (2 ^ (64 : Nat)))) :
    ((g + 28) + ((k : Nat) : Int)) = ((g + 16) + (((k + 12) : Nat) : Int)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN0e.v (replace)
example
    {T1 T2 T3 : Type}
    (q6 : Int)
    (n : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (e_off : Int → T2 → Int)
    (A3 : T2)
    (getr : T3 → Int → T1)
    (regs : T3)
    (dlen : Int → Int)
    (Z_to_bv : Int → Int → T1)
    (g : Int)
    (mp : Int)
    (ctr64 : Int)
    (stride : Int → Int → Int → Int)
    (x : Int)
    (h1 : (bv_unsigned (getr regs 10)) = n)
    (h2 : (((bv_unsigned a) + 131072) ≤ 126976 ∨ 331776 ≤ (bv_unsigned a)))
    (h3 : (bv_unsigned (Z_to_bv 64 g)) = g)
    (h4 : ((g + 40) ≤ 126976 ∨ 331776 ≤ g))
    (h5 : ((g + 40) ≤ (bv_unsigned a) ∨ ((bv_unsigned a) + (dlen n)) ≤ g))
    (h6 : (0 ≤ ctr64 ∧ ctr64 < (2 ^ (64 : Nat))))
    (h7 : ((0 : Int) ≤ 0 ∧ (0 : Int) < 32))
    (h8 : ((0 : Int) ≤ 63 ∧ (63 : Int) < 64))
    (h9 : (0 ≤ mp ∧ mp < (2 ^ (52 : Nat))))
    (h10 : (0 ≤ n ∧ (n + 4) ≤ (stride 0 mp 0)))
    (h11 : (16 ≤ (bv_unsigned a) ∧ ((((bv_unsigned a) + 16) + ((stride 0 mp 0) * 0)) + (stride 0 mp 0)) ≤ (2 ^ (63 : Nat))))
    (h12 : (((stride 0 mp 0) * 0) + (((stride 0 mp 0) - 4) - n)) < (2 ^ (20 : Nat)))
    (h13 : q6 = (((bv_unsigned a) + 16) + (16 * (e_off n A3))))
    (h14 : (0 ≤ x ∧ x < (2 ^ (64 : Nat)))) :
    (q6 + n) = ((bv_unsigned a) + ((16 + (16 * (e_off n A3))) + n)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN0m.v (replace)
example (CTX : Int) (sc : Int) :
    (((CTX + 80) + (8 * sc)) + 384) = ((CTX + 464) + (8 * sc)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN0n.v (assert)
example
    {T1 T2 T3 T4 : Type}
    (i' : Int)
    (am_avail : T1 → Int)
    (am' : T1)
    (am_freed : T1 → Int)
    (Z_testbit : Int → Int → Bool)
    (ST : Int)
    (hdr_off16 : T1 → Int → T2 → Int)
    (fr' : T2)
    (h16 : Int)
    (am_maplen : T1 → Int)
    (scl_of : T3 → Int)
    (sc' : T3)
    (znth : T3 → T4 → Int)
    (size_classes : T4)
    (class_size : T3 → Int)
    (fr_n : T2 → Int)
    (IB : Int)
    (meta_bits : T1 → Int)
    (h1 : (am_avail am') < (2 ^ (32 : Nat)))
    (h2 : (am_freed am') < (2 ^ (32 : Nat)))
    (h3 : ((Z_testbit (am_avail am') i') = false ∧ (Z_testbit (am_freed am') i') = false))
    (h4 : (((ST * i') / 16) * 16) = (ST * i'))
    (h5 : (hdr_off16 am' i' fr') = h16)
    (h6 : (am_maplen am') < (2 ^ (40 : Nat)))
    (h7 : (scl_of sc') = (znth sc' size_classes))
    (h8 : (class_size sc') = (16 * (znth sc' size_classes)))
    (h9 : 0 ≤ (ST * i'))
    (h10 : (fr_n fr') = (ST - IB))
    (h11 : 0 ≤ h16)
    (h12 : h16 ≤ 65535)
    (h13 : (16 * h16) = (ST * i'))
    (h14 : (0 ≤ (meta_bits am') ∧ (meta_bits am') < (2 ^ (64 : Nat))))
    (h15 : ((scl_of sc') * i') ≤ h16)
    (h16_1 : i' = 0)
    (h17 : (((znth sc' size_classes) * i') * 16) ≤ (((ST * i') / 16) * 16))
    (h18 : h16 < ((scl_of sc') * (i' + 1))) :
    i' = 0 := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN1f.v (replace)
example
    {T1 : Type}
    (am : T1)
    (am_sc : T1 → Int)
    (am_maplen : T1 → Int)
    (am_last : T1 → Int)
    (h1 : (0 ≤ (am_last am) ∧ (am_last am) ≤ 31))
    (h2 : (0 ≤ (am_sc am) ∧ (am_sc am) < 64))
    (h3 : 0 ≤ (am_maplen am)) :
    ((((am_sc am) + ((am_maplen am) * 64)) * 64) + ((am_last am) + 32)) = ((((am_last am) + 32) + (64 * (am_sc am))) + (4096 * (am_maplen am))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN2m.v (replace)
example (AREA_HDR : Int) (META_SIZE : Int) :
    AREA_HDR = (AREA_HDR + (META_SIZE * 0)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN36.v (replace)
example
    {T1 T2 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (FILE_BLOCK : Int)
    (FILE_BUF_OFF : Int)
    (FILE_BUFSIZ : Int)
    (f : Int)
    (bv_unsigned : T2 → Int)
    (getr : T1 → Int → T2)
    (p : Int)
    (h1 : FILE_BLOCK = 1264)
    (h2 : FILE_BUF_OFF = 240)
    (h3 : FILE_BUFSIZ = 1024)
    (h4 : ((f + FILE_BLOCK) ≤ 65536 ∨ (65536 + 8192) ≤ f))
    (h5 : ((f + FILE_BLOCK) ≤ 122880 ∨ 331776 ≤ f))
    (h6 : (bv_unsigned (getr regs 2)) = (spZ regs))
    (h7 : 0 ≤ p)
    (h8 : p = 0)
    (h9 : p ≠ 0) :
    ((spZ regs) + (-168)) = (((spZ regs) + (-184)) + 16) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN37.v (replace)
example
    (base : Int)
    (o : Int)
    (l : Int)
    (off : Int)
    (n : Nat)
    (k : Nat)
    (h1 : o ≤ off)
    (h2 : (off + ((n : Nat) : Int)) ≤ (o + l)) :
    ((base + off) + ((k : Nat) : Int)) = ((base + o) + ((off - o) + ((k : Nat) : Int))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN3a.v (replace)
example {T1 : Type} (l : T1) (r : T1) (memcmp_spec : T1 → T1 → Int) :
    (((memcmp_spec l r) + (2 ^ (64 : Nat))) + ((-1) * (2 ^ (64 : Nat)))) = (memcmp_spec l r) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YN3u.v (replace)
example {T1 : Type} (rb : T1) (length : T1 → Nat) (h1 : 8 ≤ (length rb)) :
    0 = (1 - (min 1 (length rb))) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YO0b.v (replace)
example (maplen : Int) (h1 : 0 ≤ maplen) (h2 : (0 < maplen ∧ maplen < (2 ^ (52 : Nat)))) :
    ((maplen * (2 ^ (8 : Nat))) * 16) = (maplen * 4096) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YO0b.v (replace)
example (c : Int) :
    ((-c) + (1 * (2 ^ (32 : Nat)))) = ((2 ^ (32 : Nat)) - c) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YO0g.v (replace)
example (a : Int) :
    ((2 * ((-a) - 1)) + 1) = (-((2 * a) + 1)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YO10.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (am_maplen : T1 → Int)
    (am : T1)
    (rsv_code : T1 → T2 → Int)
    (fr : T2)
    (hdr_byte3 : T1 → Int → T2 → Int)
    (i : Int)
    (Z_land : Int → Int → Int)
    (p : T3)
    (s : T4)
    (stride_of : T1 → Int)
    (st_init_done : T4 → Bool)
    (Z_testbit : T5 → Int → Bool)
    (am_avail : T1 → T5)
    (am_freed : T1 → T5)
    (poff : T3 → Int)
    (class_size : Int → Int)
    (am_sc : T1 → Int)
    (sz : Int)
    (UNIT : Int)
    (fr_off : T2 → Int)
    (am_last : T1 → Int)
    (h1 : 0 ≤ (rsv_code am fr))
    (h2 : (Z_land (hdr_byte3 am i fr) 31) = i)
    (h3 : (((stride_of am) * i) / 16) = (((stride_of am) / 16) * i))
    (h4 : (st_init_done s) = true)
    (h5 : ((Z_testbit (am_avail am) i) = false ∧ (Z_testbit (am_freed am) i) = false))
    (h6 : ((poff p) % 16) = 0)
    (h7 : ((((stride_of am) * i) / 16) * 16) = ((stride_of am) * i))
    (h8 : (class_size (am_sc am)) = (16 * sz))
    (h9 : (sz * i) ≤ ((Int.fdiv ((stride_of am) * i) UNIT) + (fr_off fr)))
    (h10 : i = 0)
    (h11 : ((sz * i) * 16) ≤ ((((stride_of am) * i) / 16) * 16))
    (h12 : ((Int.fdiv ((stride_of am) * i) UNIT) + (fr_off fr)) < (sz * (i + 1)))
    (h13 : (stride_of am) = (class_size (am_sc am)))
    (h14 : (stride_of am) = (((am_maplen am) * 4096) - UNIT))
    (h15 : (am_sc am) = 27)
    (h16 : (((stride_of am) * i) + (stride_of am)) ≤ ((stride_of am) * ((am_last am) + 1)))
    (h17 : (((((stride_of am) * i) / 16) * 16) + (16 * (fr_off fr))) ≤ (((am_maplen am) * 4096) - 20))
    (h18 : (((am_maplen am) * 4096) / 16) = ((am_maplen am) * 256)) :
    (((am_maplen am) * 256) * 16) = ((am_maplen am) * 4096) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YP08.v (replace)
example
    {T1 T2 T3 : Type}
    (a : Int)
    (total_arg_bytes_nat : T1 → Nat)
    (firstn : T2 → T3 → T1)
    (k : T2)
    (l : T3)
    (j : Nat) :
    (a + ((((total_arg_bytes_nat (firstn k l)) + j) : Nat) : Int)) = ((a + (((total_arg_bytes_nat (firstn k l)) : Nat) : Int)) + ((j : Nat) : Int)) := by
  lia

-- cgif/cgif_file_fuzzer: lib/YP0e.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (E : T1)
    (a : T2)
    (w : T2)
    (k' : Int)
    (Zpow : Int → Int → Int)
    (L : Int)
    (zcanon : Int → Int)
    (c : Int)
    (U : T1 → T2 → Int)
    (lin_denot : T1 → T3 → Int)
    (lin_div : Int → T4 → T3)
    (l : T4)
    (M64 : Int)
    (h1 : (0 < k' ∧ k' ≤ 63))
    (h2 : (U E w) = (Int.fmod ((lin_denot E (lin_div (Zpow 2 k') l)) + (Int.fdiv (zcanon c) (Zpow 2 k'))) M64))
    (h3 : 0 < (Zpow 2 k'))
    (h4 : ((Zpow 2 k') * (Zpow 2 (64 - k'))) = M64)
    (h5 : (U E a) = ((Zpow 2 k') * (U E w)))
    (h6 : (Int.fmod c (2 ^ (64 : Nat))) = ((Zpow 2 k') * (Int.fdiv (zcanon c) (Zpow 2 k')))) :
    ((Zpow 2 k') * (L + (Int.fdiv (zcanon c) (Zpow 2 k')))) = (((Zpow 2 k') * L) + ((Zpow 2 k') * (Int.fdiv (zcanon c) (Zpow 2 k')))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC16.v (replace)
example
    {T1 : Type}
    (g : Int)
    (fst : T1 → Int)
    (f : T1)
    (kk : Nat)
    (snd : T1 → Nat)
    (h1 : (0 ≤ (fst f) ∧ (((fst f) + (((snd f) : Nat) : Int)) ≤ 96 ∧ (((fst f) + (((snd f) : Nat) : Int)) ≤ 88 ∨ 92 ≤ (fst f))))) :
    (g + ((fst f) + ((kk : Nat) : Int))) = ((g + (fst f)) + ((kk : Nat) : Int)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC1e.v (replace)
example
    {T1 T2 T3 : Type}
    (SB : Int)
    (F : Int)
    (ew : T1 → Int → T2)
    (E : T1)
    (regs : T3)
    (bv_unsigned : T2 → Int)
    (spZ : T3 → Int)
    (sp1 : Int)
    (h1 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h2 : (((spZ regs) - 400) ≤ sp1 ∧ sp1 ≤ ((spZ regs) - 384)))
    (h3 : F = (32 * (F / 32)))
    (h4 : (F / 8) = (4 * (F / 32)))
    (h5 : 512 ≤ (F / 8))
    (h6 : (F / 8) < 17592186044416) :
    ((SB + (F / 8)) + (8 * 2)) = ((SB + (F / 8)) + 16) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC1o.v (replace)
example
    {T1 T2 T3 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (bv_unsigned : T2 → Int)
    (ew : T3 → Int → T2)
    (E : T3)
    (rg : T1)
    (sp1 : Int)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (h1 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h2 : (spZ rg) = sp1)
    (h3 : (raZ rg) = 555544)
    (h4 : (s0Z rg) = (spZ regs))
    (h5 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h6 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat))))
    (h7 : ((spZ regs) % 8) = 0) :
    ((2 * ((spZ regs) / 16)) * 8) = (16 * ((spZ regs) / 16)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC2z.v (replace)
example
    {T1 : Type}
    (spZ : T1 → Int)
    (regs0 : T1)
    (sp : Int)
    (sp0 : Int)
    (h1 : ((sp - sp0) % 16) = 0) :
    ((spZ regs0) + ((-20) * 16)) = ((spZ regs0) - 320) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC3a.v (replace)
example
    {T1 T2 T3 : Type}
    (z_ld : T1 → Int)
    (cx : T1)
    (lp : Int)
    (lzw_MR : Int → Int → Int)
    (z_nP : T1 → Int)
    (z_idl : T1 → Int)
    (z_MR : T1 → Int)
    (is_map : T2 → Bool)
    (mc : T2)
    (J : Int)
    (length : T3 → Nat)
    (TM : T3)
    (vLM : Int)
    (mp : Int)
    (dp : Int)
    (nth : Nat → T3 → Int → Int)
    (is_sw : T2 → Bool)
    (c : Int)
    (vLI : Int)
    (is_first : T2 → Bool)
    (is_full : T2 → Bool)
    (h1 : (lzw_MR (z_nP cx) (z_idl cx)) = (z_MR cx))
    (h2 : (z_MR cx) ≤ 26055)
    (h3 : ((z_MR cx) * 3838) ≤ ((z_MR cx) * (4094 - (z_idl cx))))
    (h4 : (2049 * (z_idl cx)) ≤ (2049 * 256))
    (h5 : ((is_map mc) = true → (0 ≤ J ∧ ((Int.toNat J) < (length TM) ∧ (((2 * J) + 2) ≤ (4098 * (z_idl cx)) ∧ ((1 ≤ vLM ∧ vLM < mp) ∧ (dp < 4096 ∧ (0 ≤ (nth (Int.toNat J) TM 0) ∧ (nth (Int.toNat J) TM 0) < 4096))))))))
    (h6 : ((is_sw mc) = true → (0 ≤ ((mp - 1) * (z_idl cx)) ∧ (J = (((mp - 1) * (z_idl cx)) + c) ∧ (((2 * J) + 2) ≤ (4098 * (z_idl cx)) ∧ ((((mp - 1) * (z_idl cx)) + (z_idl cx)) ≤ (2049 * (z_idl cx)) ∧ (vLM = 0 ∧ (vLI ≠ 0 ∧ dp < 4096))))))))
    (h7 : ((is_first mc) = true → (vLM = 0 ∧ (vLI = 0 ∧ dp < 4096))))
    (h8 : ((is_full mc) = true → dp = 4096))
    (h9 : (0 ≤ J ∧ ((2 * J) + 2) ≤ (4098 * (z_idl cx)))) :
    ((z_ld cx) + ((2 * lp) + 3)) = ((((z_ld cx) + (2 * lp)) + 2) + 1) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC3h.v (replace)
example
    {T1 T2 : Type}
    (z_ld : T1 → Int)
    (cx : T1)
    (lp : Int)
    (z_tisz : T1 → Int)
    (lzw_MR : Int → Int → Int)
    (z_nP : T1 → Int)
    (z_idl : T1 → Int)
    (z_MR : T1 → Int)
    (c1 : Int)
    (K : Int)
    (length : T2 → Nat)
    (TI : T2)
    (h1 : (8 ≤ (z_tisz cx) ∧ (z_tisz cx) ≤ 131072))
    (h2 : (lzw_MR (z_nP cx) (z_idl cx)) = (z_MR cx))
    (h3 : (z_MR cx) ≤ 26055)
    (h4 : ((z_MR cx) * 3838) ≤ ((z_MR cx) * (4094 - (z_idl cx))))
    (h5 : (0 ≤ (c1 * (z_idl cx)) ∧ (c1 * (z_idl cx)) ≤ (255 * 256)))
    (h6 : ((Int.toNat K) < (length TI) ∧ ((2 * K) + 2) ≤ (z_tisz cx)))
    (h7 : K < ((z_idl cx) * (z_idl cx))) :
    ((z_ld cx) + ((2 * lp) + 3)) = ((((z_ld cx) + (2 * lp)) + 2) + 1) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC3j.v (replace)
example
    {T1 T2 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (ly : T2)
    (alloc_ceiling : Int)
    (ly_top : T2 → Int)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (h1 : alloc_ceiling ≤ (spZ regs))
    (h2 : ((spZ regs) % 8) = 0)
    (h3 : (spZ regs) < ((ly_top ly) - 16))
    (h4 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h5 : (((spZ regs) - 192) + 16) ≤ (spZ regs))
    (h6 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h7 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat)))) :
    ((spZ regs) - 192) = ((spZ regs) + (-192)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC42.v (replace)
example
    {T1 T2 T3 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (h_1 : Int)
    (w : Int)
    (req_size : Int → Int)
    (bv_unsigned : T2 → Int)
    (ew : T3 → Int → T2)
    (E : T3)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (h1 : (h_1 * w) < (2 ^ (32 : Nat)))
    (h2 : 1 ≤ (h_1 * w))
    (h3 : (req_size (h_1 * w)) = (h_1 * w))
    (h4 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h5 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h6 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat))))
    (h7 : ((spZ regs) % 8) = 0) :
    ((spZ regs) - 120) = ((spZ regs) + (-120)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC4i.v (assert)
example
    {T1 T2 T3 T4 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (ly : T2)
    (ew : T3 → Int → T4)
    (E : T3)
    (sgct : Int)
    (bv_unsigned : T4 → Int)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (ly_top : T2 → Int)
    (F : Int)
    (alloc_ceiling : Int)
    (h1 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h2 : 547176 = (raZ regs))
    (h3 : (((spZ regs) + 16) ≤ (s0Z regs) ∧ (s0Z regs) < ((ly_top ly) - 16)))
    (h4 : F = (32 * (F / 32)))
    (h5 : (F / 8) = (4 * (F / 32)))
    (h6 : 512 ≤ (F / 8))
    (h7 : (F / 8) < 17592186044416)
    (h8 : sgct ≤ 256)
    (h9 : alloc_ceiling ≤ (spZ regs))
    (h10 : ((spZ regs) % 8) = 0)
    (h11 : (spZ regs) < ((ly_top ly) - 16))
    (h12 : (ly_top ly) ≤ (2 ^ (64 : Nat))) :
    (((spZ regs) - 192) + 16) ≤ (spZ regs) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC4i.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (ly : T2)
    (ew : T3 → Int → T4)
    (E : T3)
    (sgct : Int)
    (bv_unsigned : T4 → Int)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (ly_top : T2 → Int)
    (F : Int)
    (alloc_ceiling : Int)
    (h1 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h2 : 547176 = (raZ regs))
    (h3 : (((spZ regs) + 16) ≤ (s0Z regs) ∧ (s0Z regs) < ((ly_top ly) - 16)))
    (h4 : F = (32 * (F / 32)))
    (h5 : (F / 8) = (4 * (F / 32)))
    (h6 : 512 ≤ (F / 8))
    (h7 : (F / 8) < 17592186044416)
    (h8 : sgct ≤ 256)
    (h9 : alloc_ceiling ≤ (spZ regs))
    (h10 : ((spZ regs) % 8) = 0)
    (h11 : (spZ regs) < ((ly_top ly) - 16))
    (h12 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h13 : (((spZ regs) - 192) + 16) ≤ (spZ regs))
    (h14 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h15 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat)))) :
    ((spZ regs) + (-8)) = ((spZ regs) - 8) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC51.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (F : Int)
    (raZ : T1 → Int)
    (regs : T1)
    (ew : T2 → Int → T3)
    (E : T2)
    (bv_unsigned : T3 → Int)
    (spZ : T1 → Int)
    (msX : T4)
    (j : Int)
    (Ex : T2)
    (ms_regs : T4 → T1)
    (h1 : 529208 = (raZ regs))
    (h2 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h3 : F = (32 * (F / 32)))
    (h4 : (F / 8) = (4 * (F / 32)))
    (h5 : 512 ≤ (F / 8))
    (h6 : (F / 8) < 17592186044416)
    (h7 : (0 ≤ F ∧ F < (2 ^ (64 : Nat))))
    (h8 : (j = 4 ∨ (j = 5 ∨ (j = 6 ∨ (j = 7 ∨ (j = 8 ∨ j = 9))))))
    (h9 : (bv_unsigned (ew Ex 42)) = F)
    (h10 : (spZ (ms_regs msX)) = ((spZ regs) - 96)) :
    (((4 * (F / 32)) + 4) * 8) = ((32 * (F / 32)) + 32) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC57.v (replace)
example
    (spc : Int)
    (i : Int)
    (alloc_ceiling : Int)
    (j : Int)
    (h1 : (alloc_ceiling + 16384) ≤ spc)
    (h2 : (spc % 16) = 0)
    (h3 : (j = 0 ∨ (j = 1 ∨ (j = 2 ∨ (j = 3 ∨ (j = 4 ∨ (j = 5 ∨ (j = 6 ∨ (j = 7 ∨ (j = 8 ∨ (j = 9 ∨ (j = 10 ∨ j = 11)))))))))))) :
    ((spc + 8) + (8 + i)) = (((spc + 8) + (8 * 1)) + i) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC58.v (replace)
example
    {T1 : Type}
    (nln : Int)
    (x : Int)
    (alloc_ceiling : Int)
    (spZ : T1 → Int)
    (regs0 : T1)
    (sp0 : Int)
    (regs : T1)
    (h1 : (((alloc_ceiling + 16384) + 192) ≤ nln ∧ (nln + 2) ≤ (2 ^ (47 : Nat))))
    (h2 : (spZ regs0) ≤ nln)
    (h3 : (nln + 2) ≤ sp0)
    (h4 : ((alloc_ceiling + 16384) ≤ ((spZ regs) - 192) ∧ (spZ regs) ≤ (2 ^ (47 : Nat)))) :
    (nln + (x - nln)) = x := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC68.v (replace)
example
    (x : Int)
    (h1 : (0 ≤ x ∧ x < (2 ^ (31 : Nat))))
    (h2 : (Int.fmod (Int.fmod (x - 1) (2 ^ (64 : Nat))) (2 ^ (32 : Nat))) = (Int.fmod (x - 1) (2 ^ (32 : Nat)))) :
    x = ((x - 1) + 1) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC6o.v (replace)
example
    {T1 T2 : Type}
    (ac_f : T1 → Int)
    (C : T1)
    (T : Int)
    (h_1 : Int)
    (usedz : T2 → Int → Int)
    (ac_H : T1 → T2)
    (ac_u : T1 → Int)
    (tb : Int)
    (h1 : (524309 ≤ T ∧ T ≤ 16777216))
    (h2 : (0 ≤ h_1 ∧ h_1 < T))
    (h3 : (usedz (ac_H C) h_1) = 1)
    (h4 : ((((ac_u C) + h_1) + 1) ≤ tb ∨ (tb + 48) ≤ ((ac_u C) + h_1)))
    (h5 : ((((ac_f C) + (4 * h_1)) + 4) ≤ tb ∨ (tb + 48) ≤ ((ac_f C) + (4 * h_1))))
    (h6 : ((((ac_u C) + h_1) + 1) ≤ ((ac_f C) + (4 * h_1)) ∨ (((ac_f C) + (4 * h_1)) + 4) ≤ ((ac_u C) + h_1)))
    (h7 : (((ac_f C) + (4 * h_1)) % 4) = 0) :
    ((4 * ((ac_f C) / 16)) * 4) = (16 * ((ac_f C) / 16)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC6v.v (replace)
example
    {list_Z : Type}
    (sp0 : Int)
    (s1v : Int)
    (fmt : Int)
    (N_1 : Int)
    (imgl : list_Z)
    (off : Int)
    (j : Nat)
    (zlen : list_Z → Int)
    (h1 : s1v = (sp0 - 512))
    (h2 : (fmt = 3 ∨ fmt = 4))
    (h3 : (1 ≤ N_1 ∧ N_1 ≤ 10000))
    (h4 : (zlen imgl) = (fmt * N_1)) :
    (off + ((j : Nat) : Int)) = (((s1v + off) + ((j : Nat) : Int)) - s1v) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YC75.v (replace)
example
    (tb : Int)
    (a : Int)
    (alloc_ceiling : Int)
    (img : Int)
    (fmt : Int)
    (N_1 : Int)
    (f1 : Int)
    (h1 : Int)
    (u1 : Int)
    (p1 : Int)
    (x1 : Int)
    (h1_1 : (4096 ≤ img ∧ (img + (fmt * N_1)) ≤ alloc_ceiling))
    (h2 : (0 ≤ f1 ∧ f1 < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ h1 ∧ h1 < (2 ^ (64 : Nat))))
    (h4 : (0 ≤ u1 ∧ u1 < (2 ^ (64 : Nat))))
    (h5 : (0 ≤ p1 ∧ p1 < (2 ^ (64 : Nat))))
    (h6 : (0 ≤ x1 ∧ x1 < (2 ^ (64 : Nat)))) :
    (tb + (a - tb)) = a := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCa2.v (replace)
example
    {T1 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (raZ : T1 → Int)
    (rg : T1)
    (h1 : 529256 = (raZ regs))
    (h2 : (spZ rg) = ((spZ regs) + (-512))) :
    (((2 * ((spZ regs) / 32)) - 32) * 16) = ((32 * ((spZ regs) / 32)) + (-512)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCf0.v (assert)
example (i : Int) (h1 : (0 ≤ i ∧ i ≤ 17)) :
    (i = 0 ∨ (i = 1 ∨ (i = 2 ∨ (i = 3 ∨ (i = 4 ∨ (i = 5 ∨ (i = 6 ∨ (i = 7 ∨ (i = 8 ∨ (i = 9 ∨ (i = 10 ∨ (i = 11 ∨ (i = 12 ∨ (i = 13 ∨ (i = 14 ∨ (i = 15 ∨ (i = 16 ∨ i = 17))))))))))))))))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCf0.v (assert)
example
    (i : Int)
    (Zpow : Int → Int → Int)
    (h1 : i = 17)
    (h2 : (0 < (Zpow 2 i) ∧ (Zpow 2 i) ≤ 131072))
    (h3 : i ≤ 16) :
    i = 17 := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YChp.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (ly : T2)
    (ew : T3 → Int → T4)
    (E : T3)
    (sgct : Int)
    (bv_unsigned : T4 → Int)
    (raZ : T1 → Int)
    (s0Z : T1 → Int)
    (ly_top : T2 → Int)
    (F : Int)
    (alloc_ceiling : Int)
    (h1 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h2 : 548928 = (raZ regs))
    (h3 : (((spZ regs) + 16) ≤ (s0Z regs) ∧ (s0Z regs) < ((ly_top ly) - 16)))
    (h4 : F = (32 * (F / 32)))
    (h5 : (F / 8) = (4 * (F / 32)))
    (h6 : 512 ≤ (F / 8))
    (h7 : (F / 8) < 17592186044416)
    (h8 : sgct ≤ 256)
    (h9 : alloc_ceiling ≤ (spZ regs))
    (h10 : ((spZ regs) % 8) = 0)
    (h11 : (spZ regs) < ((ly_top ly) - 16))
    (h12 : (ly_top ly) ≤ (2 ^ (64 : Nat)))
    (h13 : (((spZ regs) - 192) + 16) ≤ (spZ regs))
    (h14 : (0 ≤ (raZ regs) ∧ (raZ regs) < (2 ^ (64 : Nat))))
    (h15 : (0 ≤ (s0Z regs) ∧ (s0Z regs) < (2 ^ (64 : Nat)))) :
    ((spZ regs) - 16576) = (((spZ regs) + (-192)) - 16384) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCi6.v (replace)
example (sp : Int) (h1 : (0 ≤ (sp - 80) ∧ sp < (2 ^ (64 : Nat)))) :
    sp = ((sp - 80) + 80) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCid.v (replace)
example
    {T1 T2 T3 : Type}
    (blk : Int)
    (a : Int)
    (raZ : T1 → Int)
    (regs : T1)
    (ew : T2 → Int → T3)
    (E : T2)
    (bv_unsigned : T3 → Int)
    (spZ : T1 → Int)
    (F : Int)
    (j : Int)
    (h1 : 529560 = (raZ regs))
    (h2 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h3 : F = (32 * (F / 32)))
    (h4 : (F / 8) = (4 * (F / 32)))
    (h5 : 512 ≤ (F / 8))
    (h6 : (F / 8) < 17592186044416)
    (h7 : (0 ≤ F ∧ F < (2 ^ (64 : Nat))))
    (h8 : (j = 4 ∨ (j = 5 ∨ (j = 6 ∨ (j = 7 ∨ (j = 8 ∨ j = 9)))))) :
    (blk + (a - blk)) = a := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCid.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (spZ : T1 → Int)
    (regs : T1)
    (raZ : T1 → Int)
    (ew : T2 → Int → T3)
    (E : T2)
    (bv_unsigned : T3 → Int)
    (msX : T4)
    (F : Int)
    (j : Int)
    (Ex : T2)
    (ms_regs : T4 → T1)
    (h1 : 529560 = (raZ regs))
    (h2 : (bv_unsigned (ew E 2)) = (spZ regs))
    (h3 : F = (32 * (F / 32)))
    (h4 : (F / 8) = (4 * (F / 32)))
    (h5 : 512 ≤ (F / 8))
    (h6 : (F / 8) < 17592186044416)
    (h7 : (0 ≤ F ∧ F < (2 ^ (64 : Nat))))
    (h8 : (j = 4 ∨ (j = 5 ∨ (j = 6 ∨ (j = 7 ∨ (j = 8 ∨ j = 9))))))
    (h9 : (bv_unsigned (ew Ex 42)) = F)
    (h10 : (spZ (ms_regs msX)) = ((spZ regs) - 96)) :
    ((spZ regs) - 96) = ((spZ regs) + (-96)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCjb.v (replace)
example (idx : Int) (c : Int) (h1 : c = 1) :
    ((idx + 1) + (c - 1)) = (idx + c) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCjc.v (replace)
example
    (idx : Int)
    (j : Int)
    (nF : Int)
    (g5 : Int)
    (g24 : Int)
    (d1 : Int)
    (ii : Int)
    (g408 : Int)
    (d2 : Int)
    (d3 : Int)
    (d4 : Int)
    (c : Int)
    (h1 : ((4 * idx) + 4) ≤ nF)
    (h2 : (g5 < g24 → (3 ≤ d1 ∧ ((4 * (idx + d1)) + 4) ≤ nF)))
    (h3 : (ii < g408 → (3 ≤ d2 ∧ ((4 * (idx + d2)) + 4) ≤ nF)))
    (h4 : (ii < g408 → (g5 ≠ 0 → (3 ≤ d3 ∧ ((4 * (idx + d3)) + 4) ≤ nF))))
    (h5 : (ii < g408 → (g5 < g24 → (3 ≤ d4 ∧ ((4 * (idx + d4)) + 4) ≤ nF))))
    (h6 : c = 1) :
    (idx + (j + 1)) = ((idx + 1) + j) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCje.v (replace)
example (fmt : Int) (s10v : Int) (cur : Int) (h1 : (4096 ≤ cur ∧ cur < 140737479966720)) :
    (fmt + s10v) = (s10v + fmt) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCkt.v (replace)
example
    {T1 T2 T3 : Type}
    (cG : T1 → Int)
    (c : T1)
    (A : Int)
    (cB : T1 → Int)
    (P : Int)
    (Z_shiftr : T2 → Int → Int)
    (zcanon : T3 → T2)
    (Z_shiftl : Int → Int → T3)
    (cR : T1 → Int)
    (Z_land : Int → Int → Int)
    (h1 : (0 ≤ P ∧ P < (2 ^ (32 : Nat))))
    (h2 : (Z_shiftr (zcanon (Z_shiftl P 56)) 40) = ((cR c) * (2 ^ (16 : Nat))))
    (h3 : (Z_land P 65280) = ((cG c) * (2 ^ (8 : Nat)))) :
    ((cG c) + (((A * (2 ^ (8 : Nat))) + (cB c)) * 256)) = (((A * (2 ^ (16 : Nat))) + ((cB c) * (2 ^ (8 : Nat)))) + (cG c)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCkz.v (replace)
example
    {T1 T2 : Type}
    (Ez : T1)
    (a : T2)
    (x : Int)
    (U : T1 → T2 → Int)
    (h1 : (U Ez a) = x)
    (h2 : (0 ≤ x ∧ x < (2 ^ (30 : Nat)))) :
    ((3 * x) * 4294967296) = (x * (3 * 4294967296)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCre.v (replace)
example
    {T1 : Type}
    (F : Int)
    (TRRFC_STK : Int)
    (ASTACK : Int)
    (alloc_ceiling : Int)
    (spZ : T1 → Int)
    (regs : T1)
    (st : Int)
    (dst : Int)
    (sp1 : Int)
    (h1 : TRRFC_STK = (176 + ASTACK))
    (h2 : ASTACK = 16384)
    (h3 : (alloc_ceiling ≤ ((spZ regs) - TRRFC_STK) ∧ (spZ regs) ≤ (2 ^ (47 : Nat))))
    (h4 : ((spZ regs) ≤ st ∧ ((st + 24) ≤ (2 ^ (47 : Nat)) ∧ alloc_ceiling ≤ st)))
    (h5 : ((4096 ≤ dst ∧ (((dst + 24) ≤ 65536 ∨ 6156288 ≤ dst) ∧ ((dst + 24) ≤ 2147446784 ∨ 17594333495296 ≤ dst))) ∧ (dst + 24) ≤ alloc_ceiling))
    (h6 : (((spZ regs) - 176) ≤ sp1 ∧ sp1 ≤ ((spZ regs) - 160)))
    (h7 : F = (32 * (F / 32)))
    (h8 : (F / 8) = (4 * (F / 32))) :
    ((4 * (F / 32)) * 8) = (32 * (F / 32)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YCre.v (replace)
example
    {T1 : Type}
    (dst : Int)
    (i : Int)
    (TRRFC_STK : Int)
    (ASTACK : Int)
    (alloc_ceiling : Int)
    (spZ : T1 → Int)
    (regs : T1)
    (st : Int)
    (sp1 : Int)
    (F : Int)
    (h1 : TRRFC_STK = (176 + ASTACK))
    (h2 : ASTACK = 16384)
    (h3 : (alloc_ceiling ≤ ((spZ regs) - TRRFC_STK) ∧ (spZ regs) ≤ (2 ^ (47 : Nat))))
    (h4 : ((spZ regs) ≤ st ∧ ((st + 24) ≤ (2 ^ (47 : Nat)) ∧ alloc_ceiling ≤ st)))
    (h5 : ((4096 ≤ dst ∧ (((dst + 24) ≤ 65536 ∨ 6156288 ≤ dst) ∧ ((dst + 24) ≤ 2147446784 ∨ 17594333495296 ≤ dst))) ∧ (dst + 24) ≤ alloc_ceiling))
    (h6 : (((spZ regs) - 176) ≤ sp1 ∧ sp1 ≤ ((spZ regs) - 160)))
    (h7 : F = (32 * (F / 32)))
    (h8 : (F / 8) = (4 * (F / 32)))
    (h9 : 512 ≤ (F / 8))
    (h10 : (F / 8) ≤ 17592184995832) :
    (dst + (0 + i)) = ((dst + 0) + i) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YD03.v (replace)
example (V : Int → Int) :
    ((((4096 * (V 0)) + (2 * (V 6))) - 1048576) * 8) = (((32768 * (V 0)) + (16 * (V 6))) - 8388608) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YD0z.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (calls : T1 → Nat)
    (data : T1)
    (bv_unsigned : T2 → Int)
    (ew : T3 → Int → T2)
    (E3 : T3)
    (sp : T2)
    (k : Int)
    (c0 : Bool)
    (sQ : Bool → Int → T4)
    (forallb : T5 → T6 → Bool)
    (drv_win_ok : T5)
    (ss_mem : T4 → T6)
    (h1 : (bv_unsigned (ew E3 0)) = (bv_unsigned sp))
    (h2 : (1 ≤ k ∧ k ≤ 4))
    (h3 : (c0 = true → k = 1))
    (h4 : (forallb drv_win_ok (ss_mem (sQ c0 k))) = true) :
    ((calls data) + (0 - 1)) = (calls data) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YE2o.v (assert)
example
    {list_byte word T3 T4 : Type}
    (bs : list_byte)
    (d : word)
    (s : word)
    (i : Nat)
    (m : Int)
    (r : Int)
    (trasegs : T3)
    (mem : T4)
    (length : list_byte → Nat)
    (store_ok : T3 → T4 → word → Nat → Bool)
    (bv_unsigned : word → Int)
    (h1 : (store_ok trasegs mem d (length bs)) = true)
    (h2 : ((bv_unsigned d) + (((length bs) : Nat) : Int)) ≤ (2 ^ (64 : Nat)))
    (h3 : ((bv_unsigned s) + (((length bs) : Nat) : Int)) ≤ (2 ^ (64 : Nat)))
    (h4 : (((bv_unsigned d) + (((length bs) : Nat) : Int)) ≤ (bv_unsigned s) ∨ ((bv_unsigned s) + (((length bs) : Nat) : Int)) ≤ (bv_unsigned d)))
    (h5 : (0 < r ∧ r < 4))
    (h6 : (32 ≤ m ∧ m < (2 ^ (64 : Nat))))
    (h7 : (((i : Nat) : Int) + m) = (((length bs) : Nat) : Int)) :
    (r = 1 ∨ (r = 2 ∨ r = 3)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YG0o.v (replace)
example (k : Int) (h1 : 0 ≤ k) :
    (k + 0) = k := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YG0w.v (replace)
example
    {T1 T2 T3 : Type}
    (a : Int)
    (shadow_addr : Int → Int)
    (ly_F : T1 → Int)
    (ly : T1)
    (fs_frame_off : T2 → T3 → Int)
    (cid : T2)
    (pos : T3) :
    a = ((shadow_addr ((ly_F ly) + (fs_frame_off cid pos))) + (a - (shadow_addr ((ly_F ly) + (fs_frame_off cid pos))))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI0d.v (replace)
example
    {list_Z T2 : Type}
    (pal : list_Z)
    (fr : list_Z)
    (imin : Int)
    (imax : Int)
    (i : Int)
    (n : Nat)
    (zlen : list_Z → Int)
    (wsum : T2 → Int)
    (node_list : list_Z → list_Z → Int → Int → Int → T2)
    (RGB_NMAX : Int)
    (h1 : (0 ≤ imin ∧ imin ≤ imax))
    (h2 : (3 * (imax + 1)) ≤ (zlen pal))
    (h3 : (imax + 1) ≤ (zlen fr))
    (h4 : (wsum (node_list pal fr imin imax 0)) ≤ RGB_NMAX)
    (h5 : (imin ≤ i ∧ i ≤ (imax + 1))) :
    ((imin + ((n : Nat) : Int)) + 1) = (imin + (((n + 1) : Nat) : Int)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI12.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (sp0 : Int)
    (CGIF_SIZE : Int)
    (g : Int)
    (s : T1)
    (nth_error : T2 → Int → Nat)
    (cg_frames : T1 → T2)
    (Some : Nat → Nat)
    (f1 : Nat)
    (f2 : Nat)
    (bv_unsigned : T3 → Int)
    (ew : T4 → Int → T3)
    (E : T4)
    (h1 : CGIF_SIZE = 96)
    (h2 : (nth_error (cg_frames s) 1) = (Some (Some f1)))
    (h3 : (nth_error (cg_frames s) 2) = (Some (Some f2)))
    (h4 : (bv_unsigned (ew E 2)) = (sp0 - 96))
    (h5 : (bv_unsigned (ew E 8)) = g)
    (h6 : ((sp0 - 96) % 16) = 0) :
    (sp0 + ((-6) * 16)) = (sp0 - 96) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI21.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (sp0 : Int)
    (f : Nat)
    (cg_frames : T1 → T2)
    (s : T1)
    (i : Nat)
    (length : T2 → Nat)
    (u : Int)
    (bv_unsigned : T3 → Int)
    (ew : T4 → Int → T3)
    (E : T4)
    (g : Int)
    (fr_ptr : Nat → Int)
    (spZ : T5 → Int)
    (ms_regs : T6 → T5)
    (msx : T6)
    (j : Nat)
    (lay_shift : Nat → T7 → T2)
    (LAY_RawFrameConfig : T7)
    (h1 : i < (length (cg_frames s)))
    (h2 : (0 ≤ u ∧ u ≤ 1))
    (h3 : (bv_unsigned (ew E 2)) = (sp0 - 272))
    (h4 : (bv_unsigned (ew E 8)) = g)
    (h5 : (bv_unsigned (ew E 9)) = (fr_ptr f))
    (h6 : (u = 0 ∨ u = 1))
    (h7 : (spZ (ms_regs msx)) = (sp0 - 272))
    (h8 : j < (length (lay_shift 128 LAY_RawFrameConfig))) :
    (sp0 + ((-17) * 16)) = (sp0 - 272) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI2p.v (replace)
example
    {T1 : Type}
    (sp0 : Int)
    (i : Int)
    (CGIF_SIZE : Int)
    (W : Int)
    (H : Int)
    (j : Nat)
    (Z_land : T1 → Int → Int)
    (attr : T1)
    (h1 : CGIF_SIZE = 96)
    (h2 : 1 ≤ W)
    (h3 : 1 ≤ H)
    (h4 : ((sp0 - 80) % 16) = 0)
    (h5 : j < 10)
    (h6 : (Z_land attr 4) ≠ 0) :
    ((sp0 + (-56)) + (i - 24)) = ((sp0 - 80) + i) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI2p.v (replace)
example
    {T1 : Type}
    (pal : Int)
    (a : Int)
    (CGIF_SIZE : Int)
    (W : Int)
    (H : Int)
    (sp0 : Int)
    (g : Int)
    (j : Nat)
    (Z_land : T1 → Int → Int)
    (attr : T1)
    (ngp : Int)
    (pala : Int)
    (h1 : CGIF_SIZE = 96)
    (h2 : 1 ≤ W)
    (h3 : 1 ≤ H)
    (h4 : ((sp0 - 80) % 16) = 0)
    (h5 : j < 10)
    (h6 : (Z_land attr 4) ≠ 0)
    (h7 : (Z_land attr 4) = 0)
    (h8 : ((g + CGIF_SIZE) ≤ pal ∨ (pal + (3 * ngp)) ≤ g))
    (h9 : ((pal + (3 * ngp)) ≤ pala ∨ (pala + (3 * ngp)) ≤ pal)) :
    (pal + (a - pal)) = a := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI2p.v (replace)
example
    {T1 : Type}
    (sp0 : Int)
    (i : Int)
    (CGIF_SIZE : Int)
    (W : Int)
    (H : Int)
    (g : Int)
    (j : Nat)
    (Z_land : T1 → Int → Int)
    (attr : T1)
    (pal : Int)
    (ngp : Int)
    (pala : Int)
    (h1 : CGIF_SIZE = 96)
    (h2 : 1 ≤ W)
    (h3 : 1 ≤ H)
    (h4 : ((sp0 - 80) % 16) = 0)
    (h5 : j < 10)
    (h6 : (Z_land attr 4) ≠ 0)
    (h7 : (Z_land attr 4) = 0)
    (h8 : ((g + CGIF_SIZE) ≤ pal ∨ (pal + (3 * ngp)) ≤ g))
    (h9 : ((pal + (3 * ngp)) ≤ pala ∨ (pala + (3 * ngp)) ≤ pal)) :
    ((sp0 + (-80)) + i) = ((sp0 - 80) + i) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI2q.v (replace)
example
    (sp0 : Int)
    (sgct : Int)
    (j : Nat)
    (h1 : (0 ≤ sgct ∧ sgct < 65536))
    (h2 : ((sp0 - 80) % 16) = 0)
    (h3 : ((sp0 - 80) % 8) = 0)
    (h4 : j < 17) :
    sp0 = ((sp0 - 80) + 80) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI3o.v (replace)
example
    {T1 T2 : Type}
    (sp : T1 → Int)
    (regs0 : T1)
    (m : Int)
    (Lf : Int)
    (elen : T2 → Int)
    (E' : T2)
    (cnt : Int)
    (k0 : T2)
    (k1 : T2)
    (j : Int)
    (h1 : (elen E') = cnt)
    (h2 : (0 ≤ (elen k0) ∧ (elen k0) ≤ 1))
    (h3 : (0 ≤ (elen k1) ∧ (elen k1) ≤ 1))
    (h4 : j = m)
    (h5 : j = (m + 1))
    (h6 : (((sp regs0) + 904) + (16 * (Lf + 1))) = (((sp regs0) + 928) + (8 * m))) :
    (((sp regs0) + 928) + (8 * (m + 1))) = (((sp regs0) + 912) + (16 * (Lf + 1))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI3p.v (replace)
example (i : Int) (a : Int) (cut : Int) (h1 : (((a + 16) + (8 * cut)) % 8) = 0) :
    (i + (-1)) = (i - 1) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI3s.v (replace)
example
    {bvmap_5_word : Type}
    (regs0 : bvmap_5_word)
    (W : Int)
    (N_1 : Int)
    (flt : Int)
    (fimg : Int)
    (a : Int)
    (RGB_NMAX : Int)
    (alloc_ceiling : Int)
    (RGBA_STK : Int)
    (sp0 : bvmap_5_word → Int)
    (M : Int)
    (SRC2_RO9 : Int)
    (h1 : 1 ≤ N_1)
    (h2 : N_1 ≤ RGB_NMAX)
    (h3 : 1 ≤ W)
    (h4 : (alloc_ceiling + RGBA_STK) ≤ (sp0 regs0))
    (h5 : (sp0 regs0) < (2 ^ (63 : Nat)))
    (h6 : ((sp0 regs0) % 16) = 0)
    (h7 : 4096 ≤ flt)
    (h8 : (flt + (4 * M)) ≤ alloc_ceiling)
    (h9 : (flt % 16) = 0)
    (h10 : 4096 ≤ fimg)
    (h11 : (fimg + N_1) ≤ alloc_ceiling)
    (h12 : ((flt + (4 * M)) ≤ fimg ∨ (fimg + N_1) ≤ flt))
    (h13 : ((flt + (4 * M)) ≤ SRC2_RO9 ∨ (SRC2_RO9 + 8) ≤ flt))
    (h14 : (fimg ≤ a ∧ a < (fimg + N_1))) :
    (fimg + (a - fimg)) = a := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI41.v (replace)
example
    {T1 : Type}
    (sp0 : Int)
    (spZ : T1 → Int)
    (regs0 : T1)
    (sp : T1 → Int)
    (fmt : Int)
    (N_1 : Int)
    (av : Int)
    (h1 : sp0 = (spZ regs0))
    (h2 : (sp regs0) = (sp0 - 5136))
    (h3 : ((sp0 - 5136) % 16) = 0)
    (h4 : 0 < (fmt * N_1))
    (h5 : (av = 2 ∨ av = 4)) :
    (((sp0 - 5136) + 120) + 28) = ((sp0 - 5136) + 148) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI46.v (replace)
example
    {colour : Type}
    (c : colour)
    (cR : colour → Int)
    (cG : colour → Int)
    (cB : colour → Int)
    (Z_lor : Int → Int → Int)
    (h1 : (Z_lor ((cG c) * 256) ((cR c) * 65536)) = (((cR c) * 65536) + ((cG c) * 256)))
    (h2 : (Z_lor (((cR c) * 65536) + ((cG c) * 256)) (cB c)) = ((((cR c) * 65536) + ((cG c) * 256)) + (cB c))) :
    ((((cR c) * 256) + (cG c)) * (2 ^ (8 : Nat))) = (((cR c) * 65536) + ((cG c) * 256)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI4b.v (replace)
example
    {cht : Type}
    (C : cht)
    (T' : Int)
    (p1 : Int)
    (x1 : Int)
    (ch_c : cht → Int)
    (alloc_ceiling : Int)
    (h1 : (p1 ≠ 0 → (4096 ≤ p1 ∧ (p1 + (3 * T')) ≤ alloc_ceiling)))
    (h2 : (x1 ≠ 0 → (4096 ≤ x1 ∧ (x1 + (4 * T')) ≤ alloc_ceiling))) :
    ((ch_c C) + 0) = (ch_c C) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI4h.v (replace)
example
    (flt : Int)
    (fmt : Int)
    (i : Int)
    (M : Int)
    (beffmt : Int)
    (N_1 : Int)
    (h1 : (0 ≤ (4 * (fmt * i)) ∧ ((4 * (fmt * i)) + 12) ≤ (4 * M)))
    (h2 : (0 ≤ (beffmt * i) ∧ ((beffmt * i) + 3) ≤ (beffmt * N_1)))
    (h3 : (flt % 4) = 0)
    (h4 : ((flt + (4 * (fmt * i))) % 4) = 0) :
    (flt + ((fmt * i) * 4)) = (flt + (4 * (fmt * i))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI4p.v (replace)
example
    {T1 : Type}
    (imgl : T1)
    (fmt : Int)
    (N_1 : Int)
    (i : Int)
    (zlen : T1 → Int)
    (h1 : (zlen imgl) = (fmt * N_1))
    (h2 : (fmt = 3 ∨ fmt = 4))
    (h3 : (0 ≤ i ∧ i < N_1)) :
    (fmt * i) = ((fmt * i) + 0) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI4s.v (replace)
example
    {T1 : Type}
    (spZ : T1 → Int)
    (regs0 : T1)
    (N_1 : Int)
    (sp : T1 → Int)
    (h1 : 1 ≤ N_1)
    (h2 : ((sp regs0) % 16) = 0) :
    ((spZ regs0) + ((-321) * 16)) = ((spZ regs0) - 5136) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YI51.v (replace)
example
    {T1 T2 : Type}
    (sp0 : Int)
    (kk : Nat)
    (k : Nat)
    (spZ : T1 → Int)
    (ms_regs : T2 → T1)
    (msx : T2)
    (h1 : ((sp0 - 128) % 16) = 0)
    (h2 : ((sp0 - 96) % 8) = 0)
    (h3 : ((sp0 - 120) % 8) = 0)
    (h4 : 1 ≤ k)
    (h5 : (spZ (ms_regs msx)) = (sp0 - 128)) :
    (((sp0 - 120) + 16) + ((kk : Nat) : Int)) = ((sp0 - 104) + ((kk : Nat) : Int)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YK14.v (lemma)
example (a : Int) (e : Int) (h1 : 0 ≤ a) (h2 : a ≤ 1024) (h3 : 0 ≤ e) (h4 : e ≤ 256) :
    (((8 + ((a + 1) * 8)) + ((e + 1) * 8)) + 160) ≤ 10424 := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YK14.v (lemma)
example (a : Int) (b : Int) (h1 : a ≤ 10424) (h2 : b ≤ 2097152) :
    (a + b) ≤ 2107576 := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YK14.v (lemma)
example
    (s : Int)
    (m : Int)
    (h1 : 0 ≤ s)
    (h2 : 0 ≤ m)
    (h3 : m ≤ 2107576)
    (h4 : (s + 4300000) < (2 ^ (64 : Nat))) :
    (0 ≤ (s + m) ∧ (s + m) < (2 ^ (64 : Nat))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YL0k.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (a : Int)
    (ptr_addr : T1 → T2 → Int)
    (L : T1)
    (q : T2)
    (dst : Int)
    (pl : Int)
    (src : Int)
    (length : T3 → Nat)
    (bs : T3)
    (bv_unsigned : T4 → Int)
    (Z_to_bv : Int → Int → T4)
    (src2segs : T5)
    (ms_mem : T6 → T7)
    (ms : T6)
    (store_ok : T5 → T7 → T4 → Nat → Bool)
    (h1 : ((dst + pl) ≤ src ∨ (src + pl) ≤ dst))
    (h2 : (length bs) = (Int.toNat pl))
    (h3 : (bv_unsigned (Z_to_bv 64 dst)) = dst)
    (h4 : (bv_unsigned (Z_to_bv 64 src)) = src)
    (h5 : (bv_unsigned (Z_to_bv 64 pl)) = (((length bs) : Nat) : Int))
    (h6 : (store_ok src2segs (ms_mem ms) (Z_to_bv 64 dst) (length bs)) = true) :
    a = ((ptr_addr L q) + (a - (ptr_addr L q))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YM02.v (replace)
example
    {T1 : Type}
    (e : Int)
    (n : Int)
    (m : Int)
    (Zpow : Int → Int → Int)
    (fp_prec : T1 → Int)
    (D : T1)
    (h1 : (n - (m * (Zpow 2 e))) = 0)
    (h2 : (-53) ≤ e)
    (h3 : ((((n * (Zpow 2 (-e))) - m)).natAbs : Int) < (Zpow 2 (fp_prec D))) :
    0 = (e + (-e)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YM02.v (replace)
example
    {T1 : Type}
    (e : Int)
    (n : Int)
    (m : Int)
    (Zpow : Int → Int → Int)
    (fp_prec : T1 → Int)
    (D : T1)
    (h1 : (n - (m * (Zpow 2 e))) = 0)
    (h2 : (-53) ≤ e)
    (h3 : ((((n * (Zpow 2 (-e))) - m)).natAbs : Int) < (Zpow 2 (fp_prec D))) :
    0 = ((-e) + e) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YM02.v (replace)
example (N_1 : Int) (h1 : 0 ≤ N_1) (h2 : ((N_1).natAbs : Int) ≤ ((2 ^ (51 : Nat)) + 1)) :
    (((2 ^ (52 : Nat)) + N_1) - (2 ^ (52 : Nat))) = N_1 := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YM05.v (replace)
example
    (n : Int)
    (e1 : Int)
    (ex : Int)
    (mx : Int)
    (d : Int)
    (Zpow : Int → Int → Int)
    (m1 : Int)
    (prec : Int)
    (emin : Int)
    (h1 : 0 ≤ n)
    (h2 : (mx = 0 ∨ ((Zpow 2 (d - 1)) ≤ mx ∧ mx < (Zpow 2 d))))
    (h3 : 0 ≤ d)
    (h4 : m1 < (Zpow 2 prec))
    (h5 : (Zpow 2 d) = ((Zpow 2 n) * (Zpow 2 (d - n))))
    (h6 : ((Zpow 2 (prec - 1)) ≤ m1 ∨ e1 = emin))
    (h7 : e1 = ((d + ex) - prec))
    (h8 : n = (d - prec))
    (h9 : (Zpow 2 (d - 1)) = ((Zpow 2 n) * (Zpow 2 (prec - 1)))) :
    n = (e1 - ex) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YM07.v (replace)
example
    (n : Int)
    (prec : Int)
    (Zpow : Int → Int → Int)
    (Z_sgn : Int → Int)
    (h1 : ((n).natAbs : Int) ≤ (Zpow 2 prec))
    (h2 : n = (((Z_sgn n) * (Zpow 2 (prec - 1))) * 2)) :
    ((prec - 1) + 1) = prec := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO0f.v (replace)
example
    {T1 T2 : Type}
    (x : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (getr : T2 → Int → T1)
    (regs : T2)
    (n : Int)
    (dlen : Int → Int)
    (Z_to_bv : Int → Int → T1)
    (g : Int)
    (ctr64 : Int)
    (h1 : 4096 ≤ (bv_unsigned a))
    (h2 : (bv_unsigned (getr regs 10)) = n)
    (h3 : (((bv_unsigned a) + 131072) ≤ 135168 ∨ 339968 ≤ (bv_unsigned a)))
    (h4 : (bv_unsigned (Z_to_bv 64 g)) = g)
    (h5 : ((g + 40) ≤ 135168 ∨ 339968 ≤ g))
    (h6 : ((g + 40) ≤ (bv_unsigned a) ∨ ((bv_unsigned a) + (dlen n)) ≤ g))
    (h7 : (0 ≤ ctr64 ∧ ctr64 < (2 ^ (64 : Nat)))) :
    x = ((bv_unsigned a) + (x - (bv_unsigned a))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO0f.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (a : T1)
    (getr : T2 → Int → T1)
    (regs : T2)
    (n : Int)
    (dlen : Int → Int)
    (Z_to_bv : Int → Int → T1)
    (g : Int)
    (mp : Int)
    (ctr64 : Int)
    (stride : Int → Int → Int → Int)
    (h1 : 4096 ≤ (bv_unsigned a))
    (h2 : (bv_unsigned (getr regs 10)) = n)
    (h3 : (((bv_unsigned a) + 131072) ≤ 135168 ∨ 339968 ≤ (bv_unsigned a)))
    (h4 : (bv_unsigned (Z_to_bv 64 g)) = g)
    (h5 : ((g + 40) ≤ 135168 ∨ 339968 ≤ g))
    (h6 : ((g + 40) ≤ (bv_unsigned a) ∨ ((bv_unsigned a) + (dlen n)) ≤ g))
    (h7 : (0 ≤ ctr64 ∧ ctr64 < (2 ^ (64 : Nat))))
    (h8 : ((0 : Int) ≤ 0 ∧ (0 : Int) < 32))
    (h9 : ((0 : Int) ≤ 63 ∧ (63 : Int) < 64))
    (h10 : (0 ≤ mp ∧ mp < (2 ^ (52 : Nat))))
    (h11 : (0 ≤ n ∧ (n + 4) ≤ (stride 0 mp 0)))
    (h12 : (16 ≤ (bv_unsigned a) ∧ ((((bv_unsigned a) + 16) + ((stride 0 mp 0) * 0)) + (stride 0 mp 0)) ≤ (2 ^ (63 : Nat))))
    (h13 : (((stride 0 mp 0) * 0) + (((stride 0 mp 0) - 4) - n)) < (2 ^ (20 : Nat))) :
    ((bv_unsigned a) + 12) = (((bv_unsigned a) + 16) - 4) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO0l.v (replace)
example
    {T1 : Type}
    (am_sc : T1 → Int)
    (am : T1)
    (am_maplen : T1 → Int)
    (am_last : T1 → Int)
    (am_avail : T1 → Int)
    (am_freed : T1 → Int)
    (meta_bits : T1 → Int)
    (h1 : (am_avail am) < (2 ^ (32 : Nat)))
    (h2 : (am_freed am) < (2 ^ (32 : Nat)))
    (h3 : (0 ≤ (am_sc am) ∧ (am_sc am) < 64))
    (h4 : (0 ≤ (am_maplen am) ∧ (am_maplen am) < (2 ^ (40 : Nat))))
    (h5 : ((meta_bits am) / 32) = (1 + (2 * ((am_sc am) + (64 * (am_maplen am)))))) :
    (((1 + (2 * ((am_sc am) + (64 * (am_maplen am))))) * 32) + (am_last am)) = ((((am_last am) + 32) + (64 * (am_sc am))) + (4096 * (am_maplen am))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO0l.v (replace)
example
    {T1 : Type}
    (am_sc : T1 → Int)
    (am : T1)
    (am_maplen : T1 → Int)
    (am_avail : T1 → Int)
    (am_freed : T1 → Int)
    (meta_bits : T1 → Int)
    (h1 : (am_avail am) < (2 ^ (32 : Nat)))
    (h2 : (am_freed am) < (2 ^ (32 : Nat)))
    (h3 : (0 ≤ (am_sc am) ∧ (am_sc am) < 64))
    (h4 : (0 ≤ (am_maplen am) ∧ (am_maplen am) < (2 ^ (40 : Nat))))
    (h5 : ((meta_bits am) / 32) = (1 + (2 * ((am_sc am) + (64 * (am_maplen am)))))) :
    (1 + (((am_sc am) + (64 * (am_maplen am))) * 2)) = (1 + (2 * ((am_sc am) + (64 * (am_maplen am))))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO0z.v (replace)
example {frame : Type} (fr : frame) (n : Int) (fr_off : frame → Int) :
    (((16 * (fr_off fr)) + 4115) + n) = (((((n + (16 * (fr_off fr))) + 16) + 4) + 4096) - 1) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO17.v (replace)
example
    (RET : Int)
    (P : Int)
    (i : Int)
    (k : Nat)
    (NEEDED : Int)
    (alloc_ceiling : Int)
    (h1 : 4096 ≤ RET)
    (h2 : (RET + NEEDED) ≤ alloc_ceiling)
    (h3 : (RET % 16) = 0) :
    (((P - 4) + i) + ((k : Nat) : Int)) = ((P - 4) + (i + ((k : Nat) : Int))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO1l.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (ly_reg : T1 → T2 → Int)
    (L' : T1)
    (ra : T2)
    (oa : Int)
    (k : Int)
    (ASF : Int)
    (regs1 : T3)
    (sp : Int)
    (spZ : T3 → Int)
    (snd : T4 → T5)
    (r : T4)
    (alloc_ceiling : Int)
    (ptr_addr : T1 → T6 → Int)
    (m : T6)
    (META_SIZE : Int)
    (handed : T5 → T7 → Int)
    (a : T7)
    (METAS_PER_AREA : Int)
    (h1 : ASF = 384)
    (h2 : (spZ regs1) = (sp - 144))
    (h3 : (4096 ≤ (ptr_addr L' m) ∧ (((ptr_addr L' m) + META_SIZE) ≤ alloc_ceiling ∧ ((ptr_addr L' m) % 8) = 0)))
    (h4 : (handed (snd r) a) ≤ METAS_PER_AREA) :
    (((((512 * ((ly_reg L' ra) / 4096)) + (512 * (oa / 4096))) + 3) + (5 * k)) * 8) = (((4096 * ((ly_reg L' ra) / 4096)) + (4096 * (oa / 4096))) + (24 + (40 * k))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO2z.v (replace)
example
    {ameta frame : Type}
    (am : ameta)
    (fr : frame)
    (n : Int)
    (RET : Int)
    (i : Int)
    (k : Nat)
    (am_sc : ameta → Int)
    (MMAP_THRESHOLD : Int)
    (fr_n : frame → Int)
    (PGSZ : Int)
    (OLDLEN : Int)
    (NEEDED : Int)
    (alloc_ceiling : Int)
    (h1 : (am_sc am) = 63)
    (h2 : MMAP_THRESHOLD < (fr_n fr))
    (h3 : (((fr_n fr) + PGSZ) ≤ n ∧ n < (2 ^ (62 : Nat))))
    (h4 : OLDLEN ≠ NEEDED)
    (h5 : (Int.fmod RET PGSZ) = 0)
    (h6 : 0 < RET)
    (h7 : (RET + NEEDED) ≤ alloc_ceiling)
    (h8 : 0 ≤ i) :
    (RET + (i + ((k : Nat) : Int))) = ((RET + i) + ((k : Nat) : Int)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO2z.v (replace)
example
    {ameta frame T3 T4 : Type}
    (am : ameta)
    (fr : frame)
    (n : Int)
    (RET : Int)
    (MEM : Int)
    (fr_off : frame → Int)
    (am_sc : ameta → Int)
    (MMAP_THRESHOLD : Int)
    (fr_n : frame → Int)
    (PGSZ : Int)
    (OLDLEN : Int)
    (NEEDED : Int)
    (alloc_ceiling : Int)
    (P' : Int)
    (ly_reg : T3 → T4 → Int)
    (L' : T3)
    (r' : T4)
    (h1 : (am_sc am) = 63)
    (h2 : MMAP_THRESHOLD < (fr_n fr))
    (h3 : (((fr_n fr) + PGSZ) ≤ n ∧ n < (2 ^ (62 : Nat))))
    (h4 : OLDLEN ≠ NEEDED)
    (h5 : (Int.fmod RET PGSZ) = 0)
    (h6 : 0 < RET)
    (h7 : (RET + NEEDED) ≤ alloc_ceiling)
    (h8 : (((ly_reg L' r') + 16) + (16 * (fr_off fr))) = P') :
    (((MEM + 16) + (16 * (fr_off fr))) - 4) = (MEM + ((16 + (16 * (fr_off fr))) - 4)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO2z.v (replace)
example
    {ameta frame T3 T4 : Type}
    (am : ameta)
    (fr : frame)
    (n : Int)
    (RET : Int)
    (G : Int)
    (j : Nat)
    (am_sc : ameta → Int)
    (MMAP_THRESHOLD : Int)
    (fr_n : frame → Int)
    (PGSZ : Int)
    (OLDLEN : Int)
    (NEEDED : Int)
    (alloc_ceiling : Int)
    (P' : Int)
    (ly_reg : T3 → T4 → Int)
    (L' : T3)
    (r' : T4)
    (fr_off : frame → Int)
    (h1 : (am_sc am) = 63)
    (h2 : MMAP_THRESHOLD < (fr_n fr))
    (h3 : (((fr_n fr) + PGSZ) ≤ n ∧ n < (2 ^ (62 : Nat))))
    (h4 : OLDLEN ≠ NEEDED)
    (h5 : (Int.fmod RET PGSZ) = 0)
    (h6 : 0 < RET)
    (h7 : (RET + NEEDED) ≤ alloc_ceiling)
    (h8 : (((ly_reg L' r') + 16) + (16 * (fr_off fr))) = P') :
    (G + (8 + ((j : Nat) : Int))) = ((G + 8) + ((j : Nat) : Int)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO2z.v (replace)
example
    {ameta frame : Type}
    (am : ameta)
    (fr : frame)
    (n : Int)
    (RET : Int)
    (i : Int)
    (OFF : Int)
    (am_sc : ameta → Int)
    (MMAP_THRESHOLD : Int)
    (fr_n : frame → Int)
    (PGSZ : Int)
    (OLDLEN : Int)
    (NEEDED : Int)
    (alloc_ceiling : Int)
    (NOLD : Int)
    (h1 : (am_sc am) = 63)
    (h2 : MMAP_THRESHOLD < (fr_n fr))
    (h3 : (((fr_n fr) + PGSZ) ≤ n ∧ n < (2 ^ (62 : Nat))))
    (h4 : OLDLEN ≠ NEEDED)
    (h5 : (Int.fmod RET PGSZ) = 0)
    (h6 : 0 < RET)
    (h7 : (RET + NEEDED) ≤ alloc_ceiling)
    (h8 : (0 ≤ i ∧ i < NOLD)) :
    (RET + ((16 + (16 * OFF)) + i)) = (((RET + 16) + (16 * OFF)) + i) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO3t.v (replace)
example
    {list_byte word T3 T4 : Type}
    (s : list_byte)
    (p : word)
    (n : word)
    (sp : word)
    (SP : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (src2segs : T3)
    (mem : T4)
    (Z_to_bv : Int → Int → word)
    (store_ok : T3 → T4 → word → Int → Bool)
    (src2_D_const_ONES_0x0101010101010100 : Int)
    (src2_D_const_HIGHS_0x8080808080808080 : Int)
    (h1 : (((bv_unsigned p) + (((length s) : Nat) : Int)) + 8) < (2 ^ (64 : Nat)))
    (h2 : ((((length s) : Nat) : Int) + 8) ≤ (bv_unsigned n))
    (h3 : 0 < (bv_unsigned p))
    (h4 : (store_ok src2segs mem (Z_to_bv 64 ((bv_unsigned sp) - 24)) 24) = true)
    (h5 : (((((bv_unsigned p) + (((length s) : Nat) : Int)) - (((bv_unsigned p) + (((length s) : Nat) : Int)) % 8)) + 8) ≤ ((bv_unsigned sp) - 24) ∨ (bv_unsigned sp) ≤ (bv_unsigned p)))
    (h6 : ((src2_D_const_ONES_0x0101010101010100 + 8) ≤ ((bv_unsigned sp) - 24) ∨ (bv_unsigned sp) ≤ src2_D_const_HIGHS_0x8080808080808080))
    (h7 : 32 ≤ (bv_unsigned sp))
    (h8 : (0 ≤ ((bv_unsigned p) % 8) ∧ ((bv_unsigned p) % 8) < 8))
    (h9 : (0 ≤ (((bv_unsigned p) + (((length s) : Nat) : Int)) % 8) ∧ (((bv_unsigned p) + (((length s) : Nat) : Int)) % 8) < 8))
    (h10 : (((bv_unsigned p) + (((length s) : Nat) : Int)) % 8) ≤ ((bv_unsigned p) + (((length s) : Nat) : Int))) :
    SP = ((SP - 32) + 32) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YO3v.v (replace)
example
    {T1 T2 : Type}
    (E : T1)
    (a : T2)
    (U : T1 → T2 → Int)
    (M64 : Int)
    (h1 : (M64 - (2 ^ (31 : Nat))) ≤ (U E a)) :
    ((((U E a) - (((2 ^ (32 : Nat)) - 1) * (2 ^ (32 : Nat)))) + (2 ^ (31 : Nat))) - (2 ^ (32 : Nat))) = ((((U E a) - (((2 ^ (32 : Nat)) - 1) * (2 ^ (32 : Nat)))) + (2 ^ (31 : Nat))) + ((-1) * (2 ^ (32 : Nat)))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YP16.v (replace)
example (hi : Int) (lo : Int) :
    ((hi - 1) + 1) = (lo + (((hi - 1) - lo) + 1)) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YQ09.v (replace)
example
    {T1 T2 T3 : Type}
    (base_val : T1 → T2 → Int)
    (E : T1)
    (b : T2)
    (c_off : T3 → Int)
    (c : T3)
    (k : Int)
    (i : Nat) :
    ((((base_val E b) + (c_off c)) + k) + ((i : Nat) : Int)) = (((base_val E b) + (c_off c)) + (k + ((i : Nat) : Int))) := by
  lia

-- cgif/cgif_rgb_fuzzer: lib/YQ0j.v (replace)
example (m : Int) :
    (Int.fmod m (2 ^ (64 : Nat))) = (((Int.fmod m (2 ^ (64 : Nat))) - (2 ^ (64 : Nat))) + (1 * (2 ^ (64 : Nat)))) := by
  lia

-- cjson/cjson_read_fuzzer: lib/A/CJ_pv_common.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (Q : T2)
    (Z_to_bv : Int → Int → T1)
    (q_SA : T2 → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 (q_SA Q))) = (q_SA Q)) :
    ((bv_unsigned sp) + (-16)) = (((bv_unsigned sp) + (-120)) + ((104 : Nat) : Int)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/A/DrvTop.v (replace)
example
    {word list_byte T3 : Type}
    (sp : word)
    (lo : Int)
    (SPB : Int)
    (P1 : Int)
    (tid : word)
    (path : list_byte)
    (slack : list_byte)
    (data : list_byte)
    (until_1 : Int)
    (a2' : Int)
    (cap : Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (zlength : list_byte → Int)
    (length : T3 → Nat)
    (firstn : Nat → list_byte → T3)
    (h1 : (lo + (2 ^ (22 : Nat))) ≤ ((bv_unsigned sp) + 80))
    (h2 : alloc_ceiling ≤ lo)
    (h3 : ((bv_unsigned sp) + 128) ≤ (2 ^ (47 : Nat)))
    (h4 : SPB = ((bv_unsigned sp) + 80))
    (h5 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h6 : ((-((P1 + (zlength path)) + 1)) % 8) ≤ (zlength slack))
    (h7 : (zlength path) ≤ 131071)
    (h8 : ((bv_unsigned sp) + 128) ≤ P1)
    (h9 : ((((P1 + (zlength path)) + 1) + (zlength slack)) + 16) ≤ (2 ^ (47 : Nat)))
    (h10 : ((zlength data) - until_1) < a2')
    (h11 : (2 ^ (26 : Nat)) ≤ cap)
    (h12 : cap < (2 ^ (26 : Nat)))
    (h13 : (length (firstn (Int.toNat cap) data)) = (Int.toNat cap)) :
    (Int.toNat cap) = (Int.toNat ((cap * 2) - cap)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/A/DrvTop.v (replace)
example
    {word list_byte T3 : Type}
    (sp : word)
    (lo : Int)
    (SPB : Int)
    (P1 : Int)
    (tid : word)
    (path : list_byte)
    (slack : list_byte)
    (data : list_byte)
    (want : Int)
    (cap : Int)
    (n : Int)
    (len : Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (zlength : list_byte → Int)
    (length : T3 → Nat)
    (bs : T3)
    (h1 : (lo + (2 ^ (22 : Nat))) ≤ ((bv_unsigned sp) + 80))
    (h2 : alloc_ceiling ≤ lo)
    (h3 : ((bv_unsigned sp) + 128) ≤ (2 ^ (47 : Nat)))
    (h4 : SPB = ((bv_unsigned sp) + 80))
    (h5 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h6 : ((-((P1 + (zlength path)) + 1)) % 8) ≤ (zlength slack))
    (h7 : (zlength path) ≤ 131071)
    (h8 : ((bv_unsigned sp) + 128) ≤ P1)
    (h9 : ((((P1 + (zlength path)) + 1) + (zlength slack)) + 16) ≤ (2 ^ (47 : Nat)))
    (h10 : (((length bs) : Nat) : Int) = (min want ((zlength data) - len)))
    (h11 : (0 ≤ n ∧ n ≤ want))
    (h12 : 0 < n)
    (h13 : (len + n) = cap) :
    cap = (n + len) := by
  lia

-- cjson/cjson_read_fuzzer: lib/A/F_vfscanf_B_b.v (replace)
example
    {list_Z : Type}
    (q : Int)
    (T : Int)
    (txt : list_Z)
    (PD : Int)
    (zlength : list_Z → Int)
    (VF_DEPTH : Int)
    (h1 : ((T + (zlength txt)) % 8) = 0)
    (h2 : (zlength txt) ≤ 256)
    (h3 : 0 ≤ (max ((q - 11440) - (T + (zlength txt))) (T - (q + 408))))
    (h4 : (T + (2 ^ (41 : Nat))) ≤ (2 ^ (63 : Nat)))
    (h5 : 6287360 ≤ (q - VF_DEPTH))
    (h6 : (q + 408) < (2 ^ (62 : Nat)))
    (h7 : 0 ≤ (max ((q - 11440) - (PD + 8)) (PD - (q + 408))))
    (h8 : (PD + 8) ≤ (2 ^ (63 : Nat)))
    (h9 : ((PD + 8) ≤ T ∨ (T + (zlength txt)) ≤ PD))
    (h10 : (6287360 ≤ PD ∧ ((PD + 8) ≤ 2147446784 ∨ 17594333495296 ≤ PD)))
    (h11 : 4096 ≤ T)
    (h12 : 6287360 ≤ T) :
    ((q + (-480)) - 2464) = ((q + (-480)) - 2464) := by
  lia

-- cjson/cjson_read_fuzzer: lib/A/RTW_depot_nstore.v (replace)
example
    {T1 : Type}
    (q : Int)
    (B0 : Int)
    (zlen : T1 → Int)
    (sbl : T1)
    (c : Int)
    (T : Int)
    (h1 : (0 ≤ B0 ∧ B0 ≤ (zlen sbl)))
    (h2 : B0 = (zlen sbl))
    (h3 : B0 = ((zlen sbl) - 1))
    (h4 : (((c + (-1)) + T) / 1048576) = (B0 + 1))
    (h5 : (T % 1048576) ≠ 0)
    (h6 : ((q + 24) % 4) = 0)
    (h7 : ((q + 40) % 4) = 0)
    (h8 : (0 ≤ q ∧ (q + 48) < (2 ^ (64 : Nat)))) :
    (q + 16) = (1556824 + (16 * B0)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/AMainGlue.v (replace)
example
    {list_list_byte : Type}
    (argv : list_list_byte)
    (envp : list_list_byte)
    (length : list_list_byte → Nat)
    (T : Nat)
    (U : Nat) :
    (((8 + ((8 * (length argv)) + (8 + ((8 * (length envp)) + (8 + (160 + (T + U))))))) : Nat) : Int) = (((((((8 + (((length argv) + 1) * 8)) + (((length envp) + 1) * 8)) + 160) : Nat) : Int) + ((T : Nat) : Int)) + ((U : Nat) : Int)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/CJ_pvalue_lemmas.v (replace)
example (U : Int) :
    (U + 64) = (U + (max 64 1)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/CJ_pwlopts_A.v (replace)
example
    {T1 : Type}
    (Fr : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (SA : Int)
    (P : Int)
    (h1 : ((((bv_unsigned sp) - 240) ≤ SA ∧ SA ≤ ((bv_unsigned sp) - 224)) ∧ (SA % 32) = 0))
    (h2 : Fr ≠ (P - 32)) :
    (Fr + 64) = ((((Fr + 8) + 24) + 8) + 24) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/CJ_pwlopts_A.v (replace)
example (a : Int) (n1 : Int) (n2 : Int) :
    (((a + n1) + n2) - 1) = ((a + (n1 + n2)) - 1) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/Drv_trunA.v (replace)
example
    (a : Int)
    (n : Int)
    (SH : Int → Int)
    (i : Int)
    (ARS : Int)
    (AIMG_LO : Int)
    (AIMG_HI : Int)
    (alowsh : Int → Int)
    (h1 : ARS ≤ a)
    (h2 : 0 < n)
    (h3 : (a + n) ≤ (ARS + 65536))
    (h4 : (SH AIMG_LO) = 2147459072)
    (h5 : (SH AIMG_HI) = 2148236800)
    (h6 : (2148210690 ≤ (SH (a + i)) ∧ (SH (a + i)) < (2148210690 + 8192)))
    (h7 : (alowsh (SH (a + i))) = 0) :
    (SH (a + i)) = (2148210690 + ((SH (a + i)) - 2148210690)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/F_floatscan_A1.v (replace)
example
    (z : Int)
    (a : Int)
    (kk : Int)
    (h_1 : Bool)
    (h1 : kk = ((a + 1) % 2048))
    (h2 : ((z + 1) % 2048) = ((a + 2) % 2048))
    (h3 : h_1 = true) :
    ((z - a) + 1) = ((z + 1) - a) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/ICPT_scommon_lg.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (AQ : Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (ASC_STACK : Int)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : (lo + ASC_STACK) ≤ (bv_unsigned sp))
    (h3 : ((AQ + 8) ≤ lo ∨ (bv_unsigned sp) ≤ AQ))
    (h4 : (AQ + 8) ≤ (2 ^ (63 : Nat)))
    (h5 : 0 ≤ AQ) :
    (bv_unsigned sp) = ((((bv_unsigned sp) + (-2240)) + 208) + 2032) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/ICPT_str3.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (s : Int)
    (c : Int)
    (n : Int)
    (lo : Int)
    (buf : list_byte)
    (R : Int)
    (L : Int)
    (length : list_byte → Nat)
    (memchr_res : Int → Int → Int → list_byte → Int)
    (memchr_chk_len : Int → Int → Int → list_byte → Int)
    (alloc_ceiling : Int)
    (AINTRIN_STACK : Int)
    (bv_unsigned : word → Int)
    (h1 : (0 ≤ n ∧ n < (2 ^ (40 : Nat))))
    (h2 : (0 ≤ c ∧ c < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ s ∧ (s + (((length buf) : Nat) : Int)) < (2 ^ (47 : Nat))))
    (h4 : R = (memchr_res s (c % 256) n buf))
    (h5 : L = (memchr_chk_len s (c % 256) n buf))
    (h6 : alloc_ceiling ≤ lo)
    (h7 : (lo + AINTRIN_STACK) ≤ (bv_unsigned sp))
    (h8 : ((s + (((length buf) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ s)) :
    ((s + L) - 1) = ((s + L) + (-1)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/ICPT_strnlen.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (s : Int)
    (n : Int)
    (lo : Int)
    (buf : list_byte)
    (Lr : Int)
    (K : Int)
    (strnlen_res : Int → list_byte → Int)
    (memchr_chk_len : Int → Int → Int → list_byte → Int)
    (alloc_ceiling : Int)
    (ASTRNLEN_STACK : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : (0 ≤ n ∧ n < (2 ^ (40 : Nat))))
    (h2 : 0 < s)
    (h3 : Lr = (strnlen_res n buf))
    (h4 : K = (memchr_chk_len s 0 n buf))
    (h5 : alloc_ceiling ≤ lo)
    (h6 : (lo + ASTRNLEN_STACK) ≤ (bv_unsigned sp))
    (h7 : ((s + (((length buf) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ s)) :
    ((2147450880 + (s / 8)) + 0) = (2147450880 + (s / 8)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/ICPT_strnlen.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (s : Int)
    (n : Int)
    (lo : Int)
    (buf : list_byte)
    (Lr : Int)
    (K : Int)
    (strnlen_res : Int → list_byte → Int)
    (memchr_chk_len : Int → Int → Int → list_byte → Int)
    (alloc_ceiling : Int)
    (ASTRNLEN_STACK : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : (0 ≤ n ∧ n < (2 ^ (40 : Nat))))
    (h2 : 0 < s)
    (h3 : Lr = (strnlen_res n buf))
    (h4 : K = (memchr_chk_len s 0 n buf))
    (h5 : alloc_ceiling ≤ lo)
    (h6 : (lo + ASTRNLEN_STACK) ≤ (bv_unsigned sp))
    (h7 : ((s + (((length buf) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ s))
    (h8 : 0 < K) :
    ((s + K) - 1) = ((s + K) + (-1)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/ICPT_vsprintf2.v (replace)
example
    {word : Type}
    (sp : word)
    (D : Int)
    (lo : Int)
    (dn : Nat)
    (r : Int)
    (i : Int)
    (alloc_ceiling : Int)
    (AVSNI_STACK : Int)
    (bv_unsigned : word → Int)
    (h1 : (0 ≤ r ∧ ((r + 1) ≤ ((dn : Nat) : Int) ∧ ((dn : Nat) : Int) < (2 ^ (31 : Nat)))))
    (h2 : alloc_ceiling ≤ lo)
    (h3 : (lo + AVSNI_STACK) ≤ (bv_unsigned sp))
    (h4 : ((D + ((dn : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ D)) :
    ((2147450880 + (D / 8)) + (i + 1)) = (((2147450880 + (D / 8)) + i) + 1) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_depot_nstore.v (replace)
example
    {T1 : Type}
    (q : Int)
    (B0 : Int)
    (zlen : T1 → Int)
    (sbl : T1)
    (h1 : (0 ≤ B0 ∧ B0 ≤ (zlen sbl)))
    (h2 : B0 = (zlen sbl))
    (h3 : B0 = ((zlen sbl) - 1)) :
    (q + 16) = (1554584 + (16 * B0)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_m_asec.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (sec_user : Int → Int)
    (mb : Int)
    (sec_alloc_beg : Int → Int)
    (rounded8 : Int → Int)
    (n : Int)
    (smapsize : Int → Int)
    (usz : Int → Int)
    (h1 : (sec_user mb) = (mb + 6144))
    (h2 : (sec_alloc_beg mb) = (mb + 4096))
    (h3 : ((rounded8 n) + 8192) ≤ (smapsize n))
    (h4 : 1 ≤ (usz n))
    (h5 : n ≤ (usz n)) :
    (bv_unsigned sp) = (((bv_unsigned sp) - 128) + 128) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_m_cid.v (replace)
example (step : Int) (s : Int) (i : Int) :
    ((s + step) + (step * (i - 1))) = (s + (step * i)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_m_mallocN.v (replace)
example
    {T1 : Type}
    (r : Int)
    (rz_size : Int → Int)
    (n : Int)
    (usz : Int → Int)
    (csize : T1 → Int)
    (c : T1)
    (h1 : 1 ≤ (usz n))
    (h2 : n ≤ (usz n))
    (h3 : (rz_size n) = (8 * ((rz_size n) / 8)))
    (h4 : (1 ≤ (((usz n) + 7) / 8) ∧ ((8 * ((rz_size n) / 8)) + (8 * (((usz n) + 7) / 8))) ≤ ((csize c) + 7)))
    (h5 : (((csize c) / 8) * 8) = (csize c)) :
    r = ((r + (rz_size n)) - (rz_size n)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_abs.v (replace)
example
    (cls : Int)
    (n : Int)
    (Nv : Int)
    (um : Bool)
    (fm : Bool)
    (pop : Bool)
    (N_1 : Int)
    (i : Int)
    (k : Int)
    (nrefill : Int → Int)
    (nf : Int)
    (h1 : (1 ≤ cls ∧ cls ≤ 30))
    (h2 : n = (nrefill cls))
    (h3 : (0 ≤ Nv ∧ n ≤ (nf + Nv)))
    (h4 : (pop = false → (Nv = 0 ∧ (um = false ∧ fm = false))))
    (h5 : 0 ≤ i)
    (h6 : 0 ≤ k)
    (h7 : (i + k) ≤ N_1) :
    (i + (k + ((N_1 - i) - k))) = N_1 := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_abs.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (cls : Int)
    (n : Int)
    (Nv : Int)
    (um : Bool)
    (fm : Bool)
    (pop : Bool)
    (rb : Int)
    (mapped : Int)
    (nrefill : Int → Int)
    (nf : Int)
    (rinfo : T1 → Int → Int)
    (st : T1)
    (rinfo_cells : T2 → Int → T3 → T4 → T5 → T6)
    (st' : T2)
    (zlen : T7 → Int)
    (L : T7)
    (cells_size : T6 → Nat)
    (jr0 : T3)
    (je0 : T4)
    (js0 : T5)
    (ris : T1 → Int)
    (h1 : (1 ≤ cls ∧ cls ≤ 30))
    (h2 : n = (nrefill cls))
    (h3 : (0 ≤ Nv ∧ n ≤ (nf + Nv)))
    (h4 : (pop = false → (Nv = 0 ∧ (um = false ∧ fm = false))))
    (h5 : (zlen L) = (nf + Nv))
    (h6 : (((cells_size (rinfo_cells st' cls jr0 je0 js0)) : Nat) : Int) = 128)
    (h7 : (rinfo st cls) = ((ris st) + (128 * cls))) :
    ((rb + mapped) + 262144) = (rb + (mapped + 262144)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_finx.v (replace)
example
    {T1 word T3 : Type}
    (mapped : Int)
    (csize : T1 → Int)
    (c : T1)
    (bv_unsigned : word → Int)
    (wz : Int → word)
    (sp : word)
    (alloc : Int)
    (fam : Int)
    (SH : Int → Int)
    (RB : Int)
    (total : Int)
    (KFREEARRAY_OFF : Int)
    (KHIGHMEM_BEG : Int)
    (U : Int)
    (x : word)
    (in_winb : T3 → word → Bool)
    (G : T3)
    (h1 : 32 ≤ (csize c))
    (h2 : (bv_unsigned (wz ((bv_unsigned sp) + (-64)))) = ((bv_unsigned sp) + (-64)))
    (h3 : (32 * 16384) ≤ ((csize c) * 16384))
    (h4 : ((SH (RB + mapped)) + 32768) = (SH ((RB + mapped) + 262144)))
    (h5 : mapped < total)
    (h6 : (mapped + 262144) ≤ KFREEARRAY_OFF)
    (h7 : (KHIGHMEM_BEG ≤ U ∧ ((U + 262144) ≤ (RB + KFREEARRAY_OFF) ∧ (U % 32768) = 0)))
    (h8 : (((SH U) % 4096) = 0 ∧ (2147450880 ≤ (SH U) ∧ (((SH U) + 32768) ≤ 17594333495296 ∧ (SH (U + 262144)) = ((SH U) + 32768)))))
    (h9 : (((SH (RB + mapped)) % 4096) = 0 ∧ (2147450880 ≤ (SH (RB + mapped)) ∧ ((SH (RB + mapped)) + 32768) ≤ 17594333495296)))
    (h10 : ((SH RB) ≤ (bv_unsigned x) ∧ (bv_unsigned x) < (SH (RB + (2 ^ (32 : Nat))))))
    (h11 : fam = 0)
    (h12 : (in_winb G x) = true)
    (h13 : (0 ≤ (Int.fdiv ((mapped + 262144) - alloc) (csize c)) ∧ (Int.fdiv ((mapped + 262144) - alloc) (csize c)) ≤ 16385))
    (h14 : ((SH ((RB + 3758096384) + fam)) + 32768) ≤ 17594333495296)
    (h15 : (SH ((RB + mapped) + 262144)) ≤ (SH ((RB + 3758096384) + fam)))
    (h16 : ((SH U) + 32768) = (SH ((RB + mapped) + 262144)))
    (h17 : total ≤ mapped) :
    mapped = (mapped + 0) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_finx.v (replace)
example (N_1 : Nat) :
    N_1 = (((N_1 + 1) - 1) - 0) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_finx.v (replace)
example (N_1 : Nat) (t : Nat) :
    ((N_1 - 1) - t) = (((N_1 + 1) - 1) - (t + 1)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_loops.v (replace)
example (P : Int) (i : Int) :
    ((P + (80 * (i + 1))) + 8) = ((P + (80 * i)) + 88) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_pop1.v (replace)
example (lo : Int) (k : Nat) :
    (lo + ((k : Nat) : Int)) = (lo + (((0 + k) : Nat) : Int)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_refillX.v (replace)
example
    {T1 : Type}
    (NB : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (h1 : NB = ((bv_unsigned sp) + (-328))) :
    NB = (((bv_unsigned sp) + (-336)) + 8) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_p_refillX.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    (((bv_unsigned sp) + (-56)) + 16) = ((((bv_unsigned sp) + (-56)) + 8) + ((8 : Nat) : Int)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_q_top.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (b_lo : T2 → T3 → Int)
    (A : T2)
    (n : T3)
    (st : T4)
    (qcache_t : T4 → Int)
    (alloc_ceiling : Int)
    (h1 : ((b_lo A n) % 8) = 0)
    (h2 : ((4096 ≤ ((qcache_t st) - 80) ∧ (((qcache_t st) + 4016) ≤ 65536 ∨ 6287360 ≤ ((qcache_t st) - 80))) ∧ ((qcache_t st) + 32) ≤ alloc_ceiling)) :
    (bv_unsigned sp) = (((bv_unsigned sp) - 64) + 64) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_q_top.v (replace)
example
    {word rtstate T3 : Type}
    (bv_unsigned : word → Int)
    (sp : word)
    (Sx : Int)
    (wz : Int → word)
    (acache : rtstate → Int)
    (st : rtstate)
    (usz : T3 → Int)
    (n : T3)
    (CEIL : Int)
    (h1 : (0 ≤ Sx ∧ Sx < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ (acache st) ∧ (acache st) < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ (usz n) ∧ (usz n) < (2 ^ (64 : Nat))))
    (h4 : CEIL ≤ (bv_unsigned sp))
    (h5 : (bv_unsigned (wz ((bv_unsigned sp) - 80))) = ((bv_unsigned sp) - 80)) :
    (bv_unsigned sp) = (((bv_unsigned sp) - 80) + 80) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_q_wf3.v (replace)
example {T1 : Type} (zlen : T1 → Int) (q : T1) (h1 : (1 : Int) ≤ 24) :
    ((zlen q) + 1) = ((zlen q) + (1 + 0)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_q_wf3.v (replace)
example (QBATCH_SIZE : Int) (n : Int) :
    (QBATCH_SIZE + (max n 1)) = ((QBATCH_SIZE + (max n 1)) + 0) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RTW_q_wf3.v (replace)
example
    {T1 T2 : Type}
    (zlen : T1 → Int)
    (pre : T1)
    (cch : T2 → Int → T1)
    (st : T2)
    (k : Int)
    (b : Int)
    (st_spacebeg : T2 → Int)
    (acache : T2 → Int)
    (alloc_ceiling : Int)
    (qcache_t : T2 → Int)
    (st_pbase : T2 → Int)
    (h1 : (zlen (cch st 24)) = ((zlen pre) + 1))
    (h2 : (0 ≤ k ∧ k < (2 ^ (28 : Nat))))
    (h3 : b = (((st_spacebeg st) + (24 * (2 ^ (32 : Nat)))) + (16 * k)))
    (h4 : (((acache st) + 2576) % 8) = 0)
    (h5 : (1 ≤ ((zlen pre) + 1) ∧ ((zlen pre) + 1) ≤ 16))
    (h6 : ((16 ≤ (acache st) ∧ (((acache st) + 3888) ≤ 65536 ∨ 6287360 ≤ ((acache st) - 208))) ∧ (((acache st) + 2584) ≤ alloc_ceiling ∧ (16 ≤ (qcache_t st) ∧ (((qcache_t st) + 32) ≤ (acache st) ∧ ((acache st) - 208) ≤ (qcache_t st))))))
    (h7 : (0 ≤ (st_spacebeg st) ∧ ((((st_spacebeg st) + (2 ^ (37 : Nat))) + 4096) ≤ alloc_ceiling ∧ (0 ≤ (st_pbase st) ∧ (st_pbase st) < (2 ^ (64 : Nat)))))) :
    (((zlen pre) + 1) - 1) = (zlen pre) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RT_poison.v (replace)
example
    {word : Type}
    (sp : word)
    (b : Int)
    (n : Int)
    (lo : Int)
    (end_ : Int)
    (AB : Int)
    (AE : Int)
    (i : Int)
    (bv_unsigned : word → Int)
    (h1 : (0 < n ∧ n ≤ (2 ^ (40 : Nat))))
    (h2 : ((b + n) ≤ ((bv_unsigned sp) - 16) ∨ (bv_unsigned sp) ≤ b))
    (h3 : (lo + 16) ≤ (bv_unsigned sp))
    (h4 : ((b + n) + 16) ≤ (2 ^ (64 : Nat)))
    (h5 : end_ = (b + n))
    (h6 : AB = (((b + 7) / 8) * 8))
    (h7 : AE = (((b + n) / 8) * 8)) :
    ((end_ - AE) - (i + 1)) = (((end_ - AE) - i) + (-1)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RT_poison.v (replace)
example
    {word : Type}
    (sp : word)
    (b : Int)
    (n : Int)
    (lo : Int)
    (end_ : Int)
    (AB : Int)
    (AE : Int)
    (j : Int)
    (bv_unsigned : word → Int)
    (h1 : (0 < n ∧ n ≤ (2 ^ (40 : Nat))))
    (h2 : ((b + n) ≤ ((bv_unsigned sp) - 16) ∨ (bv_unsigned sp) ≤ b))
    (h3 : (lo + 16) ≤ (bv_unsigned sp))
    (h4 : ((b + n) + 16) ≤ (2 ^ (64 : Nat)))
    (h5 : end_ = (b + n))
    (h6 : AB = (((b + 7) / 8) * 8))
    (h7 : AE = (((b + n) / 8) * 8)) :
    (AB + (8 * (j + 1))) = ((AB + (8 * j)) + 8) := by
  lia

-- cjson/cjson_read_fuzzer: lib/B/RT_poison2.v (replace)
example
    (b : Int)
    (n : Int)
    (vb : Int)
    (ve : Int)
    (sb : Int)
    (se : Int)
    (SH : Int → Int)
    (h1 : (0 < n ∧ n < (2 ^ (40 : Nat))))
    (h2 : (vb = 0 ∨ ((b % 8) < vb ∧ vb < 8)))
    (h3 : (ve = 0 ∨ ((((b + n) - 1) % 8) < ve ∧ ve < 8)))
    (h4 : sb = (SH (((b + 7) / 8) * 8)))
    (h5 : se = (SH (((b + n) / 8) * 8))) :
    ((b + n) - 1) = ((b + n) + (-1)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/P/Drv_loop.v (replace)
example
    {word list_byte T3 : Type}
    (sp : word)
    (lo : Int)
    (SPB : Int)
    (P1 : Int)
    (tid : word)
    (path : list_byte)
    (slack : list_byte)
    (data : list_byte)
    (want : Int)
    (PRS : Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (zlength : list_byte → Int)
    (A : Int)
    (length : T3 → Nat)
    (bs : T3)
    (len : Int)
    (n : Int)
    (cap : Int)
    (h1 : (lo + (2 ^ (22 : Nat))) ≤ ((bv_unsigned sp) + 80))
    (h2 : alloc_ceiling ≤ lo)
    (h3 : ((bv_unsigned sp) + 128) ≤ 140737488355328)
    (h4 : SPB = ((bv_unsigned sp) + 128))
    (h5 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h6 : ((-((P1 + (zlength path)) + 1)) % 8) ≤ (zlength slack))
    (h7 : (zlength path) ≤ 131071)
    (h8 : ((bv_unsigned sp) + 128) ≤ P1)
    (h9 : 348160 ≤ A)
    (h10 : (((length bs) : Nat) : Int) = (min want ((zlength data) - len)))
    (h11 : (0 ≤ n ∧ n ≤ want))
    (h12 : 0 < n)
    (h13 : (len + n) = cap)
    (h14 : len = (zlength data))
    (h15 : n = 0)
    (h16 : (length bs) = 0) :
    (PRS + want) = (PRS + (((((Int.toNat want) - 0) + 0) : Nat) : Int)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/RL/G/G_floatscan_M.v (assert)
example
    {list_Z T2 : Type}
    (q : Int)
    (Fp : Int)
    (T : Int)
    (p : Int)
    (txt : list_Z)
    (pok : Int)
    (x0 : Int)
    (zlength : list_Z → Int)
    (znth : list_Z → Int → Int)
    (RERRNO : Int)
    (FS_DEPTH : Int)
    (ssp_guard : Int)
    (got_ssp : Int)
    (rp : Int)
    (Z_shiftr : Int → T2 → Int)
    (bitlim : T2)
    (h1 : (pok = 0 ∨ pok = 1))
    (h2 : (0 ≤ p ∧ p < (zlength txt)))
    (h3 : (znth txt p) = 0)
    (h4 : p ≤ 64)
    (h5 : 4096 ≤ T)
    (h6 : (T + (2 ^ (41 : Nat))) ≤ (2 ^ (63 : Nat)))
    (h7 : ((Fp + 232) ≤ T ∨ (T + (zlength txt)) ≤ Fp))
    (h8 : ((T + (zlength txt)) ≤ RERRNO ∨ (RERRNO + 4) ≤ T))
    (h9 : 4096 ≤ (q - FS_DEPTH))
    (h10 : q ≤ Fp)
    (h11 : (Fp + 232) ≤ (2 ^ (63 : Nat)))
    (h12 : ((T + (zlength txt)) ≤ (q - FS_DEPTH) ∨ q ≤ T))
    (h13 : (ssp_guard + 8) ≤ (q - FS_DEPTH))
    (h14 : ((T + (zlength txt)) ≤ got_ssp ∨ (got_ssp + 8) ≤ T))
    (h15 : ((T + (zlength txt)) ≤ ssp_guard ∨ (ssp_guard + 8) ≤ T))
    (h16 : q < (2 ^ (63 : Nat)))
    (h17 : (10 ≤ rp ∧ rp ≤ 17))
    (h18 : (rp = 10 ∨ (rp = 11 ∨ (rp = 12 ∨ (rp = 13 ∨ (rp = 14 ∨ (rp = 15 ∨ (rp = 16 ∨ rp = 17))))))))
    (h19 : 0 ≤ (Z_shiftr x0 bitlim))
    (h20 : (Z_shiftr x0 bitlim) ≤ x0) :
    0 ≤ x0 := by
  lia

-- cjson/cjson_read_fuzzer: lib/RL/G/G_floatscan_P.v (replace)
example
    {list_Z : Type}
    (q : Int)
    (Fp : Int)
    (T : Int)
    (p : Int)
    (txt : list_Z)
    (j : Int)
    (zlength : list_Z → Int)
    (znth : list_Z → Int → Int)
    (RERRNO : Int)
    (FS_DEPTH : Int)
    (ssp_guard : Int)
    (got_ssp : Int)
    (kz : Int)
    (Zpow : Int → Int → Int)
    (x : list_Z)
    (h1 : (0 ≤ p ∧ p < (zlength txt)))
    (h2 : (znth txt p) = 0)
    (h3 : p ≤ 64)
    (h4 : 4096 ≤ T)
    (h5 : (T + (2 ^ (41 : Nat))) ≤ (2 ^ (63 : Nat)))
    (h6 : ((Fp + 232) ≤ T ∨ (T + (zlength txt)) ≤ Fp))
    (h7 : ((T + (zlength txt)) ≤ RERRNO ∨ (RERRNO + 4) ≤ T))
    (h8 : 4096 ≤ (q - FS_DEPTH))
    (h9 : q ≤ Fp)
    (h10 : (Fp + 232) ≤ (2 ^ (63 : Nat)))
    (h11 : ((T + (zlength txt)) ≤ (q - FS_DEPTH) ∨ q ≤ T))
    (h12 : (ssp_guard + 8) ≤ (q - FS_DEPTH))
    (h13 : ((T + (zlength txt)) ≤ got_ssp ∨ (got_ssp + 8) ≤ T))
    (h14 : ((T + (zlength txt)) ≤ ssp_guard ∨ (ssp_guard + 8) ≤ T))
    (h15 : q < (2 ^ (63 : Nat)))
    (h16 : j = 0)
    (h17 : 1 ≤ kz)
    (h18 : j ≠ 0)
    (h19 : (Zpow 10 j) ≤ (10 ^ (8 : Nat)))
    (h20 : ((Zpow 10 j) * (Zpow 10 (9 - j))) = 1000000000)
    (h21 : 1 ≤ (Zpow 10 (9 - j)))
    (h22 : (0 ≤ ((znth x kz) * (Zpow 10 (9 - j))) ∧ ((znth x kz) * (Zpow 10 (9 - j))) < 1000000000)) :
    (j - 9) = (j + (-9)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/RL/G/G_floatscan_T.v (assert)
example
    {list_Z : Type}
    (q : Int)
    (Fp : Int)
    (T : Int)
    (p : Int)
    (txt : list_Z)
    (rpm9 : Int)
    (zlength : list_Z → Int)
    (znth : list_Z → Int → Int)
    (RERRNO : Int)
    (FS_DEPTH : Int)
    (ssp_guard : Int)
    (got_ssp : Int)
    (rp : Int)
    (r9 : Int)
    (h1 : (0 ≤ p ∧ p < (zlength txt)))
    (h2 : (znth txt p) = 0)
    (h3 : p ≤ 64)
    (h4 : 4096 ≤ T)
    (h5 : (T + (2 ^ (41 : Nat))) ≤ (2 ^ (63 : Nat)))
    (h6 : ((Fp + 232) ≤ T ∨ (T + (zlength txt)) ≤ Fp))
    (h7 : ((T + (zlength txt)) ≤ RERRNO ∨ (RERRNO + 4) ≤ T))
    (h8 : 4096 ≤ (q - FS_DEPTH))
    (h9 : q ≤ Fp)
    (h10 : (Fp + 232) ≤ (2 ^ (63 : Nat)))
    (h11 : ((T + (zlength txt)) ≤ (q - FS_DEPTH) ∨ q ≤ T))
    (h12 : (ssp_guard + 8) ≤ (q - FS_DEPTH))
    (h13 : ((T + (zlength txt)) ≤ got_ssp ∨ (got_ssp + 8) ≤ T))
    (h14 : ((T + (zlength txt)) ≤ ssp_guard ∨ (ssp_guard + 8) ≤ T))
    (h15 : q < (2 ^ (63 : Nat)))
    (h16 : (0 ≤ rp → 0 ≤ (Int.tmod rp 9)))
    (h17 : (rp ≤ 0 → (Int.tmod rp 9) ≤ 0))
    (h18 : ((-8) ≤ r9 ∧ r9 ≤ 8))
    (h19 : r9 = 0)
    (h20 : r9 ≠ 0) :
    (rpm9 = 1 ∨ (rpm9 = 2 ∨ (rpm9 = 3 ∨ (rpm9 = 4 ∨ (rpm9 = 5 ∨ (rpm9 = 6 ∨ (rpm9 = 7 ∨ rpm9 = 8))))))) := by
  lia

-- cjson/cjson_read_fuzzer: lib/RL/G/G_fmt_fp_r3.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (B : Int)
    (junk0 : list_byte)
    (t : Int)
    (bv_unsigned : word → Int)
    (d : Int)
    (sym : Int → Int)
    (Fp : Int)
    (Z_lor : Int → Nat → Int)
    (length : list_byte → Nat)
    (h1 : 5152 ≤ (bv_unsigned sp))
    (h2 : (bv_unsigned sp) < (2 ^ (63 : Nat)))
    (h3 : ((sym 213640) + 8) ≤ ((bv_unsigned sp) - 4640))
    (h4 : (bv_unsigned sp) ≤ Fp)
    (h5 : (bv_unsigned sp) ≤ B)
    (h6 : (0 ≤ t ∧ t < 256))
    (h7 : (Z_lor t 32) ≠ 97)
    (h8 : (length junk0) < 256)
    (h9 : (0 ≤ Fp ∧ Fp < (2 ^ (64 : Nat)))) :
    (((bv_unsigned sp) + (-1056)) + (4 * (d - 1))) = ((((bv_unsigned sp) + (-1056)) + (4 * ((d - 1) - 1))) + 4) := by
  lia

-- cjson/cjson_read_fuzzer: lib/RL/G/G_fmt_fp_t9a8.v (replace)
example (n : Int) :
    (((n - 1) + 1) + 1) = (((n + 1) - 1) + 1) := by
  lia

-- cjson/cjson_read_fuzzer: lib/RL/G/G_printf_core_scan.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (n : Int)
    (i : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (sym : Int → Int)
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 131072)
    (h5 : ((((sym 142872) + 8) ≤ Fp ∧ (Fp + 232) ≤ (sym 213640)) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((((sym 213640) + 8) ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (znth fmt i) ≠ 0) :
    n = (((A + i) + n) - (A + i)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/Spec/FmtFpDig.v (replace)
example :
    ((1 * (2 ^ (51 : Nat))) : Int) = (2 ^ (51 : Nat)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/Spec/FmtFpDig.v (replace)
example
    (L : Int)
    (s : Int)
    (N_1 : Int)
    (Zpow : Int → Int → Int)
    (Z_log2 : Int → Int)
    (q : Int)
    (h1 : N_1 < (Zpow 2 s))
    (h2 : (Z_log2 N_1) = L)
    (h3 : ((Zpow 2 (L - s)) ≤ q ∧ q < (Zpow 2 ((L - s) + 1))))
    (h4 : (Zpow 2 L) = ((Zpow 2 (L - s)) * (Zpow 2 s)))
    (h5 : (Zpow 2 (L + 1)) = ((Zpow 2 ((L - s) + 1)) * (Zpow 2 s))) :
    ((16383 + L) - s) = (16383 + (L - s)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/Spec/FmtFpDig.v (replace)
example (sd : Int) (Td : Int) (h1 : 0 < Td) :
    ((sd * (2 ^ (63 : Nat))) + Td) = (((sd * (2 ^ (63 : Nat))) + (0 * (2 ^ (52 : Nat)))) + Td) := by
  lia

-- cjson/cjson_read_fuzzer: lib/Spec/NumFacts.v (replace)
example
    (s : Int)
    (m : Int)
    (Zpow : Int → Int → Int)
    (h1 : (Zpow 10 (m + 1)) = (10 * (Zpow 10 m)))
    (h2 : (Zpow 10 m) = (10 * (Zpow 10 (m - 1)))) :
    (s - (m + 1)) = ((s - 1) - m) := by
  lia

-- cjson/cjson_read_fuzzer: lib/Spec/SF_ClassDiv.v (assert)
example
    (thb : Int)
    (tlb : Int)
    (h1 : (0 ≤ thb ∧ thb < (2 ^ (48 : Nat))))
    (h2 : (0 ≤ tlb ∧ tlb < (2 ^ (64 : Nat)))) :
    ((2 ^ (112 : Nat)) ≤ (((2 ^ (112 : Nat)) + (thb * (2 ^ (64 : Nat)))) + tlb) ∧ (((2 ^ (112 : Nat)) + (thb * (2 ^ (64 : Nat)))) + tlb) < (2 ^ (113 : Nat))) := by
  lia

-- cjson/cjson_read_fuzzer: lib/Spec/SF_ClassDiv.v (replace)
example (s : Int) (aExp : Int) (h1 : (0 ≤ s ∧ s ≤ 1)) (h2 : (0 ≤ aExp ∧ aExp ≤ 32766)) :
    (((s * (2 ^ (15 : Nat))) + aExp) * (2 ^ (48 : Nat))) = ((s * (2 ^ (63 : Nat))) + (aExp * (2 ^ (48 : Nat)))) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/CJ_fuzz.v (replace)
example (P : Int) (c : Int) (h1 : P ≤ (c * 8)) :
    ((-P) + (c * 8)) = ((c * 8) - P) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/CJ_heap_instR.v (replace)
example
    {bptr list_byte mstate aptr T5 : Type}
    (p : bptr)
    (A : Int)
    (k : Int)
    (n : Int)
    (old : list_byte)
    (st : mstate)
    (g : aptr)
    (b : aptr)
    (i : Int)
    (off : Int)
    (length : list_byte → Nat)
    (stride : Int)
    (get_stride : T5 → Int)
    (mr : T5)
    (G : Int)
    (conc : mstate → aptr → Int)
    (B : Int)
    (P0 : Int)
    (fst : bptr → aptr)
    (res : Int)
    (IB : Int)
    (m_last_idx : T5 → Int)
    (si : Int)
    (sl : Int)
    (UNIT : Int)
    (h1 : (((length old) : Nat) : Int) = k)
    (h2 : (0 ≤ n ∧ n < (2 ^ (32 : Nat))))
    (h3 : stride = (get_stride mr))
    (h4 : G = (conc st g))
    (h5 : B = (conc st b))
    (h6 : P0 = (conc st (fst p)))
    (h7 : res = ((((P0 + stride) - IB) - A) - k))
    (h8 : 0 ≤ (stride * i))
    (h9 : ((stride * i) + stride) ≤ (stride * ((m_last_idx mr) + 1)))
    (h10 : si = (stride * i))
    (h11 : sl = (stride * ((m_last_idx mr) + 1)))
    (h12 : P0 = ((B + 16) + si))
    (h13 : (0 ≤ res ∧ res = (((stride - IB) - (UNIT * off)) - k)))
    (h14 : (0 ≤ (i + (32 * (min res 5))) ∧ (i + (32 * (min res 5))) < 256))
    (h15 : (A % 16) = 0) :
    (A - 3) = ((A - 4) + 1) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/CJ_heap_instR.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (n : Int)
    (mn : Int)
    (stride : Int)
    (i : Int)
    (m_last_idx : T1 → Int)
    (MR : T2 → T3 → T1)
    (st : T2)
    (g : T3)
    (P0 : Int)
    (r_base : T4 → Int)
    (r : T4)
    (snd : T5 → Int)
    (b : T5)
    (A : Int)
    (k : Int)
    (length : T6 → Nat)
    (old : T6)
    (h1 : 0 ≤ (stride * i))
    (h2 : ((stride * i) + stride) ≤ (stride * ((m_last_idx (MR st g)) + 1)))
    (h3 : P0 = ((((r_base r) + (snd b)) + 16) + (stride * i)))
    (h4 : (A % 16) = 0)
    (h5 : ((0 ≤ mn ∧ mn ≤ k) ∧ (mn ≤ n ∧ (Int.toNat mn) ≤ (length old)))) :
    n = (mn + (n - mn)) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/CJ_heap_instR.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (tp : word)
    (A : Int)
    (k : Int)
    (n : Int)
    (lo : Int)
    (Bx : Int)
    (old : list_byte)
    (length : list_byte → Nat)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (RREALLOC_STACK : Int)
    (Z_to_bv : Int → Int → word)
    (RERRNO : Int)
    (mn : Int)
    (firstn : Nat → list_byte → list_byte)
    (h1 : (((length old) : Nat) : Int) = k)
    (h2 : (bv_unsigned sp) ≤ Bx)
    (h3 : alloc_ceiling ≤ lo)
    (h4 : lo ≤ ((bv_unsigned sp) - RREALLOC_STACK))
    (h5 : (0 ≤ n ∧ n < (2 ^ (32 : Nat))))
    (h6 : ((bv_unsigned tp) + (-164)) = RERRNO)
    (h7 : alloc_ceiling ≤ Bx)
    (h8 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-64)))) = ((bv_unsigned sp) - 64))
    (h9 : ((0 ≤ mn ∧ mn ≤ k) ∧ (mn ≤ n ∧ (mn = k ∨ mn = n))))
    (h10 : (length (firstn (Int.toNat mn) old)) = (Int.toNat mn)) :
    k = ((A + k) - A) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/CJ_pstr_A.v (replace)
example
    {list_byte T2 : Type}
    (str : list_byte)
    (x16 : Nat)
    (x17 : Int)
    (esc_count : T2 → Int)
    (firstn : Nat → list_byte → T2)
    (i : Int)
    (length : list_byte → Nat)
    (h1 : ((x16 : Nat) : Int) = ((((length str) : Nat) : Int) - x17))
    (h2 : (0 ≤ x17 ∧ x17 ≤ (((length str) : Nat) : Int)))
    (h3 : i = (((length str) : Nat) : Int))
    (h4 : (0 ≤ i ∧ i < (((length str) : Nat) : Int))) :
    (esc_count (firstn (Int.toNat (i + 1)) str)) = ((esc_count (firstn (Int.toNat i) str)) + 1) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/CJ_pv_objB.v (replace)
example
    {word : Type}
    (sp : word)
    (n : Nat)
    (dep : Int)
    (lo : Int)
    (buf5 : Int)
    (k : Int)
    (off2 : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (PV_STACK : Nat → Int)
    (Z_lxor : Int → Int → Int)
    (Z_b2z : Bool → Int)
    (fz : Bool)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - (PV_STACK n)))
    (h3 : (bv_unsigned sp) ≤ (2 ^ (64 : Nat)))
    (h4 : 1 ≤ n)
    (h5 : ((bv_unsigned sp) % 16) = 0)
    (h6 : (dep + ((n : Nat) : Int)) ≤ (2 ^ (40 : Nat)))
    (h7 : 0 ≤ dep)
    (h8 : ((Z_lxor (Z_b2z fz) 3) = (3 - (Z_b2z fz)) ∧ (0 ≤ (Z_b2z fz) ∧ (Z_b2z fz) ≤ 1)))
    (h9 : fz = true) :
    ((buf5 + (k + off2)) + (2 - 1)) = ((buf5 + (k + off2)) + 1) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/CJ_pv_objB.v (replace)
example
    {word : Type}
    (sp : word)
    (n : Nat)
    (dep : Int)
    (lo : Int)
    (buf5 : Int)
    (k : Int)
    (off2 : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (PV_STACK : Nat → Int)
    (Z_lxor : Int → Int → Int)
    (Z_b2z : Bool → Int)
    (fz : Bool)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - (PV_STACK n)))
    (h3 : (bv_unsigned sp) ≤ (2 ^ (64 : Nat)))
    (h4 : 1 ≤ n)
    (h5 : ((bv_unsigned sp) % 16) = 0)
    (h6 : (dep + ((n : Nat) : Int)) ≤ (2 ^ (40 : Nat)))
    (h7 : 0 ≤ dep)
    (h8 : ((Z_lxor (Z_b2z fz) 3) = (3 - (Z_b2z fz)) ∧ (0 ≤ (Z_b2z fz) ∧ (Z_b2z fz) ≤ 1)))
    (h9 : fz = true)
    (h10 : fz = false) :
    ((buf5 + (k + off2)) + (2 - 0)) = ((buf5 + (k + off2)) + 2) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/RF_realloc_A.v (replace)
example
    {T1 T2 T3 : Type}
    (last_idx : Int)
    (freeable : Int)
    (sc : Int)
    (maplen : Int)
    (mword : Int)
    (idx : Int)
    (bv_unsigned : T1 → T2)
    (Z_land : Int → Int → Int)
    (Zpow : Int → Int → Int)
    (avail : Int)
    (freed : Int)
    (Z_shiftr : T2 → Int → Int)
    (Z_to_bv : Int → T3 → T1)
    (Z_shiftl : Int → Int → T3)
    (h1 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ idx ∧ idx < 32))
    (h3 : (Z_land mword 31) = last_idx)
    (h4 : (0 ≤ (Zpow 2 idx) ∧ (Zpow 2 idx) < (2 ^ (32 : Nat))))
    (h5 : (Z_land avail (Zpow 2 idx)) = 0)
    (h6 : (Z_land freed (Zpow 2 idx)) = 0)
    (h7 : (Z_shiftr (bv_unsigned (Z_to_bv 64 (Z_shiftl mword 52))) 58) = sc) :
    ((((last_idx + (32 * freeable)) + (64 * sc)) * (2 ^ (52 : Nat))) + (maplen * (2 ^ (64 : Nat)))) = ((((last_idx + (32 * freeable)) + (64 * sc)) + (4096 * maplen)) * (2 ^ (52 : Nat))) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/RF_realloc_A.v (replace)
example
    {T1 T2 T3 : Type}
    (last_idx : Int)
    (freeable : Int)
    (sc : Int)
    (mword : Int)
    (idx : Int)
    (bv_unsigned : T1 → T2)
    (Z_land : Int → Int → Int)
    (Zpow : Int → Int → Int)
    (avail : Int)
    (freed : Int)
    (Z_shiftr : T2 → Int → Int)
    (Z_to_bv : Int → T3 → T1)
    (Z_shiftl : Int → Int → T3)
    (h1 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ idx ∧ idx < 32))
    (h3 : (Z_land mword 31) = last_idx)
    (h4 : (0 ≤ (Zpow 2 idx) ∧ (Zpow 2 idx) < (2 ^ (32 : Nat))))
    (h5 : (Z_land avail (Zpow 2 idx)) = 0)
    (h6 : (Z_land freed (Zpow 2 idx)) = 0)
    (h7 : (Z_shiftr (bv_unsigned (Z_to_bv 64 (Z_shiftl mword 52))) 58) = sc) :
    (((last_idx + (32 * freeable)) * (2 ^ (52 : Nat))) + (sc * (2 ^ (58 : Nat)))) = (((last_idx + (32 * freeable)) + (64 * sc)) * (2 ^ (52 : Nat))) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/RF_realloc_F.v (replace)
example
    {mstate bptr T3 T4 T5 T6 T7 : Type}
    (st : mstate)
    (s16 : Int)
    (i : Int)
    (off : Int)
    (snd : bptr → Int)
    (b : bptr)
    (c : bptr)
    (Z_testbit : T3 → Int → Bool)
    (m_avail : T4 → T3)
    (MR : mstate → T5 → T4)
    (g : T5)
    (m_freed : T4 → T3)
    (conc : mstate → bptr → Int)
    (r_base : T6 → Int)
    (r : T6)
    (UNIT : Int)
    (get_stride : T4 → Int)
    (m_last_idx : T4 → Int)
    (sstart : T4 → Int → Int)
    (IB : Int)
    (stride : Int)
    (round_up_pg : T7 → Int)
    (r_len : T6 → T7)
    (q : Int)
    (h1 : ((Z_testbit (m_avail (MR st g)) i) = false ∧ (Z_testbit (m_freed (MR st g)) i) = false))
    (h2 : (conc st c) = ((r_base r) + (snd c)))
    (h3 : (conc st b) = ((r_base r) + (snd b)))
    (h4 : (snd c) = (((snd b) + UNIT) + ((get_stride (MR st g)) * i)))
    (h5 : 0 ≤ ((get_stride (MR st g)) * i))
    (h6 : (((get_stride (MR st g)) * i) + (get_stride (MR st g))) ≤ ((get_stride (MR st g)) * ((m_last_idx (MR st g)) + 1)))
    (h7 : ((sstart (MR st g) (i + 1)) - IB) = (((snd c) + (get_stride (MR st g))) - IB))
    (h8 : (0 ≤ (((snd c) + (UNIT * off)) - 4) ∧ ((((snd c) + stride) - IB) + 1) ≤ (round_up_pg (r_len r))))
    (h9 : (16 * q) = ((((snd c) + (UNIT * off)) - (snd b)) - 16)) :
    (((s16 * i) + off) * 16) = ((((((snd b) + 16) + ((16 * s16) * i)) + (16 * off)) - (snd b)) - 16) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/RF_realloc_F.v (replace)
example
    {mstate T2 bptr T4 T5 T6 T7 : Type}
    (st : mstate)
    (r_base : T2 → Int)
    (r : T2)
    (snd : bptr → Int)
    (c : bptr)
    (stride : Int)
    (IB : Int)
    (Z_testbit : T4 → Int → Bool)
    (m_avail : T5 → T4)
    (MR : mstate → T6 → T5)
    (g : T6)
    (i : Int)
    (m_freed : T5 → T4)
    (conc : mstate → bptr → Int)
    (b : bptr)
    (UNIT : Int)
    (get_stride : T5 → Int)
    (m_last_idx : T5 → Int)
    (sstart : T5 → Int → Int)
    (off : Int)
    (round_up_pg : T7 → Int)
    (r_len : T2 → T7)
    (q : Int)
    (h1 : ((Z_testbit (m_avail (MR st g)) i) = false ∧ (Z_testbit (m_freed (MR st g)) i) = false))
    (h2 : (conc st c) = ((r_base r) + (snd c)))
    (h3 : (conc st b) = ((r_base r) + (snd b)))
    (h4 : (snd c) = (((snd b) + UNIT) + ((get_stride (MR st g)) * i)))
    (h5 : 0 ≤ ((get_stride (MR st g)) * i))
    (h6 : (((get_stride (MR st g)) * i) + (get_stride (MR st g))) ≤ ((get_stride (MR st g)) * ((m_last_idx (MR st g)) + 1)))
    (h7 : ((sstart (MR st g) (i + 1)) - IB) = (((snd c) + (get_stride (MR st g))) - IB))
    (h8 : (0 ≤ (((snd c) + (UNIT * off)) - 4) ∧ ((((snd c) + stride) - IB) + 1) ≤ (round_up_pg (r_len r))))
    (h9 : (16 * q) = ((((snd c) + (UNIT * off)) - (snd b)) - 16)) :
    ((r_base r) + ((((snd c) + stride) - IB) - 1)) = ((((((((r_base r) + (snd c)) + stride) - IB) - 4) + 1) + 1) + 1) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/RMallocKit_A2.v (replace)
example
    {aptr region T3 : Type}
    (pp : aptr)
    (e : aptr)
    (r : region)
    (n : Int)
    (r_base : region → Int)
    (snd : aptr → Int)
    (rsv : Int)
    (round_up_pg : T3 → Int)
    (r_len : region → T3)
    (h1 : 4 ≤ (snd pp))
    (h2 : 0 ≤ n)
    (h3 : ((snd pp) + n) ≤ (snd e))
    (h4 : ((snd e) + 1) ≤ (round_up_pg (r_len r)))
    (h5 : (((snd e) - (snd pp)) - n) < (2 ^ (32 : Nat)))
    (h6 : (0 ≤ rsv ∧ rsv < (2 ^ (32 : Nat)))) :
    (((r_base r) + (snd e)) - rsv) = ((r_base r) + ((snd e) + (-rsv))) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/RMallocKit_A2.v (replace)
example
    {aptr region T3 : Type}
    (pp : aptr)
    (e : aptr)
    (r : region)
    (n : Int)
    (r_base : region → Int)
    (snd : aptr → Int)
    (round_up_pg : T3 → Int)
    (r_len : region → T3)
    (h1 : 4 ≤ (snd pp))
    (h2 : 0 ≤ n)
    (h3 : ((snd pp) + n) ≤ (snd e))
    (h4 : ((snd e) + 1) ≤ (round_up_pg (r_len r)))
    (h5 : (((snd e) - (snd pp)) - n) < (2 ^ (32 : Nat))) :
    (((r_base r) + (snd pp)) - 3) = ((r_base r) + ((snd pp) + (-3))) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/SO_diag.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    (((bv_unsigned sp) - 80) - 368) = (((bv_unsigned sp) + (-80)) - 368) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/SO_stdio_write.v (replace)
example {T1 : Type} (length : T1 → Nat) (s : T1) (B : Int) :
    ((((length s) : Nat) : Int) - (((length s) : Nat) : Int)) = (B - B) := by
  lia

-- cjson/cjson_read_fuzzer: lib/U/SO_stdio_write.v (replace)
example {T1 : Type} (length : T1 → Nat) (s : T1) :
    ((((length s) : Nat) : Int) - ((((length s) : Nat) : Int) - (((length s) : Nat) : Int))) = (((length s) : Nat) : Int) := by
  lia

-- coturn/FuzzStunClient: lib/Asan/AsanDepotWalkP.v (replace)
example
    (usp : Int)
    (T : Int)
    (w : Int)
    (size : Int)
    (tag : Int)
    (n : Int)
    (B : Int)
    (P : Int)
    (tf : Int)
    (st : Int)
    (i : Nat)
    (s : Int)
    (h1 : ((2 ^ (32 : Nat)) ≤ (usp - 224) ∧ usp < (2 ^ (64 : Nat))))
    (h2 : ((2 ^ (32 : Nat)) ≤ T ∧ (T + (8 * size)) < (2 ^ (64 : Nat))))
    (h3 : ((T + (8 * size)) ≤ (usp - 224) ∨ usp ≤ T))
    (h4 : (w = (size + (tag * (2 ^ (32 : Nat)))) ∧ ((1 ≤ size ∧ size ≤ 255) ∧ (0 ≤ tag ∧ tag < 256))))
    (h5 : (0 ≤ n ∧ (n + 1) < (2 ^ (16 : Nat))))
    (h6 : (6324224 ≤ B ∧ (B + (16 * (2 ^ (16 : Nat)))) < (2 ^ (64 : Nat))))
    (h7 : (usp ≤ (B + 16) ∨ (B + (16 * (n + 2))) ≤ (usp - 224)))
    (h8 : ((T + (8 * size)) ≤ (B + (16 * (n + 1))) ∨ (B + (16 * (n + 2))) ≤ T))
    (h9 : (((P + (8 * tf)) + (8 * (size + 1))) ≤ (B + 16) ∨ (B + (16 * (n + 2))) ≤ (P + (8 * tf))))
    (h10 : (0 ≤ tf ∧ ((tf + 256) < (2 ^ (20 : Nat)) ∧ (0 ≤ st ∧ (st + 256) < (2 ^ (20 : Nat))))))
    (h11 : (6324224 ≤ P ∧ (P + (8 * (2 ^ (20 : Nat)))) < (2 ^ (64 : Nat))))
    (h12 : (usp ≤ (P + (8 * tf)) ∨ ((P + (8 * tf)) + (8 * (size + 1))) ≤ (usp - 224)))
    (h13 : ((T + (8 * size)) ≤ (P + (8 * tf)) ∨ ((P + (8 * tf)) + (8 * (size + 1))) ≤ T))
    (h14 : ((i : Nat) : Int) = s)
    (h15 : (0 ≤ s ∧ s ≤ n)) :
    (B + (16 * s)) = (B + (s * (2 ^ (4 : Nat)))) := by
  lia

-- coturn/FuzzStunClient: lib/Asan/AsanDepotWalkS.v (replace)
example (tag : Int) (size : Int) :
    ((tag * 256) + size) = ((tag * (2 ^ (8 : Nat))) + size) := by
  lia

-- coturn/FuzzStunClient: lib/Asan/AsanNodesDepotSoundG.v (replace)
example
    {word T2 T3 T4 T5 : Type}
    (B : Int)
    (id_1 : Int)
    (bv_unsigned : word → Int)
    (edenot : T2 → T3 → word)
    (E : T2)
    (ELit : Int → T3)
    (bytes_le_to_Z : T4 → Int)
    (dtab : T5 → Int)
    (b : T5)
    (bs : T4)
    (h1 : (bv_unsigned (edenot E (ELit 0))) = 0)
    (h2 : (dtab b) = (bytes_le_to_Z bs)) :
    ((B + (16 * id_1)) + 8) = (B + ((16 * id_1) + 8)) := by
  lia

-- coturn/FuzzStunClient: lib/Asan/AsanNodesPGSoundG.v (replace)
example
    (H0 : Int)
    (RPN_SB : Int)
    (s3v : Int)
    (j : Int)
    (uB : Int)
    (h1 : (uB % 64) = 0)
    (h2 : (0 ≤ (uB / 8) ∧ (uB / 8) < (2 ^ (61 : Nat))))
    (h3 : H0 = (RPN_SB + (uB / 8))) :
    (H0 + (((((RPN_SB + ((s3v - 1) / 8)) / 8) * 8) - H0) + j)) = ((((RPN_SB + ((s3v - 1) / 8)) / 8) * 8) + j) := by
  lia

-- coturn/FuzzStunClient: lib/Asan/AsanPlanSound.v (replace)
example
    {word : Type}
    (s : Int)
    (c : Int)
    (Zpow : Int → Int → Int)
    (Aq : Int)
    (Tq : Int)
    (bv_unsigned : word → Int)
    (Z_to_bv : Int → Int → word)
    (h1 : (0 ≤ s ∧ s < 64))
    (h2 : 0 < (Zpow 2 s))
    (h3 : (bv_unsigned (Z_to_bv 64 s)) = s)
    (h4 : c = (((Zpow 2 s) * (Int.fdiv c (Zpow 2 s))) + (Int.fmod c (Zpow 2 s)))) :
    ((((Int.fdiv c (Zpow 2 s)) + Aq) * (Zpow 2 s)) + ((Int.fmod c (Zpow 2 s)) + Tq)) = (c + (((Zpow 2 s) * Aq) + Tq)) := by
  lia

-- coturn/FuzzStunClient: lib/Asan/AsanPlanSound.v (replace)
example
    {word : Type}
    (s : Int)
    (c : Int)
    (Zpow : Int → Int → Int)
    (Aq : Int)
    (Tq : Int)
    (q1 : Int)
    (bv_unsigned : word → Int)
    (Z_to_bv : Int → Int → word)
    (h1 : (0 ≤ s ∧ s < 64))
    (h2 : 0 < (Zpow 2 s))
    (h3 : (bv_unsigned (Z_to_bv 64 s)) = s)
    (h4 : c = (((Zpow 2 s) * (Int.fdiv c (Zpow 2 s))) + (Int.fmod c (Zpow 2 s))))
    (h5 : 0 ≤ (Int.fdiv ((Int.fmod c (Zpow 2 s)) + Tq) (Zpow 2 s)))
    (h6 : (Int.fdiv ((Int.fmod c (Zpow 2 s)) + Tq) (Zpow 2 s)) < (2 ^ (64 : Nat))) :
    ((((Int.fdiv c (Zpow 2 s)) + Aq) + (Int.fdiv ((Int.fmod c (Zpow 2 s)) + Tq) (Zpow 2 s))) + (q1 * (2 ^ (64 : Nat)))) = ((((Int.fdiv c (Zpow 2 s)) + Aq) + (q1 * (2 ^ (64 : Nat)))) + (Int.fdiv ((Int.fmod c (Zpow 2 s)) + Tq) (Zpow 2 s))) := by
  lia

-- coturn/FuzzStunClient: lib/RefReadF6.v (replace)
example
    {word list_byte T3 : Type}
    (sp0 : word)
    (content : list_byte)
    (length : list_byte → Nat)
    (pref : Nat → T3 → list_byte)
    (dropz : Nat → list_byte → T3)
    (L : Int)
    (bv_unsigned : word → Int)
    (vals : list_byte)
    (h1 : 4194304 ≤ L)
    (h2 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ 140737488355328))
    (h3 : L = (((length content) : Nat) : Int))
    (h4 : (length vals) = 40)
    (h5 : (((length (pref 2097152 (dropz 2097152 content))) : Nat) : Int) = 2097152) :
    (Int.toNat 2097152) = (length (pref 2097152 (dropz 2097152 content))) := by
  lia

-- coturn/FuzzStunClient: lib/RefReadG4.v (replace)
example
    {word list_byte T3 T4 : Type}
    (sp0 : word)
    (mb : word)
    (content : list_byte)
    (B : word)
    (bv_unsigned : word → Int)
    (B' : word)
    (length : T3 → Nat)
    (vals : T3)
    (pref : Nat → T4 → T3)
    (dropz : Nat → list_byte → T4)
    (h1 : 4096 ≤ (bv_unsigned mb))
    (h2 : ((bv_unsigned mb) + 8192) ≤ ((bv_unsigned sp0) - 8388608))
    (h3 : ((bv_unsigned mb) % 4096) = 0)
    (h4 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ 140737488355328))
    (h5 : (length vals) = 40)
    (h6 : (length (pref 524288 (dropz 524288 content))) = (Int.toNat 524288))
    (h7 : 360448 ≤ (bv_unsigned B'))
    (h8 : (((bv_unsigned B') + 2101248) ≤ (bv_unsigned B) ∨ ((bv_unsigned B) + 1052672) ≤ (bv_unsigned B')))
    (h9 : (((bv_unsigned B') + 2101248) ≤ ((bv_unsigned mb) + 4096) ∨ ((bv_unsigned mb) + 8192) ≤ (bv_unsigned B'))) :
    ((bv_unsigned B') + 12) = (((bv_unsigned B') + 16) - 4) := by
  lia

-- coturn/FuzzStunClient: lib/RefReadStage.v (replace)
example (j : Int) (h1 : 1 ≤ j) :
    ((j - 1) + 1) = j := by
  lia

-- coturn/FuzzStunClient: lib/SymPlanSound.v (replace)
example
    {T1 T2 T3 word : Type}
    (E : T1)
    (allkn : T2)
    (k : T2)
    (b : T3)
    (off : Int)
    (n : Int)
    (bv_unsigned : word → Int)
    (edenot : T1 → T3 → word)
    (wb : T3)
    (wk : Int)
    (kwritable : T2 → T2 → T3 → Int → Int → Bool)
    (h1 : (kwritable allkn k b off n) = true)
    (h2 : 0 ≤ n) :
    (((bv_unsigned (edenot E wb)) + wk) + (((bv_unsigned (edenot E b)) + off) - ((bv_unsigned (edenot E wb)) + wk))) = ((bv_unsigned (edenot E b)) + off) := by
  lia

-- coturn/FuzzStunClient: lib/UbW65x.v (replace)
example
    {word T2 : Type}
    (tid : word)
    (bv_unsigned : word → Int)
    (vals_ev : T2 → Int → word)
    (vals : T2)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat)))) :
    ((bv_unsigned (vals_ev vals 71)) + (1 * 4096)) = ((bv_unsigned (vals_ev vals 71)) + 4096) := by
  lia

-- coturn/FuzzStunClient: lib/VAbsSound3.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (A : T1)
    (nu : T2)
    (x : T3)
    (m : Int)
    (u : T4)
    (k : Int)
    (Zpow : Int → Int → Int)
    (eval : T2 → T3 → Int)
    (lin_below : T3 → T5 → Bool)
    (vs_next : T1 → T5)
    (Z_land : T4 → Int → Int)
    (h1 : (lin_below x (vs_next A)) = true)
    (h2 : (0 < m ∧ m < (2 ^ (64 : Nat))))
    (h3 : k ≤ 64)
    (h4 : (2 ^ (64 : Nat)) < (Zpow 2 k))
    (h5 : (Zpow 2 k) ≤ (2 ^ (64 : Nat)))
    (h6 : (Z_land u m) = (Int.fmod (eval nu x) (Zpow 2 k))) :
    (Zpow 2 k) = (m + 1) := by
  lia

-- coturn/FuzzStunClient: lib/VAbsSound3.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (A : T1)
    (nu : T2)
    (x : T3)
    (m : Int)
    (u : Int)
    (k : Int)
    (Zpow : Int → Int → Int)
    (zwrap : Int → Int → Int)
    (eval : T2 → T3 → Int)
    (lin_below : T3 → T4 → Bool)
    (vs_next : T1 → T4)
    (Z_land : Int → Int → Int)
    (nu2 : T2)
    (h1 : u = (zwrap 64 (eval nu x)))
    (h2 : (lin_below x (vs_next A)) = true)
    (h3 : (0 < m ∧ m < (2 ^ (64 : Nat))))
    (h4 : k ≤ 64)
    (h5 : (2 ^ (64 : Nat)) < (Zpow 2 k))
    (h6 : (Zpow 2 k) ≤ (2 ^ (64 : Nat)))
    (h7 : (Z_land u m) = (Int.fmod (eval nu x) (Zpow 2 k)))
    (h8 : (eval nu2 x) = (eval nu x))
    (h9 : (Z_land u m) = (u - (Int.fmod u (Zpow 2 k))))
    (h10 : (Int.fmod u (Zpow 2 k)) = (Int.fmod (eval nu x) (Zpow 2 k)))
    (h11 : (zwrap 64 ((eval nu x) - (Int.fmod (eval nu x) (Zpow 2 k)))) = (u - (Int.fmod u (Zpow 2 k))))
    (h12 : (0 ≤ (u - (Int.fmod (eval nu x) (Zpow 2 k))) ∧ (u - (Int.fmod (eval nu x) (Zpow 2 k))) < (2 ^ (64 : Nat)))) :
    (Zpow 2 k) = ((2 ^ (64 : Nat)) - m) := by
  lia

-- coturn/FuzzStunClient: lib/VAsanIcBcmpWalk.v (replace)
example (usp : Int) :
    ((usp - 2240) - 48) = ((((usp - 2240) + (-48)) + (-16)) + 16) := by
  lia

-- coturn/FuzzStunClient: lib/VAsanStackMallocWalk.v (replace)
example
    {word : Type}
    (fs : Int)
    (p0 : Int)
    (i : Int)
    (p : Int)
    (SB : Int)
    (j : Int)
    (N3 : Int)
    (bv_unsigned : word → Int)
    (FL : Int → word)
    (ff3 : Int → Int)
    (h1 : ((0 ≤ p0 ∧ p0 < N3) ∧ (bv_unsigned (FL p0)) = 0))
    (h2 : (0 ≤ p ∧ p < N3))
    (h3 : (0 ≤ i ∧ i < N3))
    (h4 : 6324224 ≤ (ff3 p))
    (h5 : ((ff3 p) + 512) ≤ (2 ^ (47 : Nat))) :
    ((SB + (((fs + 3182592) + (512 * p)) / 8)) + (24 + j)) = (((SB + (((fs + 3182592) + (512 * p)) / 8)) + 24) + j) := by
  lia

-- coturn/FuzzStunClient: lib/VBothIcStrncpyWalk.v (replace)
example (usp : Int) :
    (usp - 2160) = (((usp - 2160) + (-16)) + 16) := by
  lia

-- coturn/FuzzStunClient: lib/VCong.v (replace)
example {T1 T2 : Type} (eval : T1 → T2 → Int) (v : T1) (a : T2) (r' : Int) (r : Int) :
    (((eval v a) - r') + (r' - r)) = ((eval v a) - r) := by
  lia

-- coturn/FuzzStunClient: lib/VContractA.v (replace)
example (rem : Int) :
    ((Int.toNat rem) + 0) = (Int.toNat rem) := by
  lia

-- coturn/FuzzStunClient: lib/VContractASound2.v (replace)
example
    {vparams2 T2 T3 T4 T5 T6 : Type}
    (P : vparams2)
    (rB : Int)
    (k : Int)
    (vp_shoff : vparams2 → Int)
    (SBz : Int)
    (n : Int)
    (e_sp0 : T2 → Int)
    (E1 : T2)
    (vp_frame : T3 → Int)
    (P1 : T3)
    (usp : Int)
    (is_data_shadow : T4 → Bool)
    (r : T4)
    (eval : T5 → T6 → Int)
    (nu : T5)
    (de : T6)
    (rbase : T5 → T4 → Int)
    (off : T6)
    (fake_size : Int → Int)
    (fa : Int)
    (d : Int)
    (cid : Int)
    (c : Int)
    (h1 : (vp_shoff P) = SBz)
    (h2 : (0 ≤ ((e_sp0 E1) - (vp_frame P1)) ∧ (((e_sp0 E1) - (vp_frame P1)) ≤ (usp - 2208) ∧ (usp ≤ (e_sp0 E1) ∧ (e_sp0 E1) < (2 ^ (64 : Nat))))))
    (h3 : 0 < n)
    (h4 : (is_data_shadow r) = false)
    (h5 : (eval nu de) = ((rbase nu r) + (eval nu off)))
    (h6 : (fa ≤ d ∧ ((d + n) ≤ (fa + (fake_size cid)) ∧ (0 ≤ d ∧ (d + n) ≤ ((2 ^ (47 : Nat)) - 1)))))
    (h7 : (c % 256) = 0) :
    (rB + (k * 8)) = (0 + ((8 * k) + rB)) := by
  lia

-- coturn/FuzzStunClient: lib/VContractASound3_asan.v (assert)
example (cid : Int) (h1 : (0 ≤ cid ∧ cid ≤ 4)) :
    (cid = 0 ∨ (cid = 1 ∨ (cid = 2 ∨ (cid = 3 ∨ cid = 4)))) := by
  lia

-- coturn/FuzzStunClient: lib/VContractASound4.v (replace)
example
    {vparams2 T2 T3 T4 T5 T6 : Type}
    (P : vparams2)
    (e_sp0 : T2 → Int)
    (E1 : T2)
    (sov : Int)
    (i : Int)
    (vp_shoff : vparams2 → Int)
    (SBz : Int)
    (vp_datal : vparams2 → Int)
    (n : Int)
    (vp_frame : T3 → Int)
    (P1 : T3)
    (usp : Int)
    (eval : T4 → T5 → Int)
    (nu : T4)
    (se : T5)
    (rbase : T4 → T6 → Int)
    (r2 : T6)
    (off2 : T5)
    (s : Int)
    (de : T5)
    (r : T6)
    (off : T5)
    (d : Int)
    (h1 : (vp_shoff P) = SBz)
    (h2 : 8 ≤ (vp_datal P))
    (h3 : (0 ≤ n ∧ n ≤ (2 ^ (40 : Nat))))
    (h4 : (0 ≤ ((e_sp0 E1) - (vp_frame P1)) ∧ (((e_sp0 E1) - (vp_frame P1)) ≤ (usp - 2224) ∧ (usp ≤ (e_sp0 E1) ∧ (e_sp0 E1) < (2 ^ (64 : Nat))))))
    (h5 : (eval nu se) = ((rbase nu r2) + (eval nu off2)))
    (h6 : (eval nu de) = ((rbase nu r) + (eval nu off)))
    (h7 : (n = 0 ∨ ((s + n) ≤ d ∨ (d + n) ≤ s))) :
    ((e_sp0 E1) + (sov + i)) = (((e_sp0 E1) + sov) + i) := by
  lia

-- coturn/FuzzStunClient: lib/VContractSound.v (replace)
example
    {T1 T2 T3 : Type}
    (e_data : T1 → Int)
    (E : T1)
    (eval : T2 → T3 → Int)
    (nu : T2)
    (base : T3)
    (i : Int) :
    ((e_data E) + (((eval nu base) - (e_data E)) + i)) = ((eval nu base) + i) := by
  lia

-- coturn/FuzzStunClient: lib/VSoundCall2x.v (replace)
example
    (sp0 : Int)
    (lo0 : Int)
    (hi0 : Int)
    (off : Int)
    (s : Int)
    (l : Int)
    (h1 : (sp0 % 16) = 0)
    (h2 : (lo0 % 8) = 0)
    (h3 : (hi0 % 8) = 0)
    (h4 : ((lo0 / 8) ≤ off ∧ off < (hi0 / 8)))
    (h5 : 0 ≤ (sp0 + lo0))
    (h6 : hi0 ≤ 0)
    (h7 : sp0 < (2 ^ (64 : Nat)))
    (h8 : ((sp0 + lo0) / 8) = ((2 * s) + l))
    (h9 : (sp0 / 8) = (2 * s)) :
    ((2 * s) * 8) = (16 * s) := by
  lia

-- coturn/FuzzStunClient: lib/VSoundCall2x.v (replace)
example
    (sp0 : Int)
    (lo0 : Int)
    (hi0 : Int)
    (off : Int)
    (h_1 : Int)
    (l : Int)
    (s : Int)
    (h1 : (sp0 % 16) = 0)
    (h2 : (lo0 % 8) = 0)
    (h3 : (hi0 % 8) = 0)
    (h4 : ((lo0 / 8) ≤ off ∧ off < (hi0 / 8)))
    (h5 : 0 ≤ (sp0 + lo0))
    (h6 : hi0 ≤ 0)
    (h7 : sp0 < (2 ^ (64 : Nat)))
    (h8 : ((sp0 + lo0) / 8) = ((2 * s) + l))
    (h9 : (sp0 / 8) = (2 * s))
    (h10 : ((hi0 - lo0) / 8) = (h_1 - l)) :
    ((h_1 - l) * 8) = ((8 * h_1) - (8 * l)) := by
  lia

-- coturn/FuzzStunClient: lib/VSoundContract2.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (vs_pc : T1 → Int)
    (v1 : T2 → T1)
    (A : T2)
    (contract2_K : T3 → Int)
    (c : T3)
    (in_ranges : T4 → Int → Int → Bool)
    (vp_wstack : T5 → T4)
    (p1 : T6 → T5)
    (P : T6)
    (spoff : Int)
    (npc : Int)
    (h1 : ((contract2_K c) = 0 ∨ (in_ranges (vp_wstack (p1 P)) (spoff - (contract2_K c)) (contract2_K c)) = true))
    (h2 : (0 ≤ npc ∧ npc < (2 ^ (64 : Nat)))) :
    ((vs_pc (v1 A)) + (2 * 2)) = ((vs_pc (v1 A)) + 4) := by
  lia

-- coturn/FuzzStunClient: lib/VStepMem2SoundB.v (replace)
example
    (sz : Int)
    (d : Int)
    (q : Int)
    (h1 : d = (q * 8))
    (h2 : (((d + sz) - 1) / 8) = (q + ((sz - 1) / 8)))
    (h3 : (((sz - 1) / 8) + 2) = ((sz + 15) / 8)) :
    ((sz - 1) + (2 * 8)) = (sz + 15) := by
  lia

-- coturn/FuzzStunClient: lib/VTopAsan.v (replace)
example
    {list_Segment FAParams vunit2 word T5 : Type}
    (SEGS : list_Segment)
    (FA : FAParams)
    (U : vunit2)
    (sp : word)
    (spa : word)
    (usp : Int)
    (q : Int)
    (segs_wr_readable : list_Segment → Bool)
    (bv_unsigned : word → Int)
    (root_ok2 : FAParams → vunit2 → Bool)
    (res : Int)
    (u_sp : T5 → Int)
    (u1 : vunit2 → T5)
    (fa_frame : FAParams → Int)
    (h1 : (segs_wr_readable SEGS) = true)
    (h2 : (root_ok2 FA U) = true)
    (h3 : ((bv_unsigned sp) % 32) = res)
    (h4 : (bv_unsigned spa) = ((bv_unsigned sp) - (u_sp (u1 U))))
    (h5 : ((usp - (fa_frame FA)) / 8) = ((usp / 8) - ((fa_frame FA) / 8))) :
    (usp + ((-(q * 8)) * 8)) = (usp - (q * 64)) := by
  lia

-- coturn/FuzzStunClient: lib/VTopAsan.v (replace)
example
    {list_Segment FAParams vunit2 word T5 : Type}
    (SEGS : list_Segment)
    (FA : FAParams)
    (U : vunit2)
    (sp : word)
    (spa : word)
    (usr : Int)
    (u_sp : T5 → Int)
    (u1 : vunit2 → T5)
    (segs_wr_readable : list_Segment → Bool)
    (bv_unsigned : word → Int)
    (root_ok2 : FAParams → vunit2 → Bool)
    (usp : Int)
    (h1 : (segs_wr_readable SEGS) = true)
    (h2 : (root_ok2 FA U) = true)
    (h3 : (bv_unsigned spa) = ((bv_unsigned sp) - (u_sp (u1 U))))
    (h4 : usp = (usr - (u_sp (u1 U))))
    (h5 : (usp / 8) = ((usr / 8) - ((u_sp (u1 U)) / 8))) :
    usr = ((usr - (u_sp (u1 U))) + (u_sp (u1 U))) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/AsanNodesIOSound.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (E : T1)
    (allkn : T2)
    (k : T2)
    (b : T3)
    (off : Int)
    (n : T4)
    (bv_unsigned : T5 → Int)
    (edenot : T1 → T3 → T5)
    (wb : T3)
    (wk : Int)
    (kwritable0_x : T2 → T2 → T3 → Int → T4 → Bool)
    (h1 : (kwritable0_x allkn k b off n) = true) :
    (((bv_unsigned (edenot E wb)) + wk) + (((bv_unsigned (edenot E b)) + off) - ((bv_unsigned (edenot E wb)) + wk))) = ((bv_unsigned (edenot E b)) + off) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/BnA_ads1.v (replace)
example
    {T1 : Type}
    (F : Int)
    (zlen : T1 → Int)
    (chunks : Int → Int → T1)
    (d : Int)
    (B : Int)
    (M64 : Int)
    (h1 : (1 ≤ (zlen (chunks 3 d)) ∧ (zlen (chunks 3 d)) ≤ 3))
    (h2 : ((1 ≤ d ∧ d < B) ∨ ((B ≤ d ∧ d < (B * B)) ∨ ((B * B) ≤ d ∧ d < M64))))
    (h3 : (0 ≤ (d % 268435456) ∧ (d % 268435456) < 268435456))
    (h4 : (1 ≤ (d / 268435456) ∧ (d / 268435456) < 268435456)) :
    (F + 696) = (((F + 688) + 4) + (4 * 1)) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/BnA_frame.v (replace)
example
    {T1 : Type}
    (k : Int)
    (i : Int)
    (Zpow : Int → Int → Int)
    (Z_shiftl : T1 → Int → Int)
    (Z_ones : Int → T1)
    (h1 : (0 < k ∧ k < 64))
    (h2 : ((2 ^ (64 : Nat)) - (Zpow 2 k)) = (Z_shiftl (Z_ones (64 - k)) k)) :
    i = ((i - k) + k) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/BnB_cbd2.v (replace)
example
    {T1 : Type}
    (F : Int)
    (zlen : T1 → Int)
    (ds : T1)
    (len : Int)
    (FS : Int)
    (SHA : Int)
    (pA : Int)
    (p : Int)
    (FA : Int)
    (gA : Int)
    (h1 : (zlen ds) = len)
    (h2 : pA ≠ p)
    (h3 : FA = ((FS + 5279744) + (pA * 2048)))
    (h4 : FA = (8 * (gA - SHA)))
    (h5 : ((FA + 2048) ≤ F ∨ (F + 2048) ≤ FA)) :
    ((F + 688) + 516) = (F + 1204) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/BnMath.v (replace)
example (r : Int) (r' : Int) :
    (((r - 13) - r') + 13) = (r - r') := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/BnP_ads1.v (replace)
example (sp : Int) :
    (sp + (-616)) = (((sp + (-620)) + 4) + (4 * ((0 : Nat) : Int))) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/BnZX.v (replace)
example
    {T1 T2 : Type}
    (E : T1)
    (b : T2)
    (s : Int)
    (M64 : Int)
    (ev : T1 → T2 → Int)
    (h1 : (Int.fmod (ev E b) M64) = (M64 - 1)) :
    (63 - ((Int.fmod s M64) % 64)) = ((64 - ((Int.fmod s M64) % 64)) - 1) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/LaSoundMem2.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (st : T1)
    (t : T2)
    (w : Int)
    (SH_A : Int)
    (rho : T3 → Int)
    (SYM_DATA : T3)
    (SYM_N : T3)
    (SYM_D16 : T3)
    (g : Int)
    (wf_state : T1 → Bool)
    (lin_below : T2 → T4 → Bool)
    (s_next : T1 → T4)
    (h1 : (wf_state st) = true)
    (h2 : 0 < w)
    (h3 : w ≤ 8)
    (h4 : (lin_below t (s_next st)) = true)
    (h5 : ((rho SYM_DATA) / 8) = (2 * (rho SYM_D16)))
    (h6 : (g + 1) ≤ ((rho SYM_N) / 8))
    (h7 : ((rho SYM_N) / 8) = g)
    (h8 : ((rho SYM_N) % 8) = ((rho SYM_N) - (8 * g))) :
    ((SH_A + ((rho SYM_DATA) / 8)) + ((rho SYM_N) / 8)) = ((SH_A + (2 * (rho SYM_D16))) + g) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/LaSoundVal.v (replace)
example
    {T1 T2 : Type}
    (rho : T1)
    (x : T2)
    (y : T2)
    (evl : T1 → T2 → Int)
    (d : T2)
    (h1 : (evl rho d) = ((evl rho x) - (evl rho y))) :
    (((evl rho d) + (2 ^ (64 : Nat))) + ((-1) * (2 ^ (64 : Nat)))) = (evl rho d) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/LaSumMemset.v (replace)
example
    {T1 T2 T3 : Type}
    (a : Int)
    (a' : Int)
    (n : Int)
    (length : T1 → Nat)
    (repeat_1 : T2 → Nat → T1)
    (Z_to_bv : Nat → T3 → T2)
    (c : T3)
    (h1 : 0 ≤ a)
    (h2 : a < (2 ^ (64 : Nat)))
    (h3 : (a + (((length (repeat_1 (Z_to_bv 8 c) (Int.toNat n))) : Nat) : Int)) ≤ (2 ^ (64 : Nat)))
    (h4 : (¬ (a ≤ a' ∧ a' < (a + (((length (repeat_1 (Z_to_bv 8 c) (Int.toNat n))) : Nat) : Int))))) :
    (a + (a' - a)) = a' := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/LxSoundAlu.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (rho2 : T1)
    (st2 : T2)
    (x : T3)
    (y : T3)
    (wa : T4)
    (wb : T4)
    (evl : T1 → T3 → Int)
    (p2 : Int)
    (q : Int)
    (lin_below : T3 → T5 → Bool)
    (s_next : T2 → T5)
    (bv_unsigned : T4 → Int)
    (alu64 : T6 → T4 → T4 → T4)
    (ALU_AND : T6)
    (Z_land : Int → Int → Int)
    (m : Int)
    (two64 : Int)
    (j : Int)
    (Zpow : Int → Int → Int)
    (h1 : (lin_below x (s_next st2)) = true)
    (h2 : (lin_below y (s_next st2)) = true)
    (h3 : (bv_unsigned (alu64 ALU_AND wa wb)) = (Z_land (bv_unsigned wa) (bv_unsigned wb)))
    (h4 : 0 ≤ (Z_land (bv_unsigned wa) (bv_unsigned wb)))
    (h5 : (bv_unsigned wb) = (Int.fmod m two64))
    (h6 : 0 ≤ j)
    (h7 : j ≤ 64)
    (h8 : (2 ^ (64 : Nat)) < (Zpow 2 j))
    (h9 : (bv_unsigned wa) = (evl rho2 x))
    (h10 : (bv_unsigned wa) = ((evl rho2 x) + (2 ^ (64 : Nat))))
    (h11 : (Zpow 2 j) ≤ (2 ^ (64 : Nat)))
    (h12 : (Int.fdiv (evl rho2 x) p2) = q) :
    (Int.fmod (evl rho2 x) p2) = ((evl rho2 x) + (-(q * p2))) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/LxUnitSplit.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (Un : T1)
    (which : T2)
    (cps : T3)
    (i : Nat)
    (k' : Nat)
    (leaves_ok : T4 → Bool)
    (run_some : T1 → Nat → T3 → T2 → T4)
    (h1 : (leaves_ok (run_some Un i cps which)) = true) :
    (i + (k' + 1)) = ((i + 1) + k') := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/RefReadG1.v (replace)
example
    {word list_byte T3 T4 : Type}
    (sp0 : word)
    (mb : word)
    (content : list_byte)
    (B : word)
    (bv_unsigned : word → Int)
    (B' : word)
    (L : Int)
    (length : T3 → Nat)
    (vals : T3)
    (pref : Nat → T4 → T3)
    (dropz : Nat → list_byte → T4)
    (h1 : 524288 ≤ L)
    (h2 : 4096 ≤ (bv_unsigned mb))
    (h3 : ((bv_unsigned mb) + 8192) ≤ ((bv_unsigned sp0) - 8388608))
    (h4 : ((bv_unsigned mb) % 4096) = 0)
    (h5 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ 140737488355328))
    (h6 : (length vals) = 40)
    (h7 : (length (pref 262144 (dropz 262144 content))) = (Int.toNat 262144))
    (h8 : 942080 ≤ (bv_unsigned B'))
    (h9 : (((bv_unsigned B') + 1052672) ≤ (bv_unsigned B) ∨ ((bv_unsigned B) + 528384) ≤ (bv_unsigned B')))
    (h10 : (((bv_unsigned B') + 1052672) ≤ ((bv_unsigned mb) + 4096) ∨ ((bv_unsigned mb) + 8192) ≤ (bv_unsigned B'))) :
    ((bv_unsigned B') + 13) = (((bv_unsigned B') + 16) - 3) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/RefW65x.v (replace)
example
    {list_byte word : Type}
    (path : list_byte)
    (tid : word)
    (vals : list_byte)
    (bv_unsigned : word → Int)
    (gm : word)
    (path_has_slash : list_byte → Bool)
    (path_is_dirref : list_byte → Bool)
    (length : list_byte → Nat)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h2 : (path_has_slash path) = false)
    (h3 : (path_is_dirref path) = false)
    (h4 : (length path) ≤ 4095)
    (h5 : (length vals) = 73) :
    ((bv_unsigned gm) + 69624) = (((((bv_unsigned gm) + 16) + 69616) - 4) - 4) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/SymPlanSoundEF.v (replace)
example
    {T1 T2 T3 : Type}
    (E : T1)
    (st : Int)
    (bv_unsigned : T2 → Int)
    (edenot : T1 → T3 → T2)
    (sb : T3)
    (sk : Int)
    (g : Int)
    (start : T3)
    (h1 : (0 ≤ g ∧ (g + 40) ≤ (2 ^ (64 : Nat))))
    (h2 : (bv_unsigned (edenot E start)) = st)
    (h3 : ((bv_unsigned (edenot E sb)) + sk) = st) :
    (st - 4) = ((bv_unsigned (edenot E sb)) + (sk - 4)) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/SymPlanSoundEF.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (E : T1)
    (M : T2)
    (stride : Int)
    (RSEGS : T3)
    (edenot : T1 → T4 → T5)
    (strideE : T4)
    (Z_to_bv : Int → Int → T5)
    (bv_unsigned : T5 → Int)
    (g : Int)
    (start : T4)
    (st : Int)
    (sb : T4)
    (sk : Int)
    (store_ok : T3 → T2 → T5 → Nat → Bool)
    (elenZ : T1 → T6 → Int)
    (mkAlu : T7 → T4 → T8 → T6)
    (ALU_ADD : T7)
    (ELit : Int → T8)
    (h1 : (bv_unsigned (edenot E strideE)) = stride)
    (h2 : (0 ≤ g ∧ (g + 40) ≤ (2 ^ (64 : Nat))))
    (h3 : (bv_unsigned (edenot E start)) = st)
    (h4 : ((bv_unsigned (edenot E sb)) + sk) = st)
    (h5 : (store_ok RSEGS M (Z_to_bv 64 (st - 3)) (Int.toNat (stride - 1))) = true)
    (h6 : (elenZ E (mkAlu ALU_ADD strideE (ELit (-1)))) = (stride - 1)) :
    ((stride - 1) + (1 * (2 ^ (64 : Nat)))) = (stride + ((2 ^ (64 : Nat)) - 1)) := by
  lia

-- double-conversion/string_to_double_fuzzer: lib/UbSymPlanSound.v (lemma)
example (a : Nat) (v : Nat) (h1 : (max 1 a) ≤ v) :
    a ≤ v := by
  lia

-- fast_float/from_chars: lib/AAC/AcConvInvG.v (replace)
example
    {valu lin tree_bval T4 : Type}
    (E : valu)
    (D1l : lin)
    (B1l : lin)
    (ct : tree_bval)
    (cs : tree_bval)
    (cd : tree_bval)
    (n : Int)
    (F : Int)
    (st : Int)
    (fuel : Nat)
    (b : Int)
    (j : Nat)
    (tab_ok_g : tree_bval → tree_bval → Int → Nat → Bool)
    (fb : tree_bval → T4 → Bool)
    (bv_list : Int → lin → Int → T4)
    (uE : valu → lin → Int)
    (h1 : (tab_ok_g ct cd n fuel) = true)
    (h2 : (0 ≤ n ∧ n ≤ 65533))
    (h3 : (fb ct (bv_list 4197544 D1l 8)) = true)
    (h4 : ((0 ≤ st ∧ st ≤ F) ∧ F ≤ 1048000))
    (h5 : (fb cs (bv_list 3224 B1l 8)) = true)
    (h6 : (6529024 ≤ (uE E D1l) ∧ (((uE E D1l) + 1048576) ≤ (2 ^ (47 : Nat)) ∧ ((uE E D1l) % 16) = 0)))
    (h7 : (6529024 ≤ (uE E B1l) ∧ (((uE E B1l) + 8388608) ≤ (2 ^ (47 : Nat)) ∧ ((uE E B1l) % 8) = 0)))
    (h8 : (((uE E D1l) + 1048576) ≤ (uE E B1l) ∨ ((uE E B1l) + 8388608) ≤ (uE E D1l)))
    (h9 : (0 ≤ b ∧ b < 1048576)) :
    ((3224 + (4 * b)) + ((j : Nat) : Int)) = ((((3224 + (4 * b)) + ((j : Nat) : Int)) + 1) - 1) := by
  lia

-- fast_float/from_chars: lib/AACB/AcMALlib.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (E : T1)
    (L : T2)
    (M : T3)
    (spl : T4)
    (bv_unsigned : T5 → Int)
    (lden : T1 → T4 → T5)
    (sm_sp : T3 → T4)
    (segs_below_b : T6 → Int → Bool)
    (ASEGS : T6)
    (band_ok : T7 → T3 → T4 → Bool)
    (s_facts : T2 → T7)
    (d : Int)
    (two64 : Int)
    (h1 : (segs_below_b ASEGS 140737488355328) = true)
    (h2 : (band_ok (s_facts L) M spl) = true)
    (h3 : (((bv_unsigned (lden E (sm_sp M))) - (bv_unsigned (lden E spl))) % 18446744073709551616) = (((bv_unsigned (lden E (sm_sp M))) - (bv_unsigned (lden E spl))) + 18446744073709551616))
    (h4 : (bv_unsigned (lden E spl)) = (Int.fmod ((bv_unsigned (lden E (sm_sp M))) + d) two64)) :
    (bv_unsigned (lden E spl)) = (((bv_unsigned (lden E spl)) - (bv_unsigned (lden E (sm_sp M)))) + (bv_unsigned (lden E (sm_sp M)))) := by
  lia

-- fast_float/from_chars: lib/AACB/AcPriStep.v (assert)
example
    {list_Z : Type}
    (pz : list_Z)
    (c : Int)
    (c' : Int)
    (z_tg : list_Z → Int)
    (z_pg : list_Z → Int)
    (PG_SIZE : Int)
    (z_z : list_Z → Int → Int)
    (h1 : (((z_tg pz) + 4096) ≤ (z_pg pz) ∨ ((z_pg pz) + PG_SIZE) ≤ (z_tg pz)))
    (h2 : (z_z pz c) = 262144) :
    (c' = c ∨ (c' ≤ (c - 1) ∨ (c + 1) ≤ c')) := by
  lia

-- fast_float/from_chars: lib/AACB/AcPriStep.v (assert)
example
    {list_Z : Type}
    (pz : list_Z)
    (c : Int)
    (x : Int)
    (c' : Int)
    (z_tg : list_Z → Int)
    (z_pg : list_Z → Int)
    (PG_SIZE : Int)
    (z_z : list_Z → Int → Int)
    (z_j : list_Z → Int → Int)
    (sz_tbl : Int → Int)
    (z_sb : list_Z → Int)
    (h1 : (((z_tg pz) + 4096) ≤ (z_pg pz) ∨ ((z_pg pz) + PG_SIZE) ≤ (z_tg pz)))
    (h2 : (z_z pz c) = 262144)
    (h3 : ((z_j pz c) + 1) ≤ (Int.fdiv 262144 (sz_tbl c)))
    (h4 : ((((z_sb pz) + (4294967296 * c)) + ((sz_tbl c) * (z_j pz c))) ≤ x ∧ x < ((((z_sb pz) + (4294967296 * c)) + ((sz_tbl c) * (z_j pz c))) + (sz_tbl c))))
    (h5 : x < (((z_sb pz) + (4294967296 * c)) + 262144)) :
    (c' = c ∨ (c' ≤ (c - 1) ∨ (c + 1) ≤ c')) := by
  lia

-- fast_float/from_chars: lib/AACB/AcSplitX.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (E : T1)
    (R : T2)
    (o : Int)
    (z : Int)
    (p : T3)
    (m : T3)
    (uE : T1 → T3 → Int)
    (rg_base : T2 → T3)
    (i : Int)
    (rk_rwz : T4 → Bool)
    (rg_kind : T2 → T4)
    (rsz : T1 → T2 → Int)
    (two64 : Int)
    (h1 : (rk_rwz (rg_kind R)) = true)
    (h2 : (rsz E R) = z)
    (h3 : (0 ≤ o ∧ o < z))
    (h4 : (1 ≤ (uE E m) ∧ (o + (uE E m)) = z))
    (h5 : (uE E p) = ((uE E (rg_base R)) + o))
    (h6 : ((uE E (rg_base R)) + z) < two64) :
    ((uE E (rg_base R)) + (o + i)) = (((uE E (rg_base R)) + o) + i) := by
  lia

-- fast_float/from_chars: lib/AACB/AcUnwApp.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (E : T1)
    (b : Int)
    (z : Int)
    (c : T2)
    (j : Nat)
    (RG : T3 → T3 → T4 → T2 → T5)
    (lconst : Int → T3)
    (RZ : T4)
    (two64 : Int)
    (psz_ok : T2 → Int → Bool)
    (bv_unsigned : T6 → Int)
    (lden : T1 → T7 → T6)
    (rg_base : T5 → T7)
    (h1 : (0 ≤ b ∧ b ≤ 1532192))
    (h2 : (1532192 + 8) ≤ (b + z))
    (h3 : (b + z) < two64)
    (h4 : (psz_ok c (1532192 - b)) = true)
    (h5 : (bv_unsigned (lden E (rg_base (RG (lconst b) (lconst z) RZ c)))) = b) :
    (1532192 + ((j : Nat) : Int)) = (b + ((((Int.toNat (1532192 - b)) + j) : Nat) : Int)) := by
  lia

-- fast_float/from_chars: lib/AAX/AxAsan.v (replace)
example
    {T1 T2 T3 : Type}
    (E : T1)
    (ea : T2)
    (eb : T2)
    (a : Int)
    (b : Int)
    (bv_unsigned : T3 → Int)
    (edenot : T1 → T2 → T3)
    (h1 : 0 ≤ a)
    (h2 : 0 ≤ b)
    (h3 : (a + b) < (2 ^ (31 : Nat)))
    (h4 : a < (2 ^ (31 : Nat)))
    (h5 : (bv_unsigned (edenot E ea)) = a)
    (h6 : (bv_unsigned (edenot E eb)) = b) :
    ((a + b) + 2147483648) = ((((a + 2147483648) - 2147483648) + ((b + 2147483648) - 2147483648)) + 2147483648) := by
  lia

-- fast_float/from_chars: lib/AAXB/AXG_np2.v (replace)
example
    (t : Nat)
    (Hk : Int)
    (rem : Int)
    (vc : Int)
    (h1 : (Hk / 32) = ((t : Nat) : Int))
    (h2 : (32 ≤ Hk ∧ Hk ≤ (2 ^ (32 : Nat))))
    (h3 : (0 ≤ vc ∧ vc ≤ ((2 ^ (64 : Nat)) - 1)))
    (h4 : ((rem - 32) / 32) = ((t : Nat) : Int)) :
    ((rem - 32) + (1 * 32)) = rem := by
  lia

-- fast_float/from_chars: lib/AAXB/AXG_np2.v (replace)
example
    {T1 T2 : Type}
    (R : T1)
    (s : Int)
    (n : Int)
    (kq : Int)
    (getr : T1 → Int → T2)
    (bv_unsigned : T2 → Int)
    (Z_to_bv : Int → Int → Int)
    (c : Int)
    (b : Int)
    (R9 : T1)
    (wc : Int)
    (q : Int)
    (Z_shiftr : Int → Int → Int)
    (h1 : 1 ≤ s)
    (h2 : (0 ≤ n ∧ n ≤ (2 ^ (32 : Nat))))
    (h3 : (s + n) ≤ (2 ^ (47 : Nat)))
    (h4 : (bv_unsigned (getr R (Z_to_bv 5 ((10 : Nat) : Int)))) = s)
    (h5 : (0 ≤ c ∧ c ≤ ((2 ^ (64 : Nat)) - 1)))
    (h6 : (0 ≤ b ∧ b < 256))
    (h7 : 1 ≤ n)
    (h8 : 9 ≤ n)
    (h9 : (0 ≤ wc ∧ wc ≤ ((2 ^ (64 : Nat)) - 1)))
    (h10 : wc = (72057594037927936 * b))
    (h11 : (bv_unsigned (getr R9 (Z_to_bv 5 ((10 : Nat) : Int)))) = s)
    (h12 : (((n - kq) - 3) ≤ (4 * q) ∧ (4 * q) ≤ (n - kq)))
    (h13 : (4 * (Z_shiftr (Int.fmod (n + ((-1) * kq)) (2 ^ (64 : Nat))) 2)) = (4 * q)) :
    (n - kq) = (n + ((-1) * kq)) := by
  lia

-- fast_float/from_chars: lib/Common/FxCall.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (E1 : T1)
    (Eq : T1)
    (P0s : T2)
    (Qs : T2)
    (x : T3)
    (bv_unsigned : T3 → Int)
    (lden : T1 → T4 → T3)
    (rg_base : T5 → T4)
    (R : T5)
    (shape_eqb : T2 → T2 → Bool)
    (kinds_ok : T2 → T2 → Bool)
    (RQ : T5)
    (h1 : (shape_eqb P0s Qs) = true)
    (h2 : (kinds_ok P0s Qs) = true)
    (h3 : (bv_unsigned (lden Eq (rg_base RQ))) = (bv_unsigned (lden E1 (rg_base R)))) :
    (bv_unsigned x) = ((bv_unsigned (lden E1 (rg_base R))) + ((bv_unsigned x) - (bv_unsigned (lden E1 (rg_base R))))) := by
  lia

-- fast_float/from_chars: lib/Common/FxFacts.v (assert)
example
    (v : Int)
    (y : Int)
    (k : Int)
    (Zpow : Int → Int → Int)
    (z : Int)
    (u : Int)
    (t : Int)
    (t2 : Int)
    (h1 : (2 ^ (64 : Nat)) = ((Zpow 2 k) * (Zpow 2 (64 - k))))
    (h2 : 0 < (Zpow 2 k))
    (h3 : 0 < (Zpow 2 (64 - k)))
    (h4 : (Int.fmod (z - ((Zpow 2 k) * u)) (2 ^ (64 : Nat))) = 0)
    (h5 : (Int.fmod (v - u) (2 ^ (64 : Nat))) = 0)
    (h6 : y = (u + ((Zpow 2 (64 - k)) * t)))
    (h7 : (v - y) = ((Zpow 2 (64 - k)) * (((Zpow 2 k) * t2) - t)))
    (h8 : (((Zpow 2 k) * t2) - t) = 0)
    (h9 : (Zpow 2 (64 - k)) ≤ (((v - y)).natAbs : Int))
    (h10 : 1 ≤ (((((Zpow 2 k) * t2) - t)).natAbs : Int)) :
    v = y := by
  lia

-- fast_float/from_chars: lib/Common/FxLin.v (replace)
example
    {T1 T2 T3 : Type}
    (E : T1)
    (a : T2)
    (kx : Int)
    (vz : T1 → T3 → Int)
    (x : T3)
    (tsum : T1 → T2 → Int)
    (ky : Int)
    (y : T3)
    (b : T2) :
    (((kx * (vz E x)) + (tsum E a)) + ((ky * (vz E y)) + (tsum E b))) = ((ky * (vz E y)) + (((kx * (vz E x)) + (tsum E a)) + (tsum E b))) := by
  lia

-- fast_float/from_chars: lib/Common/FxNum.v (assert)
example
    {T1 T2 T3 T4 T5 : Type}
    (c : T1)
    (v : T1)
    (h_1 : T2)
    (ival : T1 → Int)
    (to_Z : T2 → Int)
    (PrimInt63_head0 : T3 → T2)
    (iabs : T1 → T3)
    (PrimInt63_leb : T4 → T5 → Bool)
    (i65 : T4)
    (PrimInt63_add : T2 → T2 → T5)
    (Zpow : Int → Int → Int)
    (hc : Int)
    (h1 : (to_Z h_1) ≤ (to_Z (PrimInt63_head0 (iabs v))))
    (h2 : (PrimInt63_leb i65 (PrimInt63_add (PrimInt63_head0 (iabs c)) h_1)) = true)
    (h3 : (((ival v)).natAbs : Int) < (Zpow 2 (63 - (to_Z h_1))))
    (h4 : ((Zpow 2 (63 - hc)) * (Zpow 2 (63 - (to_Z h_1)))) ≤ 2305843009213693952)
    (h5 : ((((ival c) * (ival v))).natAbs : Int) < 2305843009213693952) :
    0 ≤ (((ival c)).natAbs : Int) := by
  lia

-- fast_float/from_chars: lib/Common/FxNum.v (assert)
example
    {T1 T2 T3 T4 T5 : Type}
    (c : T1)
    (v : T1)
    (h_1 : T2)
    (ival : T1 → Int)
    (to_Z : T2 → Int)
    (PrimInt63_head0 : T3 → T2)
    (iabs : T1 → T3)
    (PrimInt63_leb : T4 → T5 → Bool)
    (i65 : T4)
    (PrimInt63_add : T2 → T2 → T5)
    (Zpow : Int → Int → Int)
    (hc : Int)
    (h1 : (to_Z h_1) ≤ (to_Z (PrimInt63_head0 (iabs v))))
    (h2 : (PrimInt63_leb i65 (PrimInt63_add (PrimInt63_head0 (iabs c)) h_1)) = true)
    (h3 : (((ival v)).natAbs : Int) < (Zpow 2 (63 - (to_Z h_1))))
    (h4 : ((Zpow 2 (63 - hc)) * (Zpow 2 (63 - (to_Z h_1)))) ≤ 2305843009213693952)
    (h5 : ((((ival c) * (ival v))).natAbs : Int) < 2305843009213693952)
    (h6 : 0 ≤ (((ival c)).natAbs : Int)) :
    0 ≤ (((ival v)).natAbs : Int) := by
  lia

-- fast_float/from_chars: lib/FF/P_from_chars_float.v (replace)
example (kp : Int) (k1 : Int) (kI : Int) :
    ((kp - k1) - 1) = ((kI - k1) - ((kI + 1) - kp)) := by
  lia

-- fast_float/from_chars: lib/FF/P_lib_closed.v (replace)
example
    (len : Int)
    (ylen : Int)
    (start : Int)
    (nl : Nat)
    (ny : Nat)
    (ns : Nat)
    (N_1 : Int)
    (nN : Nat)
    (j : Nat)
    (h1 : len = ((nl : Nat) : Int))
    (h2 : ylen = ((ny : Nat) : Int))
    (h3 : start = ((ns : Nat) : Int))
    (h4 : (0 ≤ len ∧ len ≤ 62))
    (h5 : (0 ≤ ylen ∧ ylen ≤ 62))
    (h6 : 0 ≤ start)
    (h7 : (ylen + start) ≤ 62)
    (h8 : N_1 = ((nN : Nat) : Int))
    (h9 : N_1 = (max len (ylen + start)))
    (h10 : j = nN)
    (h11 : N_1 ≤ 61) :
    (8 * N_1) = (N_1 * (2 ^ (3 : Nat))) := by
  lia

-- fast_float/from_chars: lib/FF/P_lib_closed.v (replace)
example
    {word list_word : Type}
    (sp : word)
    (xv : word)
    (yv : word)
    (ws : list_word)
    (ys : list_word)
    (len : Int)
    (ylen : Int)
    (start : Int)
    (nl : Nat)
    (ny : Nat)
    (ns : Nat)
    (N_1 : Int)
    (nN : Nat)
    (x0 : list_word)
    (length : list_word → Nat)
    (bv_unsigned : word → Int)
    (j : Nat)
    (w : word)
    (limbZ : list_word → Nat → Int)
    (h1 : len = ((nl : Nat) : Int))
    (h2 : ylen = ((ny : Nat) : Int))
    (h3 : start = ((ns : Nat) : Int))
    (h4 : (length ws) = 62)
    (h5 : (length ys) = 62)
    (h6 : (0 ≤ len ∧ len ≤ 62))
    (h7 : (0 ≤ ylen ∧ ylen ≤ 62))
    (h8 : 0 ≤ start)
    (h9 : (ylen + start) ≤ 62)
    (h10 : ((bv_unsigned xv) % 8) = 0)
    (h11 : ((bv_unsigned yv) % 8) = 0)
    (h12 : (bv_unsigned yv) ≠ 0)
    (h13 : ((bv_unsigned yv) + 496) < (2 ^ (64 : Nat)))
    (h14 : ((bv_unsigned sp) % 16) = 0)
    (h15 : (((bv_unsigned xv) + 498) ≤ ((bv_unsigned sp) - 48) ∨ (bv_unsigned sp) ≤ (bv_unsigned xv)))
    (h16 : (((bv_unsigned yv) + 496) ≤ ((bv_unsigned sp) - 48) ∨ (bv_unsigned sp) ≤ (bv_unsigned yv)))
    (h17 : (((bv_unsigned xv) + 498) ≤ (bv_unsigned yv) ∨ ((bv_unsigned yv) + 496) ≤ (bv_unsigned xv)))
    (h18 : N_1 = ((nN : Nat) : Int))
    (h19 : N_1 = (max len (ylen + start)))
    (h20 : (length x0) = 62)
    (h21 : j = nN)
    (h22 : N_1 ≤ 61)
    (h23 : (limbZ x0 j) = (bv_unsigned w))
    (h24 : ((bv_unsigned w) + 1) = (2 ^ (64 : Nat)))
    (h25 : ((bv_unsigned w) + 1) < (2 ^ (64 : Nat))) :
    nN = (Int.toNat N_1) := by
  lia

-- fast_float/from_chars: lib/FF/P_lib_closed.v (replace)
example
    (len : Int)
    (ylen : Int)
    (start : Int)
    (nl : Nat)
    (ny : Nat)
    (ns : Nat)
    (N_1 : Int)
    (nN : Nat)
    (i : Nat)
    (h1 : len = ((nl : Nat) : Int))
    (h2 : ylen = ((ny : Nat) : Int))
    (h3 : start = ((ns : Nat) : Int))
    (h4 : (0 ≤ len ∧ len ≤ 62))
    (h5 : (0 ≤ ylen ∧ ylen ≤ 62))
    (h6 : 0 ≤ start)
    (h7 : (ylen + start) ≤ 62)
    (h8 : N_1 = ((nN : Nat) : Int))
    (h9 : N_1 = (max len (ylen + start)))
    (h10 : (i + 1) = ny) :
    ((((((ny + ns) : Nat) : Int) - N_1) - 1) + (1 * (2 ^ (64 : Nat)))) = ((18446744073709551615 - N_1) + (ylen + start)) := by
  lia

-- fast_float/from_chars: lib/FF/P_spd_DC.v (replace)
example
    {spd_ctx T2 T3 T4 : Type}
    (c : spd_ctx)
    (bv_unsigned : T2 → Int)
    (r_sp : spd_ctx → T2)
    (length : T3 → Nat)
    (firstn : Int → T4 → T3)
    (r : T4)
    (ibs : T3)
    (kI : Int)
    (k3 : Int)
    (fbs : T3)
    (fL : Int)
    (h1 : (length (firstn 504 r)) = 504)
    (h2 : (((length ibs) : Nat) : Int) = (kI - k3))
    (h3 : (((length fbs) : Nat) : Int) = fL) :
    (((bv_unsigned (r_sp c)) + (-688)) + 32) = ((bv_unsigned (r_sp c)) + (-656)) := by
  lia

-- fast_float/from_chars: lib/FF/P_spf_DC.v (replace)
example {spf_ctx T2 : Type} (c : spf_ctx) (bv_unsigned : T2 → Int) (r_sp : spf_ctx → T2) :
    ((bv_unsigned (r_sp c)) + (-118)) = (((((bv_unsigned (r_sp c)) + (-688)) + 72) + 496) + 2) := by
  lia

-- fast_float/from_chars: lib/FF/Spf_text.v (replace)
example
    {T1 T2 : Type}
    (b : Int)
    (vl : T1 → Int)
    (l : T1)
    (cB : T2 → Int)
    (length : T1 → T2)
    (Z_testbit : Int → Int → Bool)
    (h1 : (Z_testbit (b + 70) 7) = false)
    (h2 : (Z_testbit (b + 208) 7) = false) :
    ((b + 208) + ((2 ^ (8 : Nat)) * (((vl l) + (cB (length l))) - 1))) = ((b + ((2 ^ (8 : Nat)) * (vl l))) + (208 + ((2 ^ (8 : Nat)) * ((cB (length l)) - 1)))) := by
  lia

-- fast_float/from_chars: lib/FF/Spf_text.v (replace)
example
    {T1 T2 : Type}
    (V : Int)
    (z0 : Int)
    (z1 : Int)
    (z2 : Int)
    (z3 : Int)
    (v4 : Int → Int → Int → Int → Int)
    (bv_eqb : T1 → T1 → Bool)
    (Z_to_bv : Int → Int → T1)
    (Z_land : T2 → Int → Int)
    (bv_unsigned : T1 → T2)
    (Z_lor : T2 → T2 → Int)
    (bv_swrap : Int → Int → Int)
    (i : Nat)
    (h1 : (0 ≤ z0 ∧ z0 < 256))
    (h2 : (0 ≤ z1 ∧ z1 < 256))
    (h3 : (0 ≤ z2 ∧ z2 < 256))
    (h4 : (0 ≤ z3 ∧ z3 < 256))
    (h5 : (0 ≤ V ∧ V < (2 ^ (64 : Nat))))
    (h6 : (Int.fmod V (2 ^ (32 : Nat))) = (v4 z0 z1 z2 z3))
    (h7 : (!(bv_eqb (Z_to_bv 64 (Z_land (bv_unsigned (Z_to_bv 64 (Z_lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (V + 1179010630)))) (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (V + 18446744072901087184))))))) 18446744071570489472)) (Z_to_bv 64 0))) = false)
    (h8 : (0 ≤ ((8 * ((i : Nat) : Int)) + 7) ∧ ((8 * ((i : Nat) : Int)) + 7) < 32)) :
    (((v4 z0 z1 z2 z3) + 3486502864) + (4294967295 * (2 ^ (32 : Nat)))) = ((v4 z0 z1 z2 z3) + 18446744072901087184) := by
  lia

-- fast_float/from_chars: lib/FF/U_large_add_from.v (replace)
example (n : Int) (len : Int) :
    (8 * (n - len)) = ((n - len) * (2 ^ (3 : Nat))) := by
  lia

-- fast_float/from_chars: lib/FF/U_lib_closed.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (a2 : T1) (K : Int) :
    ((bv_unsigned a2) - (K + 8)) = (((bv_unsigned a2) - K) + (-8)) := by
  lia

-- fast_float/from_chars: lib/FF/U_parse_mantissa.v (replace)
example
    {word list_word : Type}
    (yw : word)
    (ws : list_word)
    (len : Int)
    (length : list_word → Nat)
    (bval : list_word → Nat → Int)
    (bv_unsigned : word → Int)
    (BIG_CAP : Int)
    (i : Nat)
    (h1 : (length ws) = 62)
    (h2 : (0 < len ∧ len ≤ 62))
    (h3 : ((bval ws (Int.toNat len)) * (bv_unsigned yw)) < BIG_CAP)
    (h4 : (i + 1) = (Int.toNat len)) :
    (8 * len) = (len * (2 ^ (3 : Nat))) := by
  lia

-- fast_float/from_chars: lib/FF/U_slow_path_float.v (replace)
example {T1 : Type} (bv_signed : T1 → Int) (q : T1) :
    (2 * ((bv_signed q) + 342)) = ((2 * (bv_signed q)) + 684) := by
  lia

-- fast_float/from_chars: lib/FF/U_small_add.v (replace)
example
    {list_word : Type}
    (y : Int)
    (ws : list_word)
    (len : Int)
    (i : Nat)
    (length : list_word → Nat)
    (bval : list_word → Nat → Int)
    (BIG_CAP : Int)
    (h1 : (length ws) = 62)
    (h2 : (0 ≤ len ∧ len ≤ 62))
    (h3 : (0 < y ∧ y < (2 ^ (64 : Nat))))
    (h4 : ((bval ws (Int.toNat len)) + y) < BIG_CAP)
    (h5 : i = (Int.toNat len))
    (h6 : len ≤ 61)
    (h7 : (Int.toNat len) = 62) :
    (8 * len) = (len * (2 ^ (3 : Nat))) := by
  lia

-- fast_float/from_chars: lib/FFA/A_parse_mantissa.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (resv : word)
    (numv : word)
    (mdw : word)
    (dv : word)
    (iptr : word)
    (fptr : word)
    (ibs : list_byte)
    (fbs : list_byte)
    (ilen : Int)
    (flen : Int)
    (maxd : Int)
    (FS : Int)
    (THI : Int)
    (GLO : Int)
    (gi : Int)
    (gin : Int)
    (bv_unsigned : word → Int)
    (p : word)
    (off : Nat)
    (length : list_byte → Nat)
    (IMG_END : Int)
    (KHI : Int)
    (KTOP : Int)
    (FSSIZE : Int)
    (dg : Int)
    (h1 : ilen = (((length ibs) : Nat) : Int))
    (h2 : flen = (((length fbs) : Nat) : Int))
    (h3 : maxd = (bv_unsigned mdw))
    (h4 : (0 < maxd ∧ maxd ≤ 769))
    (h5 : ((bv_unsigned resv) % 8) = 0)
    (h6 : ((bv_unsigned numv) % 8) = 0)
    (h7 : ((bv_unsigned sp) % 16) = 0)
    (h8 : (bv_unsigned iptr) ≠ 0)
    (h9 : ((bv_unsigned iptr) + ilen) < (2 ^ (64 : Nat)))
    (h10 : (0 ≤ ilen ∧ ilen < (2 ^ (40 : Nat))))
    (h11 : ((bv_unsigned fptr) + flen) < (2 ^ (64 : Nat)))
    (h12 : (0 ≤ flen ∧ flen < (2 ^ (40 : Nat))))
    (h13 : IMG_END ≤ ((bv_unsigned sp) - 176))
    (h14 : KHI ≤ ((bv_unsigned sp) - 176))
    (h15 : (bv_unsigned sp) ≤ (bv_unsigned dv))
    (h16 : ((bv_unsigned dv) + 8) ≤ KTOP)
    (h17 : FS ≤ (bv_unsigned iptr))
    (h18 : ((bv_unsigned iptr) + ilen) ≤ THI)
    (h19 : ((bv_unsigned resv) + 498) ≤ ((bv_unsigned numv) + 32))
    (h20 : ((bv_unsigned numv) + 64) ≤ (GLO + FSSIZE))
    (h21 : ((THI ≤ (bv_unsigned resv) ∨ ((bv_unsigned resv) + 498) ≤ FS) ∧ ((GLO + FSSIZE) ≤ ((bv_unsigned sp) - 176) ∧ THI ≤ ((bv_unsigned sp) - 176))))
    (h22 : (0 ≤ gi ∧ gi ≤ ((bv_unsigned iptr) / 8)))
    (h23 : (((bv_unsigned iptr) + ilen) ≤ (8 * (gi + gin)) ∧ (8 * (gi + gin)) ≤ KTOP))
    (h24 : dg = maxd)
    (h25 : dg < maxd) :
    (bv_unsigned p) = ((bv_unsigned fptr) + ((off : Nat) : Int)) := by
  lia

-- fast_float/from_chars: lib/FFA/A_pow10.v (replace)
example
    {T1 : Type}
    (len : Int)
    (e0 : Int)
    (e : Int)
    (pow5_growth : Int → Int)
    (LM_T : Int)
    (lenk : Int)
    (POW5_27 : Int)
    (bval : T1 → Nat → Int)
    (wsk : T1)
    (BIG_CAP : Int)
    (h1 : (0 ≤ len ∧ len ≤ 62))
    (h2 : (0 ≤ e0 ∧ e0 < (2 ^ (31 : Nat))))
    (h3 : (len + (pow5_growth e0)) ≤ LM_T)
    (h4 : (0 : Int) < (5 ^ (27 : Nat)))
    (h5 : (pow5_growth e) = (1 + (pow5_growth (e - 27))))
    (h6 : lenk ≤ 60)
    (h7 : (POW5_27 * (bval wsk (Int.toNat lenk))) < BIG_CAP)
    (h8 : (lenk + (pow5_growth (e + (-27)))) ≤ (len + (pow5_growth e0)))
    (h9 : ((lenk + 1) + (pow5_growth (e + (-27)))) ≤ (len + (pow5_growth e0))) :
    (e - 27) = (e + (-27)) := by
  lia

-- fast_float/from_chars: lib/FFA/A_shl_bits.v (replace)
example
    {word list_word : Type}
    (sp : word)
    (vec : word)
    (nw : word)
    (ws : list_word)
    (len : Int)
    (length : list_word → Nat)
    (bv_unsigned : word → Int)
    (KHI : Int)
    (KTOP : Int)
    (i : Nat)
    (Zpow : Int → Int → Int)
    (h1 : (length ws) = 62)
    (h2 : (0 < len ∧ len ≤ 62))
    (h3 : (1 ≤ (bv_unsigned nw) ∧ (bv_unsigned nw) ≤ 63))
    (h4 : ((bv_unsigned sp) ≤ (bv_unsigned vec) ∨ ((bv_unsigned vec) + 498) ≤ ((bv_unsigned sp) + (-16))))
    (h5 : KHI ≤ ((bv_unsigned sp) + (-16)))
    (h6 : (bv_unsigned sp) ≤ KTOP)
    (h7 : ((bv_unsigned vec) + 504) ≤ KTOP)
    (h8 : (i + 1) = (Int.toNat len))
    (h9 : (Zpow 2 (bv_unsigned nw)) ≤ (2 ^ (63 : Nat))) :
    (8 * len) = (len * (2 ^ (3 : Nat))) := by
  lia

-- fast_float/from_chars: lib/FFB/B_parse_mantissa.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (resv : word)
    (numv : word)
    (mdw : word)
    (dv : word)
    (iptr : word)
    (fptr : word)
    (ibs : list_byte)
    (fbs : list_byte)
    (ilen : Int)
    (flen : Int)
    (maxd : Int)
    (FS : Int)
    (THI : Int)
    (GLO : Int)
    (gi : Int)
    (gin : Int)
    (bv_unsigned : word → Int)
    (p : word)
    (off : Nat)
    (length : list_byte → Nat)
    (IMG_END : Int)
    (KHI : Int)
    (KTOP : Int)
    (FSSIZE : Int)
    (dg : Int)
    (h1 : ilen = (((length ibs) : Nat) : Int))
    (h2 : flen = (((length fbs) : Nat) : Int))
    (h3 : maxd = (bv_unsigned mdw))
    (h4 : (0 < maxd ∧ maxd ≤ 769))
    (h5 : ((bv_unsigned resv) % 8) = 0)
    (h6 : ((bv_unsigned numv) % 8) = 0)
    (h7 : ((bv_unsigned sp) % 16) = 0)
    (h8 : (bv_unsigned iptr) ≠ 0)
    (h9 : ((bv_unsigned iptr) + ilen) < (2 ^ (64 : Nat)))
    (h10 : (0 ≤ ilen ∧ ilen < (2 ^ (40 : Nat))))
    (h11 : ((bv_unsigned fptr) + flen) < (2 ^ (64 : Nat)))
    (h12 : (0 ≤ flen ∧ flen < (2 ^ (40 : Nat))))
    (h13 : IMG_END ≤ ((bv_unsigned sp) - 176))
    (h14 : KHI ≤ ((bv_unsigned sp) - 176))
    (h15 : (bv_unsigned sp) ≤ (bv_unsigned dv))
    (h16 : ((bv_unsigned dv) + 8) ≤ KTOP)
    (h17 : FS ≤ (bv_unsigned iptr))
    (h18 : ((bv_unsigned iptr) + ilen) ≤ THI)
    (h19 : (bv_unsigned sp) ≤ ((bv_unsigned numv) + 32))
    (h20 : ((bv_unsigned numv) + 64) ≤ (bv_unsigned dv))
    (h21 : ((bv_unsigned resv) + 504) ≤ (GLO + FSSIZE))
    (h22 : ((THI ≤ (bv_unsigned resv) ∨ ((bv_unsigned resv) + 498) ≤ FS) ∧ ((GLO + FSSIZE) ≤ ((bv_unsigned sp) - 176) ∧ THI ≤ ((bv_unsigned sp) - 176))))
    (h23 : (0 ≤ gi ∧ gi ≤ ((bv_unsigned iptr) / 8)))
    (h24 : (((bv_unsigned iptr) + ilen) ≤ (8 * (gi + gin)) ∧ (8 * (gi + gin)) ≤ KTOP))
    (h25 : dg = maxd)
    (h26 : dg < maxd) :
    (bv_unsigned p) = ((bv_unsigned fptr) + ((off : Nat) : Int)) := by
  lia

-- fast_float/from_chars: lib/FXC/FxChFix.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (E : T1)
    (fs : T2)
    (n : T3)
    (b : Int)
    (k : Int)
    (wlo : Int)
    (whi : Int)
    (R : T4)
    (ub : T5)
    (u : Int)
    (s : Int)
    (SH_OFF : Int)
    (src_ok : T2 → T3 → Int → Int → T4 → T5 → Bool)
    (SH_LO : Int)
    (SH_HI : Int)
    (uE : T1 → T6 → Int)
    (laddc : T7 → Int → T6)
    (pb : T7)
    (rg_base : T4 → T6)
    (bv_unsigned : T8 → Int)
    (lden : T1 → T6 → T8)
    (ps : T6)
    (rsz : T1 → T4 → Int)
    (h1 : (src_ok fs n wlo whi R ub) = true)
    (h2 : (whi ≤ SH_LO ∨ SH_HI ≤ wlo))
    (h3 : 0 ≤ wlo)
    (h4 : b ≤ ((wlo / 8) + SH_OFF))
    (h5 : ((whi / 8) + SH_OFF) ≤ (b + k))
    (h6 : (uE E (laddc pb SH_OFF)) = (((uE E (rg_base R)) / 8) + SH_OFF))
    (h7 : ((bv_unsigned (lden E (rg_base R))) / 8) < 2305843009213693952)
    (h8 : (uE E ps) = ((rsz E R) / 8))
    (h9 : u = (8 * (u / 8)))
    (h10 : s = (8 * (s / 8)))
    (h11 : ((u + s) / 8) = ((u / 8) + (s / 8)))
    (h12 : (u / 8) ≥ (wlo / 8))
    (h13 : ((u + s) / 8) ≤ (whi / 8))
    (h14 : 0 < (s / 8)) :
    (u + s) = (8 * ((((u / 8) + SH_OFF) - SH_OFF) + (s / 8))) := by
  lia

-- fast_float/from_chars: lib/FXC/FxChSep.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (E : T1)
    (fs : T2)
    (R : T3)
    (w : Int)
    (uE : T1 → T4 → Int)
    (rg_base : T3 → T4)
    (SH_HI : Int)
    (two64 : Int)
    (sep_noshadow_b : T2 → T3 → Bool)
    (rsz : T1 → T3 → Int)
    (laddc : T4 → Int → T4)
    (h1 : (sep_noshadow_b fs R) = true)
    (h2 : ((uE E (rg_base R)) ≤ w ∧ w < ((uE E (rg_base R)) + (rsz E R))))
    (h3 : (uE E (laddc (rg_base R) (-SH_HI))) = (((uE E (rg_base R)) - SH_HI) + two64)) :
    ((((uE E (rg_base R)) - SH_HI) + two64) + ((-1) * two64)) = ((uE E (rg_base R)) + (-SH_HI)) := by
  lia

-- fast_float/from_chars: lib/FXC/FxChSep.v (replace)
example
    {valu list_fact list_____lin_lin_gkind Model lin T6 T7 T8 T9 T10 T11 : Type}
    (E : valu)
    (fs : list_fact)
    (gs : list_____lin_lin_gkind)
    (model : Model)
    (sp : lin)
    (j : T6)
    (g : lin)
    (a : lin)
    (n : Int)
    (R : T7)
    (w : Int)
    (uE : valu → lin → Int)
    (rg_base : T7 → lin)
    (SH_HI : Int)
    (two64 : Int)
    (m_vmmaps : Model → T8)
    (vm_init_sp : T8 → T9)
    (bv_unsigned : T9 → Int)
    (sp_window_hi : Int)
    (is_mark : lin → Bool)
    (fst : lin → lin)
    (gsz : valu → lin → Int)
    (SH_LO : Int)
    (SH_OFF : Int)
    (rsz : valu → T7 → Int)
    (sep_pc_b : list_fact → list_____lin_lin_gkind → T6 → lin → T7 → Bool)
    (g' : lin)
    (laddc : lin → Int → lin)
    (pb : lin)
    (gsz_lo : list_fact → lin → Int)
    (lscale : Int → lin → lin)
    (atop_pg : T8 → Int)
    (q : Int)
    (fact_hi : list_fact → lin → T10 → Int)
    (snd : T11 → T10)
    (irange : list_fact → lin → T11)
    (h1 : (bv_unsigned (vm_init_sp (m_vmmaps model))) ≤ sp_window_hi)
    (h2 : (is_mark g) = false)
    (h3 : (uE E (fst (fst g))) ≤ (uE E a))
    (h4 : ((uE E a) + n) ≤ ((uE E (fst (fst g))) + (gsz E g)))
    (h5 : ((uE E a) % 8) = 0)
    (h6 : (n % 8) = 0)
    (h7 : 0 < n)
    (h8 : SH_LO ≤ (((uE E a) / 8) + SH_OFF))
    (h9 : ((((uE E a) / 8) + SH_OFF) + (n / 8)) ≤ SH_HI)
    (h10 : 0 ≤ (rsz E R))
    (h11 : ((uE E (rg_base R)) + (rsz E R)) ≤ two64)
    (h12 : (sep_pc_b fs gs j sp R) = true)
    (h13 : ((uE E (rg_base R)) ≤ w ∧ w < ((uE E (rg_base R)) + (rsz E R))))
    (h14 : (uE E (laddc pb SH_OFF)) = (((uE E (fst (fst g'))) / 8) + SH_OFF))
    (h15 : ((uE E (fst (fst g'))) / 8) ≤ (uE E (fst (fst g'))))
    (h16 : 0 ≤ ((uE E (fst (fst g'))) / 8))
    (h17 : ((gsz_lo fs g') / 8) ≤ (gsz_lo fs g'))
    (h18 : ((gsz_lo fs g') / 8) ≤ ((gsz E g') / 8))
    (h19 : (uE E a) = (8 * ((uE E a) / 8)))
    (h20 : n = (8 * (n / 8)))
    (h21 : (uE E (lscale 8 (rg_base R))) = (8 * (uE E (rg_base R))))
    (h22 : ((uE E (fst (fst g))) + (gsz E g)) ≤ (atop_pg (m_vmmaps model)))
    (h23 : (4096 * (((uE E sp) - ((8 * 1024) * 1024)) / 4096)) ≤ (4096 * (q - 4194240)))
    (h24 : (0 ≤ (uE E (laddc (rg_base R) (-SH_HI))) ∧ (uE E (laddc (rg_base R) (-SH_HI))) ≤ (fact_hi fs (laddc (rg_base R) (-SH_HI)) (snd (irange fs (laddc (rg_base R) (-SH_HI)))))))
    (h25 : (uE E (laddc (rg_base R) (-SH_HI))) = (((uE E (rg_base R)) - SH_HI) + two64)) :
    ((((uE E (rg_base R)) - SH_HI) + two64) + ((-1) * two64)) = ((uE E (rg_base R)) + (-SH_HI)) := by
  lia

-- fast_float/from_chars: lib/FXC/FxChSplitS.v (replace)
example
    {T1 T2 T3 : Type}
    (E : T1)
    (R : T2)
    (uE : T1 → T3 → Int)
    (rg_base : T2 → T3)
    (d : Int)
    (i : Int)
    (rk_split : T2 → Bool)
    (h1 : (rk_split R) = true) :
    ((uE E (rg_base R)) + (d + i)) = (((uE E (rg_base R)) + d) + i) := by
  lia

-- fast_float/from_chars: lib/FXDB/AsanTop.v (assert)
example {T1 : Type} (sp : T1) (OFS : T1 → Int) :
    ((OFS sp) ≤ (OFS sp) ∧ (OFS sp) ≤ (OFS sp)) := by
  lia

-- fast_float/from_chars: lib/FXG/AsanImgScan.v (replace)
example
    {T1 T2 T3 : Type}
    (p : T1)
    (s : T2)
    (lo : Nat)
    (n : Nat)
    (i : Nat)
    (bscan : T1 → T2 → Nat → Nat → Bool)
    (to_Z : T3 → Int)
    (of_Z : Int → T3)
    (h1 : (bscan p s lo n) = true)
    (h2 : i < n)
    (h3 : (to_Z (of_Z (((2 * lo) : Nat) : Int))) = (((2 * lo) : Nat) : Int))
    (h4 : (to_Z (of_Z (((2 * n) : Nat) : Int))) = (((2 * n) : Nat) : Int)) :
    ((((2 * lo) : Nat) : Int) + ((((2 * i) : Nat) : Int) + 1)) = ((((2 * (lo + i)) + 1) : Nat) : Int) := by
  lia

-- fast_float/from_chars: lib/H/P_h_fuzz_base.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (a2 : T1) :
    (((2 ^ (64 : Nat)) - ((bv_unsigned a2) * 2)) + ((-1) * (2 ^ (64 : Nat)))) = (0 - ((bv_unsigned a2) * 2)) := by
  lia

-- fast_float/from_chars: lib/H/P_h_fuzz_base.v (replace)
example
    {T1 T2 T3 : Type}
    (s : Int)
    (length : T1 → Nat)
    (ob0 : T1)
    (firstn : Nat → T1 → T1)
    (buf : T1)
    (skipn : Nat → T1 → T1)
    (sp_of : T2 → Int)
    (r1 : T2)
    (bv_unsigned : T3 → Int)
    (sp : T3)
    (h1 : (length ob0) = 23)
    (h2 : (length (firstn (Int.toNat (s + 1)) ob0)) = (Int.toNat (s + 1)))
    (h3 : (length (firstn (Int.toNat (s + 1)) buf)) = (Int.toNat (s + 1)))
    (h4 : (length (skipn (Int.toNat (s + 1)) ob0)) = (Int.toNat (22 - s)))
    (h5 : (sp_of r1) = ((bv_unsigned sp) + (-80))) :
    (2 * s) = (s * 2) := by
  lia

-- fast_float/from_chars: lib/H/P_h_fuzz_base.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (length : T2 → Nat)
    (ob0 : T2)
    (firstn : Nat → T2 → T2)
    (s : Int)
    (buf : T2)
    (skipn : Nat → T2 → T2)
    (sp_of : T3 → Int)
    (r1 : T3)
    (h1 : (length ob0) = 23)
    (h2 : (length (firstn (Int.toNat (s + 1)) ob0)) = (Int.toNat (s + 1)))
    (h3 : (length (firstn (Int.toNat (s + 1)) buf)) = (Int.toNat (s + 1)))
    (h4 : (length (skipn (Int.toNat (s + 1)) ob0)) = (Int.toNat (22 - s)))
    (h5 : (sp_of r1) = ((bv_unsigned sp) + (-80))) :
    (bv_unsigned sp) = (((bv_unsigned sp) + (-80)) + ((80 : Nat) : Int)) := by
  lia

-- fast_float/from_chars: lib/H/U_h_fuzz.v (replace)
example
    {T1 T2 T3 : Type}
    (t : Int)
    (sp_of : T1 → Int)
    (r1 : T1)
    (bv_unsigned : T2 → Int)
    (sp : T2)
    (length : T3 → Nat)
    (buf0 : T3)
    (firstn : Nat → T3 → T3)
    (s : Int)
    (buf : T3)
    (skipn : Nat → T3 → T3)
    (p' : Int)
    (z : Int)
    (r3 : T1)
    (h1 : (sp_of r1) = ((bv_unsigned sp) + (-80)))
    (h2 : (length buf0) = (Int.toNat (t + 1)))
    (h3 : (length (firstn (Int.toNat (s + 1)) buf0)) = (Int.toNat (s + 1)))
    (h4 : (length (firstn (Int.toNat (s + 1)) buf)) = (Int.toNat (s + 1)))
    (h5 : (length (skipn (Int.toNat (s + 1)) buf0)) = (Int.toNat (t - s)))
    (h6 : (¬ (p' ≤ z ∧ z < (p' + (t + 1)))))
    (h7 : (sp_of r3) = ((bv_unsigned sp) + (-80))) :
    (t + 2) = ((t + 1) + 1) := by
  lia

-- fast_float/from_chars: lib/H/U_h_fuzz.v (assert)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (h1 : ((bv_unsigned sp) + (-104)) = (((bv_unsigned sp) + (-128)) + ((24 : Nat) : Int)))
    (h2 : ((bv_unsigned sp) + (-100)) = (((bv_unsigned sp) + (-104)) + ((4 : Nat) : Int)))
    (h3 : ((bv_unsigned sp) + (-96)) = (((bv_unsigned sp) + (-100)) + ((4 : Nat) : Int)))
    (h4 : ((bv_unsigned sp) + (-72)) = (((bv_unsigned sp) + (-96)) + ((24 : Nat) : Int)))
    (h5 : ((bv_unsigned sp) + (-48)) = (((bv_unsigned sp) + (-72)) + ((24 : Nat) : Int)))
    (h6 : ((bv_unsigned sp) + (-40)) = (((bv_unsigned sp) + (-48)) + ((8 : Nat) : Int)))
    (h7 : ((bv_unsigned sp) + (-24)) = (((bv_unsigned sp) + (-40)) + ((16 : Nat) : Int))) :
    (((bv_unsigned sp) - ((128 + (128 + 2576)) + 5760)) ≤ (((bv_unsigned sp) + (-128)) - 16) ∧ (((bv_unsigned sp) + (-128)) - 16) ≤ ((bv_unsigned sp) + (-128))) := by
  lia

-- fast_float/from_chars: lib/H/U_h_fuzz_base.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (o : Int)
    (f : Int)
    (ptr0 : Int)
    (rem0 : Int)
    (bs0 : list_byte)
    (rem : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : (64 ≤ (bv_unsigned sp) ∧ (bv_unsigned sp) < (2 ^ (64 : Nat))))
    (h2 : (((bv_unsigned sp) + 64) ≤ o ∧ (o + 24) < (2 ^ (64 : Nat))))
    (h3 : (((bv_unsigned sp) + 64) ≤ f ∧ ((f + 16) < (2 ^ (64 : Nat)) ∧ ((o + 24) ≤ f ∨ (f + 16) ≤ o))))
    (h4 : (1 ≤ rem0 ∧ rem0 ≤ (2 ^ (26 : Nat))))
    (h5 : (((length bs0) : Nat) : Int) = rem0)
    (h6 : (1 ≤ ptr0 ∧ (ptr0 + rem0) ≤ ((bv_unsigned sp) - 64))) :
    (((ptr0 + rem0) - rem) + 1) = ((ptr0 + rem0) - (rem - 1)) := by
  lia

-- fast_float/from_chars: lib/H/U_h_fuzz_base.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (o : Int)
    (f : Int)
    (ptr0 : Int)
    (rem0 : Int)
    (bs0 : list_byte)
    (c : Int)
    (p : Int)
    (rem : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : ((23 ≤ c ∧ c < (2 ^ (26 : Nat))) ∧ ((c % 2) = 1 ∧ (min 128 rem0) ≤ c)))
    (h2 : (0 ≤ p ∧ (((p + c) + 1) ≤ ((bv_unsigned sp) - 64) ∧ (((p + c) + 1) ≤ ptr0 ∨ (ptr0 + rem0) ≤ p))))
    (h3 : (64 ≤ (bv_unsigned sp) ∧ (bv_unsigned sp) < (2 ^ (64 : Nat))))
    (h4 : (((bv_unsigned sp) + 64) ≤ o ∧ (o + 24) < (2 ^ (64 : Nat))))
    (h5 : (((bv_unsigned sp) + 64) ≤ f ∧ ((f + 16) < (2 ^ (64 : Nat)) ∧ ((o + 24) ≤ f ∨ (f + 16) ≤ o))))
    (h6 : (1 ≤ rem0 ∧ rem0 ≤ (2 ^ (26 : Nat))))
    (h7 : (((length bs0) : Nat) : Int) = rem0)
    (h8 : (1 ≤ ptr0 ∧ (ptr0 + rem0) ≤ ((bv_unsigned sp) - 64))) :
    (((ptr0 + rem0) - rem) + 2) = ((ptr0 + rem0) - (rem - 2)) := by
  lia

-- fast_float/from_chars: lib/HX/HxSw4W.v (replace)
example
    {list_byte : Type}
    (bs : list_byte)
    (T : Int)
    (FP : Int)
    (Y0 : Int)
    (Y1 : Int)
    (kc : Int)
    (length : list_byte → Nat)
    (h1 : (1 ≤ (((length bs) : Nat) : Int) ∧ (((length bs) : Nat) : Int) ≤ 128))
    (h2 : (6529024 ≤ T ∧ T ≤ 140737488355072))
    (h3 : ((8 * Y0) ≤ T ∧ (T + (((length bs) : Nat) : Int)) ≤ (8 * Y1)))
    (h4 : T ≤ FP)
    (h5 : (FP - T) ≤ kc)
    (h6 : (kc + 4) ≤ (((length bs) : Nat) : Int)) :
    (kc + 4) = (((T + kc) + 4) - T) := by
  lia

-- fast_float/from_chars: lib/HXB/HxExpBF.v (replace)
example
    {T1 T2 : Type}
    (Pz : Int)
    (Tz : Int)
    (Lz : Int)
    (two64 : Int)
    (getr : T1 → Int → Int)
    (ms_regs : T2 → T1)
    (ms : T2)
    (Z_to_bv : Int → Int → Int)
    (h1 : (Int.fmod (Tz + Lz) two64) = (Tz + Lz))
    (h2 : (Tz ≤ Pz ∧ Pz < (Tz + Lz)))
    (h3 : (getr (ms_regs ms) 25) = (Z_to_bv 64 (Tz + (Pz - Tz)))) :
    Pz = (Tz + (Pz - Tz)) := by
  lia

-- fast_float/from_chars: lib/HXB/HxSemB.v (replace)
example
    {T1 : Type}
    (T : Int)
    (bs : T1)
    (T' : Int)
    (bs' : T1)
    (a : Int)
    (b : Int)
    (k : Int)
    (length : T1 → Nat)
    (h1 : T ≤ a)
    (h2 : b ≤ (T + (((length bs) : Nat) : Int)))
    (h3 : T' ≤ a)
    (h4 : b ≤ (T' + (((length bs') : Nat) : Int))) :
    ((k + T) - T') = ((T + k) - T') := by
  lia

-- fast_float/from_chars: lib/HXB/HxSw4BF.v (replace)
example
    {list_byte : Type}
    (bs : list_byte)
    (T : Int)
    (FP : Int)
    (Y0 : Int)
    (Y1 : Int)
    (kc : Int)
    (length : list_byte → Nat)
    (h1 : (1 ≤ (((length bs) : Nat) : Int) ∧ (((length bs) : Nat) : Int) ≤ 128))
    (h2 : (6537216 ≤ T ∧ T ≤ 140737488355072))
    (h3 : ((8 * Y0) ≤ T ∧ (T + (((length bs) : Nat) : Int)) ≤ (8 * Y1)))
    (h4 : T ≤ FP)
    (h5 : ((FP - T) ≤ kc ∧ kc ≤ (((length bs) : Nat) : Int))) :
    kc = ((T + kc) - T) := by
  lia

-- fast_float/from_chars: lib/HXB/HxSw8BF.v (replace)
example
    {T1 T2 T3 : Type}
    (Xz : Int)
    (Tz : Int)
    (Lz : Int)
    (two64 : Int)
    (A1z : Int)
    (S8z : Int)
    (ASAN_B : Int)
    (d : Int)
    (SHBz : Int)
    (getr : T1 → Int → Int)
    (ms_regs : T2 → T1)
    (ms : T2)
    (Z_to_bv : Int → Int → Int)
    (length : T3 → Nat)
    (bs : T3)
    (Y0z : Int)
    (Y1z : Int)
    (h1 : (Int.fmod (Tz + Lz) two64) = (Tz + Lz))
    (h2 : (Tz ≤ Xz ∧ (Xz + 8) ≤ (Tz + Lz)))
    (h3 : A1z = ((Tz + Lz) - Xz))
    (h4 : S8z = (ASAN_B + (Xz / 8)))
    (h5 : (0 ≤ d ∧ d ≤ (2 ^ (48 : Nat))))
    (h6 : (Int.fmod (8 * d) two64) = (8 * d))
    (h7 : ((8 * d) ≤ Xz ∧ Xz ≤ ((8 * d) + 7)))
    (h8 : d = (Xz / 8))
    (h9 : d = (S8z - SHBz))
    (h10 : (getr (ms_regs ms) 10) = (Z_to_bv 64 10))
    (h11 : (getr (ms_regs ms) 13) = (Z_to_bv 64 7))
    (h12 : (getr (ms_regs ms) 17) = (Z_to_bv 64 14974415777481871312))
    (h13 : (getr (ms_regs ms) 28) = (Z_to_bv 64 9259542123273814144))
    (h14 : (getr (ms_regs ms) 29) = (Z_to_bv 64 5063812098665367110))
    (h15 : (getr (ms_regs ms) 30) = (Z_to_bv 64 100000000))
    (h16 : (getr (ms_regs ms) 31) = (Z_to_bv 64 4294967296000100))
    (h17 : (getr (ms_regs ms) 25) = (Z_to_bv 64 42949672960001))
    (h18 : (getr (ms_regs ms) 26) = (Z_to_bv 64 1095216660735))
    (h19 : (getr (ms_regs ms) 19) = (Z_to_bv 64 ASAN_B))
    (h20 : (getr (ms_regs ms) 24) = (Z_to_bv 64 (Tz + (Xz - Tz))))
    (h21 : (getr (ms_regs ms) 6) = (Z_to_bv 64 (Tz + (Xz - Tz))))
    (h22 : (getr (ms_regs ms) 11) = (Z_to_bv 64 ((((length bs) : Nat) : Int) - (Xz - Tz))))
    (h23 : (getr (ms_regs ms) 1) = (Z_to_bv 64 (ASAN_B + ((Tz + (Xz - Tz)) / 8))))
    (h24 : (getr (ms_regs ms) 12) = (Z_to_bv 64 ((Tz + (Xz - Tz)) + 7)))
    (h25 : (getr (ms_regs ms) 27) = (getr (ms_regs ms) 16))
    (h26 : (1 ≤ (((length bs) : Nat) : Int) ∧ (((length bs) : Nat) : Int) ≤ 128))
    (h27 : (6537216 ≤ Tz ∧ Tz ≤ 140737488355072))
    (h28 : ((8 * Y0z) ≤ Tz ∧ (Tz + (((length bs) : Nat) : Int)) ≤ (8 * Y1z)))
    (h29 : Tz ≤ Xz) :
    (Xz - Tz) = (Xz - Tz) := by
  lia

-- fast_float/from_chars: lib/HXB/HxTmBF.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (IEz : Int)
    (fLz : Int)
    (Tz : Int)
    (Lz : Int)
    (two64 : Int)
    (Sz : Int)
    (r6z : Int)
    (r16z : Int)
    (EXPMAX : Int)
    (evz : Int)
    (Z_to_bv : Int → Int → Int)
    (lden : T1 → T2 → Int)
    (E : T1)
    (rgl : Int → Int → T2)
    (length : T3 → Nat)
    (bs : T3)
    (getr : T4 → Int → Int)
    (ms_regs : T5 → T4)
    (ms : T5)
    (bv_unsigned : Int → Int)
    (S1z : Int)
    (fpz : Int)
    (ASAN_B : Int)
    (Rc : T6)
    (rg_base : T6 → T2)
    (o : Int)
    (h1 : (Int.fmod (Tz + Lz) two64) = (Tz + Lz))
    (h2 : ((Tz ≤ Sz ∧ Sz ≤ IEz) ∧ IEz ≤ (Tz + Lz)))
    (h3 : r6z = ((IEz - Sz) + fLz))
    (h4 : r16z = (IEz - Sz))
    (h5 : ((-EXPMAX) ≤ evz ∧ evz ≤ EXPMAX))
    (h6 : (Z_to_bv 64 evz) = (lden E (rgl (((length bs) : Nat) : Int) 7)))
    (h7 : (getr (ms_regs ms) 1) = (Z_to_bv 64 46))
    (h8 : (getr (ms_regs ms) 9) = (Z_to_bv 64 S1z))
    (h9 : (getr (ms_regs ms) 10) = (Z_to_bv 64 IEz))
    (h10 : (getr (ms_regs ms) 21) = (Z_to_bv 64 Sz))
    (h11 : (getr (ms_regs ms) 29) = (Z_to_bv 64 fpz))
    (h12 : (getr (ms_regs ms) 6) = (Z_to_bv 64 (((IEz - Tz) - (Sz - Tz)) + fLz)))
    (h13 : (getr (ms_regs ms) 16) = (Z_to_bv 64 (IEz - Sz)))
    (h14 : (getr (ms_regs ms) 7) = (Z_to_bv 64 evz))
    (h15 : (getr (ms_regs ms) 22) = (Z_to_bv 64 (Tz + Lz)))
    (h16 : (getr (ms_regs ms) 19) = (Z_to_bv 64 ASAN_B))
    (h17 : ((bv_unsigned (lden E (rg_base Rc))) + o) = (S1z + 48))
    (h18 : IEz < (Tz + Lz)) :
    (((IEz + 1) + fLz) - Tz) = (((IEz - Tz) + 1) + fLz) := by
  lia

-- fast_float/from_chars: lib/HXH/HxRebyte.v (replace)
example
    {T1 T2 T3 : Type}
    (Zpos : T1 → Int)
    (p : T1)
    (length : T2 → Nat)
    (cbvs : Int → Nat → T2)
    (cval : T3 → Int)
    (bs : T3)
    (n : Nat)
    (two64 : Int)
    (Zpow : Int → Int → Int)
    (o : Int)
    (nth : Nat → T3 → Int → Int)
    (h1 : (length (cbvs (cval bs) n)) = n)
    (h2 : (0 ≤ (cval bs) ∧ (cval bs) < two64))
    (h3 : (Zpow 256 ((n : Nat) : Int)) ≤ (256 ^ (8 : Nat)))
    (h4 : (0 ≤ (nth (Int.toNat (((Zpos p) - 1) - o)) bs 0) ∧ (nth (Int.toNat (((Zpos p) - 1) - o)) bs 0) < 256)) :
    (Zpos p) = (((Zpos p) - 1) + 1) := by
  lia

-- fast_float/from_chars: lib/HXH/HxRecell.v (replace)
example
    (k : Int)
    (Zpow : Int → Int → Int)
    (v : Int)
    (h1 : 0 < (Zpow 2 k))
    (h2 : (0 ≤ (Int.fdiv v (Zpow 2 k)) ∧ (Int.fdiv v (Zpow 2 k)) < (Zpow 2 (64 - k)))) :
    64 = (k + (64 - k)) := by
  lia

-- fast_float/from_chars: lib/KX/KxBridge.v (replace)
example
    (A : Int)
    (n : Nat)
    (i : Nat)
    (h1 : 0 ≤ A)
    (h2 : (A + ((n : Nat) : Int)) ≤ (2 ^ (64 : Nat))) :
    (A + (((i + 1) : Nat) : Int)) = ((A + 1) + ((i : Nat) : Int)) := by
  lia

-- fast_float/from_chars: lib/MAX/AXF_t0a.v (assert)
example
    {T1 T2 : Type}
    (W : Int)
    (idx : Int)
    (avail : Int)
    (freed : Int)
    (Z_testbit : Int → Int → Bool)
    (bv_unsigned : T1 → Int)
    (ev : T2 → Int → T1)
    (E : T2)
    (h1 : (0 ≤ W ∧ W ≤ ((2 ^ (64 : Nat)) - 1)))
    (h2 : (0 ≤ idx ∧ idx ≤ 31))
    (h3 : (0 ≤ avail ∧ avail ≤ ((2 ^ (32 : Nat)) - 1)))
    (h4 : (0 ≤ freed ∧ freed ≤ ((2 ^ (32 : Nat)) - 1)))
    (h5 : (Z_testbit avail idx) = false)
    (h6 : (Z_testbit freed idx) = false)
    (h7 : freed = 0)
    (h8 : (bv_unsigned (ev E 33)) = W)
    (h9 : (bv_unsigned (ev E 34)) = idx)
    (h10 : (bv_unsigned (ev E 36)) = avail)
    (h11 : (bv_unsigned (ev E 37)) = freed)
    (h12 : (0 ≤ avail ∧ avail < (2 ^ (32 : Nat)))) :
    (0 ≤ freed ∧ freed < (2 ^ (32 : Nat))) := by
  lia

-- fast_float/from_chars: lib/MAX/AXG_mwt.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (x : Int)
    (ly_ctx : T1 → Int)
    (L : T1)
    (bv_unsigned : T2 → Int)
    (getr : T3 → Int → T2)
    (regs : T3)
    (sp : Int)
    (memv : Int)
    (ly_reg : T1 → T4 → Int)
    (prid : T5 → T4)
    (am_mem : T6 → T5)
    (am : T6)
    (poff : T5 → Int)
    (stv : Int)
    (stride_of : T6 → Int)
    (k : Int)
    (am_last : T6 → Int)
    (group_extent : T6 → Int)
    (IB : Int)
    (HTOP : Int)
    (K : Int)
    (h1 : (bv_unsigned (getr regs 2)) = sp)
    (h2 : memv = ((ly_reg L (prid (am_mem am))) + (poff (am_mem am))))
    (h3 : stv = ((memv + 16) + ((stride_of am) * k)))
    (h4 : (0 ≤ ((stride_of am) * k) ∧ ((stride_of am) * k) ≤ ((stride_of am) * (am_last am))))
    (h5 : (16 ≤ (stv - memv) ∧ ((stv + (stride_of am)) ≤ ((memv + (group_extent am)) + IB) ∧ (0 < memv ∧ ((memv + (group_extent am)) + IB) ≤ HTOP))))
    (h6 : ((memv + (group_extent am)) + IB) ≤ (sp - K)) :
    (x + 1) = (((ly_ctx L) + (x - (ly_ctx L))) + ((1 : Nat) : Int)) := by
  lia

-- fast_float/from_chars: lib/MAX/AXG_mwt.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (stv : Int)
    (d : Int)
    (memv : Int)
    (L : T1)
    (bv_unsigned : T2 → Int)
    (getr : T3 → Int → T2)
    (regs : T3)
    (sp : Int)
    (ly_reg : T1 → T4 → Int)
    (prid : T5 → T4)
    (am_mem : T6 → T5)
    (am : T6)
    (poff : T5 → Int)
    (stride_of : T6 → Int)
    (k : Int)
    (am_last : T6 → Int)
    (group_extent : T6 → Int)
    (IB : Int)
    (HTOP : Int)
    (K : Int)
    (Gv : Int)
    (ctr' : Int)
    (am_maplen : T6 → Int)
    (Z_shiftr : Int → Int → Int)
    (meta_bits : T6 → Int)
    (Z_land : Int → Int → Int)
    (ef_dstride : Int → Int)
    (ef_dsz : Int → Int)
    (h1 : (bv_unsigned (getr regs 2)) = sp)
    (h2 : memv = ((ly_reg L (prid (am_mem am))) + (poff (am_mem am))))
    (h3 : stv = ((memv + 16) + ((stride_of am) * k)))
    (h4 : (0 ≤ ((stride_of am) * k) ∧ ((stride_of am) * k) ≤ ((stride_of am) * (am_last am))))
    (h5 : (16 ≤ (stv - memv) ∧ ((stv + (stride_of am)) ≤ ((memv + (group_extent am)) + IB) ∧ (0 < memv ∧ ((memv + (group_extent am)) + IB) ≤ HTOP))))
    (h6 : ((memv + (group_extent am)) + IB) ≤ (sp - K))
    (h7 : (((stv - 4) + (stride_of am)) ≤ (Gv + 16) ∨ (Gv + 40) ≤ (stv - 4)))
    (h8 : (0 ≤ ctr' ∧ ctr' ≤ ((2 ^ (64 : Nat)) - 1)))
    (h9 : k = 0)
    (h10 : (4096 * (am_maplen am)) ≤ (2 ^ (47 : Nat)))
    (h11 : (stride_of am) = (((am_maplen am) * 4096) - 16))
    (h12 : (Z_shiftr (meta_bits am) 12) = (am_maplen am))
    (h13 : (Z_land (meta_bits am) 31) = 0)
    (h14 : (4096 ≤ (meta_bits am) ∧ (meta_bits am) ≤ ((2 ^ (63 : Nat)) - 1)))
    (h15 : (ef_dstride (meta_bits am)) = (stride_of am))
    (h16 : (16 * (ef_dsz (meta_bits am))) = (stride_of am))
    (h17 : stv = (memv + 16)) :
    ((stv - 4) + d) = ((memv + 12) + d) := by
  lia

-- fast_float/from_chars: lib/MAX/MngBud.v (replace)
example
    {T1 : Type}
    (B : Int)
    (n : Int)
    (cur : Int)
    (CH : T1 → Int)
    (KBrkGrow : Int → T1)
    (PGSZ : Int)
    (h1 : (CH (KBrkGrow n)) ≤ B)
    (h2 : PGSZ ≤ cur)
    (h3 : (Int.fmod cur PGSZ) = 0)
    (h4 : 1 ≤ n)
    (h5 : ((cur + (PGSZ * n)) + PGSZ) < (2 ^ (64 : Nat))) :
    n = (max 0 n) := by
  lia

-- fast_float/from_chars: lib/MAX/MngGM.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (sz : Int)
    (i : Int)
    (s : T1)
    (rsv_code : T2 → T3 → Int)
    (am : T2)
    (fr : T3)
    (hdr_byte3 : T2 → Int → T3 → Int)
    (Z_land : Int → Int → Int)
    (p : T4)
    (stride_of : T2 → Int)
    (st_init_done : T1 → Bool)
    (Z_testbit : T5 → Int → Bool)
    (am_avail : T2 → T5)
    (am_freed : T2 → T5)
    (poff : T4 → Int)
    (class_size : Int → Int)
    (am_sc : T2 → Int)
    (UNIT : Int)
    (fr_off : T3 → Int)
    (am_maplen : T2 → Int)
    (h1 : 0 ≤ (rsv_code am fr))
    (h2 : (Z_land (hdr_byte3 am i fr) 31) = i)
    (h3 : (((stride_of am) * i) / 16) = (((stride_of am) / 16) * i))
    (h4 : (st_init_done s) = true)
    (h5 : ((Z_testbit (am_avail am) i) = false ∧ (Z_testbit (am_freed am) i) = false))
    (h6 : ((poff p) % 16) = 0)
    (h7 : ((((stride_of am) * i) / 16) * 16) = ((stride_of am) * i))
    (h8 : (class_size (am_sc am)) = (16 * sz))
    (h9 : (sz * i) ≤ ((Int.fdiv ((stride_of am) * i) UNIT) + (fr_off fr)))
    (h10 : i = 0)
    (h11 : ((sz * i) * 16) ≤ ((((stride_of am) * i) / 16) * 16))
    (h12 : ((Int.fdiv ((stride_of am) * i) UNIT) + (fr_off fr)) < (sz * (i + 1)))
    (h13 : (stride_of am) = (class_size (am_sc am)))
    (h14 : (stride_of am) = (((am_maplen am) * 4096) - UNIT))
    (h15 : (am_sc am) = 27) :
    ((sz * i) * 16) = ((16 * sz) * i) := by
  lia

-- fast_float/from_chars: lib/MAX/MngZ.v (assert)
example (y : Int) (lb : Int) (hb : Int) (h1 : y = lb) :
    ((y).natAbs : Int) ≤ (max ((lb).natAbs : Int) ((hb).natAbs : Int)) := by
  lia

-- fast_float/from_chars: lib/MAXU/AXG_ag14.v (replace)
example
    {layout : Type}
    (L : layout)
    (x : Int)
    (z1 : Int)
    (z2 : Int)
    (ly_ctx : layout → Int)
    (h1 : (0 ≤ z1 ∧ z1 < 256))
    (h2 : (0 ≤ z2 ∧ z2 < 256))
    (h3 : 0 ≤ x)
    (h4 : (x + 2) ≤ (2 ^ (64 : Nat))) :
    x = ((ly_ctx L) + (x - (ly_ctx L))) := by
  lia

-- fast_float/from_chars: lib/MAXU/AXG_nF.v (replace)
example
    (G : Int)
    (n : Nat)
    (sp0 : Int)
    (H : Int)
    (HP : Int)
    (h1 : (1 ≤ G ∧ (G + 40) ≤ (sp0 - 1024)))
    (h2 : (1 ≤ H ∧ (H + 40) ≤ (sp0 - 1024)))
    (h3 : (1 ≤ HP ∧ (HP + 40) ≤ (sp0 - 1024)))
    (h4 : ((2 ^ (20 : Nat)) ≤ sp0 ∧ sp0 ≤ (2 ^ (47 : Nat))))
    (h5 : (H = HP ∨ ((H + 40) ≤ HP ∨ (HP + 40) ≤ H))) :
    ((G + 24) + (((n + 4) : Nat) : Int)) = ((G + 28) + ((n : Nat) : Int)) := by
  lia

-- fast_float/from_chars: lib/MAXU/AXG_nF.v (replace)
example
    (G : Int)
    (n : Nat)
    (sp0 : Int)
    (H : Int)
    (h1 : (1 ≤ G ∧ (G + 40) ≤ (sp0 - 1024)))
    (h2 : (1 ≤ H ∧ (H + 40) ≤ (sp0 - 1024)))
    (h3 : ((2 ^ (20 : Nat)) ≤ sp0 ∧ sp0 ≤ (2 ^ (47 : Nat))))
    (h4 : (H = H ∨ ((H + 40) ≤ H ∨ (H + 40) ≤ H))) :
    ((G + 24) + (((n + 4) : Nat) : Int)) = ((G + 28) + ((n : Nat) : Int)) := by
  lia

-- fast_float/from_chars: lib/PDrvMain.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp0 : T1) :
    ((bv_unsigned sp0) + (((8 + (8 * 1)) : Nat) : Int)) = ((bv_unsigned sp0) + 16) := by
  lia

-- glaze/binary_reflection: lib/AsAinvOpsPf3d.v (replace)
example
    (p' : Int)
    (AS_HEAPLO : Int)
    (SBEG : Int)
    (n : Int)
    (p : Int)
    (rz : Int → Int)
    (blk_class : Int → Int)
    (KSPACE : Int)
    (rounded : Int → Int)
    (PG : Int)
    (needed : Int → Int)
    (T : Int)
    (BATCHCLASS : Int)
    (c0 : Int)
    (h1 : AS_HEAPLO ≤ SBEG)
    (h2 : (1 ≤ (needed n) ∧ (needed n) ≤ 65536))
    (h3 : (needed n) = ((rounded n) + (rz n)))
    (h4 : ((T + PG) ≤ SBEG ∨ ((SBEG + KSPACE) + PG) ≤ T))
    (h5 : ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ ((blk_class n) * (2 ^ (32 : Nat))))
    (h6 : (((blk_class n) * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c0 * (2 ^ (32 : Nat))))
    (h7 : ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (BATCHCLASS * (2 ^ (32 : Nat))))
    (h8 : ((BATCHCLASS * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c0 * (2 ^ (32 : Nat))))
    (h9 : p' = p) :
    p' = ((p' - 16) + 16) := by
  lia

-- glaze/binary_reflection: lib/AsAinvOpsPf3d.v (replace)
example
    {T1 T2 : Type}
    (c0 : Int)
    (AS_HEAPLO : Int)
    (SBEG : Int)
    (n : Int)
    (p : Int)
    (rz : Int → Int)
    (blk_class : Int → Int)
    (KSPACE : Int)
    (rounded : Int → Int)
    (PG : Int)
    (needed : Int → Int)
    (b : T1)
    (T : Int)
    (BATCHCLASS : Int)
    (p' : Int)
    (i : Nat)
    (length : T2 → Nat)
    (ba_items : T1 → T2)
    (tq' : T2)
    (j : Nat)
    (h1 : AS_HEAPLO ≤ SBEG)
    (h2 : (1 ≤ (needed n) ∧ (needed n) ≤ 65536))
    (h3 : (needed n) = ((rounded n) + (rz n)))
    (h4 : ((T + PG) ≤ SBEG ∨ ((SBEG + KSPACE) + PG) ≤ T))
    (h5 : ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ ((blk_class n) * (2 ^ (32 : Nat))))
    (h6 : (((blk_class n) * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c0 * (2 ^ (32 : Nat))))
    (h7 : ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (BATCHCLASS * (2 ^ (32 : Nat))))
    (h8 : ((BATCHCLASS * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c0 * (2 ^ (32 : Nat))))
    (h9 : p' = p)
    (h10 : i = (length tq'))
    (h11 : j = (length (ba_items b))) :
    ((c0 + 1) * (2 ^ (32 : Nat))) = ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) := by
  lia

-- glaze/binary_reflection: lib/AsAinvOpsQ23.v (replace)
example
    {T1 T2 T3 : Type}
    (c0 : Int)
    (AS_HEAPLO : Int)
    (SBEG : Int)
    (BATCHCLASS : Int)
    (k : T1)
    (st : T2)
    (ba : Int)
    (chunk_of_compact : Int → Int → T1 → Int)
    (a_tq : T2 → T3)
    (n : Int)
    (p : Int)
    (rz : Int → Int)
    (blk_class : Int → Int)
    (KSPACE : Int)
    (rounded : Int → Int)
    (PG : Int)
    (needed : Int → Int)
    (T : Int)
    (p' : Int)
    (length : T3 → Nat)
    (i : Nat)
    (h1 : AS_HEAPLO ≤ SBEG)
    (h2 : (1 ≤ BATCHCLASS ∧ BATCHCLASS ≤ 30))
    (h3 : ba = (chunk_of_compact SBEG BATCHCLASS k))
    (h4 : (1 ≤ (needed n) ∧ (needed n) ≤ 65536))
    (h5 : (needed n) = ((rounded n) + (rz n)))
    (h6 : ((T + PG) ≤ SBEG ∨ ((SBEG + KSPACE) + PG) ≤ T))
    (h7 : ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (BATCHCLASS * (2 ^ (32 : Nat))))
    (h8 : ((BATCHCLASS * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c0 * (2 ^ (32 : Nat))))
    (h9 : ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ ((blk_class n) * (2 ^ (32 : Nat))))
    (h10 : (((blk_class n) * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c0 * (2 ^ (32 : Nat))))
    (h11 : p' = p)
    (h12 : i = (length (a_tq st))) :
    ((c0 + 1) * (2 ^ (32 : Nat))) = ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) := by
  lia

-- glaze/binary_reflection: lib/AsAinvOpsRc43.v (replace)
example
    (c : Int)
    (m : Int)
    (T : Int)
    (PG : Int)
    (SBEG : Int)
    (KSPACE : Int)
    (AS_HEAPLO : Int)
    (c' : Int)
    (c0 : Int)
    (h1 : m ≤ 16)
    (h2 : ((T + PG) ≤ SBEG ∨ ((SBEG + KSPACE) + PG) ≤ T))
    (h3 : AS_HEAPLO ≤ SBEG)
    (h4 : ((c * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c' * (2 ^ (32 : Nat))))
    (h5 : ((c' * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c * (2 ^ (32 : Nat))))
    (h6 : ((c * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c0 * (2 ^ (32 : Nat)))) :
    ((c + 1) * (2 ^ (32 : Nat))) = ((c * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) := by
  lia

-- glaze/binary_reflection: lib/AsAinvOpsRc43.v (replace)
example
    {T1 T2 T3 : Type}
    (st : T1)
    (c : Int)
    (m : Int)
    (length : T2 → Nat)
    (r_free : T3 → T2)
    (a_reg : T1 → Int → T3)
    (r_mapped_fa : T3 → Int)
    (BATCHCLASS : Int)
    (h1 : (1 ≤ c ∧ c ≤ 30))
    (h2 : 0 ≤ m)
    (h3 : (4 * ((((length (r_free (a_reg st c))) : Nat) : Int) + m)) ≤ (r_mapped_fa (a_reg st c)))
    (h4 : (1 ≤ BATCHCLASS ∧ BATCHCLASS ≤ 30))
    (h5 : ((c * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (BATCHCLASS * (2 ^ (32 : Nat)))) :
    ((c + 1) * (2 ^ (32 : Nat))) = ((c * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) := by
  lia

-- glaze/binary_reflection: lib/AsAinvOpsRc73.v (replace)
example
    (a : Int)
    (z : Int)
    (BATCHCLASS : Int)
    (BATCHSZ : Int)
    (c0 : Int)
    (h1 : (a ≤ z ∧ z < (a + BATCHSZ)))
    (h2 : (1 ≤ BATCHCLASS ∧ BATCHCLASS ≤ 30))
    (h3 : ((c0 * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (BATCHCLASS * (2 ^ (32 : Nat))))
    (h4 : ((BATCHCLASS * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (c0 * (2 ^ (32 : Nat)))) :
    ((BATCHCLASS + 1) * (2 ^ (32 : Nat))) = ((BATCHCLASS * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) := by
  lia

-- glaze/binary_reflection: lib/AsAllocFRc4a.v (replace)
example
    {list_byte word T3 T4 : Type}
    (T : Int)
    (spb : Int)
    (c : Int)
    (e : Int)
    (cnt : Int)
    (mx : Int)
    (bst : list_byte)
    (bcs : list_byte)
    (Z_to_bv : Int → Int → word)
    (length : list_byte → Nat)
    (store_ok : T3 → T4 → word → Nat → Bool)
    (ASEGS : T3)
    (mem : T4)
    (h1 : (0 ≤ spb ∧ (spb + (2 ^ (37 : Nat))) < (2 ^ (47 : Nat))))
    (h2 : (1 ≤ c ∧ c ≤ 30))
    (h3 : (0 ≤ e ∧ e < (2 ^ (32 : Nat))))
    (h4 : ((0 ≤ cnt ∧ cnt < mx) ∧ mx ≤ 16))
    (h5 : (length bst) = 8)
    (h6 : (length bcs) = 8)
    (h7 : (store_ok ASEGS mem (Z_to_bv 64 T) (Int.toNat 4096)) = true) :
    ((4 * cnt) * (2 ^ (30 : Nat))) = (cnt * (2 ^ (32 : Nat))) := by
  lia

-- glaze/binary_reflection: lib/AsDepotTop3.v (replace)
example (sz : Int) :
    (0 + sz) = (((0 + sz) + 1) - 1) := by
  lia

-- glaze/binary_reflection: lib/AsRtStkLift.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (sp : Int)
    (ia_img_lo : T1 → Int)
    (bt_ia : T2 → T1)
    (bt : T2)
    (ia_tp : T1 → Int)
    (ia_img_hi : T1 → Int)
    (FCAP : T3 → Int)
    (k : T3)
    (pos : Int)
    (busy : Int → Bool)
    (hint : Int)
    (fs : Int)
    (skf_frame : T3 → Int → Int → T4 → Int)
    (i0 : T4)
    (f : Int)
    (skf_sh : T3 → Int → Int → T4 → Int)
    (sh_lo : Int → Int)
    (FSK : T3 → Int)
    (FS : T3 → Int)
    (U : T5 → Int)
    (fsw : T5)
    (tg_res : T6 → T5)
    (VV : T6)
    (sh_hi : Int → Int → Int)
    (FAKE_SIZE : Int)
    (h1 : (((ia_img_lo (bt_ia bt)) + 88) ≤ (ia_tp (bt_ia bt)) ∧ ((ia_tp (bt_ia bt)) + 16) ≤ (ia_img_hi (bt_ia bt))))
    (h2 : 0 < (FCAP k))
    (h3 : (0 ≤ pos ∧ pos < (FCAP k)))
    (h4 : (busy pos) = true)
    (h5 : (skf_frame k fs hint i0) = f)
    (h6 : (skf_sh k fs hint i0) = (sh_lo f))
    (h7 : (FSK k) = (FS k))
    (h8 : (U fsw) = fs)
    (h9 : (U (tg_res VV)) = (ia_tp (bt_ia bt)))
    (h10 : ((sh_hi f (FS k)) = ((sh_lo f) + ((FS k) / 8)) ∧ (2147450880 ≤ (sh_lo f) ∧ (((sh_lo f) + ((FS k) / 8)) ≤ 17594333495296 ∧ ((sh_lo fs) ≤ (sh_lo f) ∧ ((sh_lo f) + ((FS k) / 8)) ≤ (sh_hi fs FAKE_SIZE))))))
    (h11 : 0 ≤ ((FS k) / 8)) :
    208 = (sp - (sp - 208)) := by
  lia

-- glaze/binary_reflection: lib/AzBridgeAnn.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (bt : T1)
    (bv_signed : T1 → Int)
    (h1 : ((bv_signed bt) = (bv_unsigned bt) ∨ (bv_signed bt) = ((bv_unsigned bt) - 256))) :
    (((bv_unsigned bt) - 128) + (1 * 256)) = ((bv_unsigned bt) + 128) := by
  lia

-- glaze/binary_reflection: lib/AzCall.v (replace)
example
    {atable gtable T3 T4 T5 T6 T7 T8 : Type}
    (A : atable)
    (G : gtable)
    (E : T3)
    (k : T4)
    (sb : T5)
    (sk : T6)
    (ne : T7)
    (estart : T3 → T8 → Int)
    (SA : T5 → T6 → T8)
    (kb : T5)
    (kk : T6)
    (i : Int)
    (img_hi : atable → Int)
    (g_img_hi : gtable → Int)
    (SHMAPLO : Int)
    (kn_readable_x : T4 → T5 → T6 → T7 → Bool)
    (h1 : (img_hi A) = (g_img_hi G))
    (h2 : (g_img_hi G) ≤ SHMAPLO)
    (h3 : (kn_readable_x k sb sk ne) = true) :
    ((estart E (SA kb kk)) + (((estart E (SA sb sk)) - (estart E (SA kb kk))) + i)) = ((estart E (SA sb sk)) + i) := by
  lia

-- glaze/binary_reflection: lib/AzNodesLibc2.v (replace)
example
    {atable gtable : Type}
    (A : atable)
    (G : gtable)
    (i : Int)
    (a : Int)
    (img_hi : atable → Int)
    (g_img_hi : gtable → Int)
    (img_lo : atable → Int)
    (g_img_lo : gtable → Int)
    (CEIL_run : Int)
    (g_errno : gtable → Int)
    (SHMAPLO : Int)
    (g_ro_lo : gtable → Int)
    (g_ro_hi : gtable → Int)
    (h1 : (img_hi A) = (g_img_hi G))
    (h2 : (img_lo A) = (g_img_lo G))
    (h3 : (g_img_hi G) ≤ CEIL_run)
    (h4 : ((g_img_lo G) ≤ (g_errno G) ∧ ((g_errno G) + 4) ≤ (g_img_hi G)))
    (h5 : (g_img_hi G) ≤ SHMAPLO)
    (h6 : (0 ≤ (g_img_lo G) ∧ ((g_img_lo G) ≤ (g_ro_lo G) ∧ (g_ro_lo G) ≤ (g_img_hi G))))
    (h7 : ((g_ro_lo G) ≤ (g_ro_hi G) ∧ (g_ro_hi G) ≤ (g_img_hi G))) :
    ((a + 1) + (i - 1)) = (a + i) := by
  lia

-- glaze/binary_reflection: lib/AzSSums.v (replace)
example
    {expr word : Type}
    (nx0 : Nat)
    (ISP : expr)
    (s : word)
    (n : Int)
    (i : Int)
    (bv_unsigned : word → Int)
    (expr_vars_lt : Nat → expr → Bool)
    (h1 : (expr_vars_lt nx0 ISP) = true)
    (h2 : ((bv_unsigned s) + n) ≤ (2 ^ (64 : Nat)))
    (h3 : (0 ≤ i ∧ i < n)) :
    (((Int.toNat i) : Nat) : Int) = i := by
  lia

-- glaze/binary_reflection: lib/BoAllocFRc4R.v (replace)
example
    {list_byte T2 T3 T4 : Type}
    (T : Int)
    (spb : Int)
    (c : Int)
    (e : Int)
    (cnt' : Int)
    (bst : list_byte)
    (bcs : list_byte)
    (Z_to_bv : Int → Int → T2)
    (length : list_byte → Nat)
    (store_ok : T3 → T4 → T2 → Nat → Bool)
    (BSEGS : T3)
    (mem : T4)
    (h1 : (0 ≤ spb ∧ (spb + (2 ^ (37 : Nat))) < (2 ^ (47 : Nat))))
    (h2 : (1 ≤ c ∧ c ≤ 30))
    (h3 : (0 ≤ e ∧ e < (2 ^ (32 : Nat))))
    (h4 : (0 ≤ cnt' ∧ cnt' < 16))
    (h5 : (length bst) = 8)
    (h6 : (length bcs) = 8)
    (h7 : (store_ok BSEGS mem (Z_to_bv 64 T) (Int.toNat 4096)) = true) :
    ((4 * cnt') * (2 ^ (30 : Nat))) = (cnt' * (2 ^ (32 : Nat))) := by
  lia

-- glaze/binary_reflection: lib/BoAllocM8Lh.v (replace)
example
    {word : Type}
    (z : Int)
    (k : Nat)
    (x : word)
    (U : word → Int)
    (AIMGLO : Int)
    (AIMGHI : Int)
    (h1 : 0 ≤ z)
    (h2 : (z + ((k : Nat) : Int)) < (2 ^ (64 : Nat)))
    (h3 : ((z + ((k : Nat) : Int)) ≤ AIMGLO ∨ AIMGHI ≤ z))
    (h4 : (z ≤ (U x) ∧ (U x) < (z + ((k : Nat) : Int)))) :
    (U x) = (z + (((Int.toNat ((U x) - z)) : Nat) : Int)) := by
  lia

-- glaze/binary_reflection: lib/BoAllocMMemB2.v (assert)
example
    {word : Type}
    (m : word)
    (T : Int)
    (n : Int)
    (x : word)
    (U : word → Int)
    (rz : Int → Int)
    (rz_log : Int → Int)
    (c : Int)
    (h1 : (1 ≤ n ∧ n ≤ 64512))
    (h2 : ((U x) < (((U m) + (rz n)) - 16) ∨ (((U m) + (rz n)) + (min n 4096)) ≤ (U x)))
    (h3 : ((rz_log n) ≠ 0 → ((U x) < (U m) ∨ ((U m) + 16) ≤ (U x))))
    (h4 : ((U x) < (T + 2800) ∨ (T + 2824) ≤ (U x)))
    (h5 : ((U x) < ((T + 2912) + (8 * c)) ∨ (((T + 2912) + (8 * c)) + 8) ≤ (U x))) :
    ((U x) < (((U m) + (rz n)) - 8) ∨ (((U m) + (rz n)) + (min n 4096)) ≤ (U x)) := by
  lia

-- glaze/binary_reflection: lib/BoDrvS0SoundA.v (replace)
example
    {T1 T2 T3 : Type}
    (k : T1)
    (a : Int)
    (n : Int)
    (bv_unsigned : T2 → Int)
    (x : T2)
    (kn_readable_x : T1 → T3 → Int → T3 → Bool)
    (ELit : Int → T3)
    (Z_to_bv : Int → Int → T2)
    (h1 : (kn_readable_x k (ELit 0) a (ELit n)) = true)
    (h2 : (1 ≤ n ∧ n < (2 ^ (64 : Nat))))
    (h3 : (bv_unsigned (Z_to_bv 64 n)) = n)
    (h4 : (bv_unsigned (Z_to_bv 64 a)) = a) :
    (bv_unsigned x) = (a + ((bv_unsigned x) - a)) := by
  lia

-- glaze/binary_reflection: lib/DrvS2Glue.v (assert)
example
    {list_byte : Type}
    (data : list_byte)
    (m : Nat)
    (len : Int)
    (cap : Int)
    (L : list_byte → Int)
    (h1 : (Int.toNat ((L data) - (len + 65536))) < m)
    (h2 : 3 ≤ len)
    (h3 : (len + 65536) ≤ (L data))
    (h4 : (len + 65536) < cap) :
    (0 ≤ (len + 65536) ∧ (len + 65536) ≤ (L data)) := by
  lia

-- glaze/binary_reflection: lib/DrvS2Glue.v (replace)
example (cnt : Int) (h1 : 3 ≤ cnt) (h2 : cnt < (2 ^ (64 : Nat))) :
    3 = (min 3 (Int.toNat cnt)) := by
  lia

-- glaze/binary_reflection: lib/GlzStrGrowPlain2.v (replace)
example
    {word T2 T3 : Type}
    (n : Int)
    (s : Int)
    (alloc : Int)
    (cap : Int)
    (spw : word)
    (bv_unsigned : word → Int)
    (store_ok : T2 → T3 → word → Int → Bool)
    (Plain_M_loaded_segments : T2)
    (M : T3)
    (Z_to_bv : Int → Int → word)
    (w0 : word)
    (h1 : (n ≤ (alloc - 1) ∧ ((2 * cap) ≤ (alloc - 1) ∧ (alloc ≤ ((max n (2 * cap)) + 8) ∧ (alloc % 8) = 0))))
    (h2 : (1 ≤ alloc ∧ alloc ≤ (2 ^ (40 : Nat))))
    (h3 : (alloc % 2) = 0)
    (h4 : 80 ≤ (bv_unsigned spw))
    (h5 : (store_ok Plain_M_loaded_segments M (Z_to_bv 64 ((bv_unsigned spw) - 80)) 80) = true)
    (h6 : ((cap + 1) % 2) = 0)
    (h7 : ((bv_unsigned w0) % 2) = 1) :
    n = (s + (n - s)) := by
  lia

-- glaze/binary_reflection: lib/GlzStrGrowPlain2.v (replace)
example
    {word T2 T3 : Type}
    (bv_unsigned : word → Int)
    (spw : word)
    (store_ok : T2 → T3 → word → Int → Bool)
    (Plain_M_loaded_segments : T2)
    (M : T3)
    (Z_to_bv : Int → Int → word)
    (w0 : word)
    (h1 : 80 ≤ (bv_unsigned spw))
    (h2 : (store_ok Plain_M_loaded_segments M (Z_to_bv 64 ((bv_unsigned spw) - 80)) 80) = true)
    (h3 : ((bv_unsigned w0) % 2) = 1) :
    ((bv_unsigned spw) + ((-5) * 16)) = ((bv_unsigned spw) - 80) := by
  lia

-- glaze/binary_reflection: lib/GlzStrGrowUbsan3.v (replace)
example
    (n : Int)
    (s : Int)
    (alloc : Int)
    (h1 : (n ≤ (alloc - 1) ∧ ((2 * 22) ≤ (alloc - 1) ∧ (alloc ≤ ((max n (2 * 22)) + 8) ∧ (alloc % 8) = 0))))
    (h2 : (1 ≤ alloc ∧ alloc ≤ (2 ^ (40 : Nat))))
    (h3 : (alloc % 2) = 0) :
    n = (s + (n - s)) := by
  lia

-- glaze/binary_reflection: lib/MhDefs.v (replace)
example
    (fr : Int)
    (sc : Int)
    (ml : Int)
    (h1 : (0 ≤ fr ∧ fr < 2))
    (h2 : (0 ≤ sc ∧ sc < 64))
    (h3 : 0 ≤ ml) :
    (((fr + (2 * sc)) + (128 * ml)) * 32) = ((32 * fr) + ((64 * sc) + (4096 * ml))) := by
  lia

-- glaze/binary_reflection: lib/MhMallocH2.v (replace)
example
    {list_byte : Type}
    (g : Int)
    (memg : Int)
    (b : Int)
    (W : Int)
    (sbs : list_byte)
    (w_sizeclass : Int → Int)
    (HEAPLO : Int)
    (CEIL : Int)
    (IMG_LO : Int)
    (IMG_HI : Int)
    (bytes_le_to_Z : list_byte → Int)
    (size_class : Int → Int)
    (gl_ok : Nat → Int → Int → Bool)
    (GFUEL : Nat)
    (span0_of : Int → Int → Int)
    (scw : Int)
    (h1 : (HEAPLO ≤ g ∧ ((g + 40) ≤ CEIL ∧ ((g + 40) ≤ IMG_LO ∨ IMG_HI ≤ g))))
    (h2 : (HEAPLO ≤ memg ∧ ((memg + 16) ≤ CEIL ∧ ((memg + 16) ≤ IMG_LO ∨ IMG_HI ≤ memg))))
    (h3 : ((memg + 16) ≤ g ∨ (g + 40) ≤ memg))
    (h4 : (0 ≤ b ∧ b < 256))
    (h5 : (0 ≤ W ∧ W < (2 ^ (64 : Nat))))
    (h6 : (w_sizeclass W) < 48)
    (h7 : (bytes_le_to_Z sbs) = (size_class (w_sizeclass W)))
    (h8 : (gl_ok GFUEL (span0_of b W) (16 * (size_class scw))) = true)
    (h9 : (0 ≤ (span0_of b W) ∧ ((span0_of b W) + ((16 * (size_class scw)) * (((GFUEL : Nat) : Int) + 2))) < (2 ^ (31 : Nat)))) :
    (145812 + (2 * (w_sizeclass W))) = ((145812 + (2 * (w_sizeclass W))) + 0) := by
  lia

-- glaze/binary_reflection: lib/UbMhNtf.v (replace)
example
    {T1 T2 T3 : Type}
    (i : Int)
    (Zpow : Int → Int → Int)
    (Z_lor : T1 → Int → Int)
    (mr_avail : T2 → T1)
    (s_meta : T3 → Int → T2)
    (st : T3)
    (m : Int)
    (mr_freed : T2 → Int)
    (g_lastidx : T3 → Int → Int)
    (g_sc : T3 → Int → Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (g_stride : T3 → Int → Int)
    (h1 : (0 ≤ (Zpow 2 i) ∧ (Zpow 2 i) < (2 ^ (32 : Nat))))
    (h2 : (Zpow 2 i) ≤ (2 ^ (31 : Nat)))
    (h3 : (((Z_lor (mr_avail (s_meta st m)) (mr_freed (s_meta st m))) + (Zpow 2 i)) ≠ ((2 * (Zpow 2 (g_lastidx st m))) - 1) → (g_sc st m) ≠ 63))
    (h4 : i = 0)
    (h5 : (Z_lor (mr_avail (s_meta st m)) (mr_freed (s_meta st m))) = 0)
    (h6 : ((g_sc st m) < 48 → (UNIT * (size_class (g_sc st m))) ≤ (g_stride st m)))
    (h7 : (g_sc st m) ≠ 63)
    (h8 : (g_sc st m) < 48) :
    0 = i := by
  lia

-- glaze/binary_reflection: lib/UbMhTac.v (replace)
example (n : Int) (k : Int) (h1 : 0 ≤ n) (h2 : 0 ≤ k) :
    k = ((k - n) + n) := by
  lia

-- glaze/binary_reflection: lib/UbMuslMemmove.v (replace)
example
    {word list_byte T3 T4 : Type}
    (d : word)
    (s : word)
    (n : Int)
    (bs : list_byte)
    (k : Int)
    (m : Nat)
    (length : list_byte → Nat)
    (store_ok : T3 → T4 → word → Nat → Bool)
    (RSEGS : T3)
    (mem0 : T4)
    (bv_unsigned : word → Int)
    (sub : list_byte → Nat → Nat → list_byte)
    (h1 : (0 ≤ n ∧ n < (2 ^ (63 : Nat))))
    (h2 : (length bs) = (Int.toNat n))
    (h3 : (store_ok RSEGS mem0 d (Int.toNat n)) = true)
    (h4 : ((bv_unsigned s) + n) < (2 ^ (64 : Nat)))
    (h5 : ((bv_unsigned d) + n) < (2 ^ (64 : Nat)))
    (h6 : (((m : Nat) : Int) ≤ k ∧ k ≤ n))
    (h7 : (length (sub bs (Int.toNat (k - ((m : Nat) : Int))) m)) = m) :
    k = ((k - ((m : Nat) : Int)) + ((m : Nat) : Int)) := by
  lia

-- json-c/json_object_fuzzer: lib/Q1Rk.v (replace)
example
    (sb : Int)
    (co : Int)
    (tk : Int)
    (A_SB : Int)
    (Ff : Int)
    (alloc_ceiling : Int)
    (len : Int)
    (h1 : (((tk / 8) + A_SB) + 4) = ((tk / 8) + 2147450884))
    (h2 : (((tk / 8) + A_SB) + 8) = ((tk / 8) + 2147450888))
    (h3 : 0 ≤ Ff)
    (h4 : Ff < alloc_ceiling)
    (h5 : (sb + len) ≤ alloc_ceiling)
    (h6 : (sb + len) ≤ (2 ^ (47 : Nat)))
    (h7 : ((((((sb + co) + 1) / 8) + 2147450880) + 1) ≤ Ff ∨ (Ff + 256) ≤ ((((sb + co) + 1) / 8) + 2147450880))) :
    ((sb + (co + 1)) + 1) = ((sb + co) + 2) := by
  lia

-- json-c/json_object_fuzzer: lib/Q1Rk.v (replace)
example
    (sb : Int)
    (co : Int)
    (tk : Int)
    (A_SB : Int)
    (Ff : Int)
    (alloc_ceiling : Int)
    (len : Int)
    (h1 : (((tk / 8) + A_SB) + 4) = ((tk / 8) + 2147450884))
    (h2 : (((tk / 8) + A_SB) + 8) = ((tk / 8) + 2147450888))
    (h3 : 0 ≤ Ff)
    (h4 : Ff < alloc_ceiling)
    (h5 : (sb + len) ≤ alloc_ceiling)
    (h6 : (sb + len) ≤ (2 ^ (47 : Nat)))
    (h7 : ((((((sb + co) + 1) / 8) + 2147450880) + 1) ≤ Ff ∨ (Ff + 256) ≤ ((((sb + co) + 1) / 8) + 2147450880))) :
    (sb + (co + 1)) = ((sb + co) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/Q20K.v (replace)
example
    {list_byte : Type}
    (buf : Int)
    (ln : Int)
    (len : Int)
    (length : list_byte → Nat)
    (bs : list_byte)
    (h1 : (length bs) = (Int.toNat len))
    (h2 : (((buf + len) - 1) / 8) ≤ (2 ^ (44 : Nat)))
    (h3 : len = (ln + 1))
    (h4 : (0 ≤ ln ∧ ln < 64))
    (h5 : ((buf / 8) ≤ ((buf + ln) / 8) ∧ ((buf + ln) / 8) ≤ ((buf / 8) + 8))) :
    (buf + ln) = ((buf + (ln + 1)) - 1) := by
  lia

-- json-c/json_object_fuzzer: lib/Q20K.v (replace)
example
    {list_byte : Type}
    (buf : Int)
    (i : Int)
    (len : Int)
    (length : list_byte → Nat)
    (bs : list_byte)
    (ln : Int)
    (h1 : (length bs) = (Int.toNat len))
    (h2 : (((buf + len) - 1) / 8) ≤ (2 ^ (44 : Nat)))
    (h3 : len = (ln + 1))
    (h4 : (0 ≤ ln ∧ ln < 64))
    (h5 : ((buf / 8) ≤ ((buf + ln) / 8) ∧ ((buf + ln) / 8) ≤ ((buf / 8) + 8))) :
    (((buf / 8) + 2147450880) + (i + 1)) = ((((buf / 8) + 2147450880) + i) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/Q25t.v (replace)
example
    {T1 T2 : Type}
    (V0 : Int)
    (V10 : Int)
    (TOPP : T1 → Int)
    (bv_unsigned : T2 → T1)
    (sp : T2)
    (h1 : (TOPP (bv_unsigned sp)) = ((32768 * V0) + (4096 * V10)))
    (h2 : (Int.fmod (4096 * V0) (2 ^ (64 : Nat))) = (4096 * V0))
    (h3 : (Int.fmod (512 * V10) (2 ^ (64 : Nat))) = (512 * V10))
    (h4 : (Int.fmod ((((2 ^ (64 : Nat)) - (4096 * V0)) - (512 * V10)) + 17592187092992) (2 ^ (64 : Nat))) = ((17592187092992 - (4096 * V0)) - (512 * V10)))
    (h5 : (((TOPP (bv_unsigned sp)) - 8388608) / 8) = (((4096 * V0) + (512 * V10)) - 1048576)) :
    ((((4096 * V0) + (512 * V10)) - 1048576) * 8) = (((32768 * V0) + (4096 * V10)) - 8388608) := by
  lia

-- json-c/json_object_fuzzer: lib/Q2Do.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (r : Int)
    (length : T1 → Nat)
    (ps : T1)
    (a : Int)
    (junk : T1)
    (size' : Int)
    (store_ok : T2 → T3 → T4 → Int → Bool)
    (asegs : T2)
    (m : T3)
    (wa : Int → T4)
    (h1 : a ≠ r)
    (h2 : (length junk) = (Int.toNat (8 * (size' - (((length ps) : Nat) : Int)))))
    (h3 : (store_ok asegs m (wa (r + ((((length ps) : Nat) : Int) * 8))) 8) = true) :
    ((r + (8 * (((length ps) : Nat) : Int))) + 0) = (r + ((((length ps) : Nat) : Int) * 8)) := by
  lia

-- json-c/json_object_fuzzer: lib/Q2Do.v (replace)
example
    {T1 : Type}
    (ns : Int)
    (length : T1 → Nat)
    (junk : T1)
    (size : Int)
    (ps : T1)
    (h1 : (length junk) = (Int.toNat (8 * (size - (((length ps) : Nat) : Int)))))
    (h2 : (((length junk) : Nat) : Int) = (8 * (size - (((length ps) : Nat) : Int))))
    (h3 : ((((length ps) : Nat) : Int) ≤ ns ∧ (1 ≤ ns ∧ ns ≤ size)))
    (h4 : ns = (max (((length ps) : Nat) : Int) 1)) :
    (8 * ns) = (ns * 8) := by
  lia

-- json-c/json_object_fuzzer: lib/Q30W.v (replace)
example (tbl : Int) (A_SB : Int) (i : Nat) :
    (((tbl / 8) + A_SB) + (((5 * i) : Nat) : Int)) = (((tbl / 8) + (5 * ((i : Nat) : Int))) + A_SB) := by
  lia

-- json-c/json_object_fuzzer: lib/Q3dN.v (replace)
example
    {T1 : Type}
    (SH : Int)
    (W : Int)
    (st : T1)
    (n : Int)
    (AMW : Int → Int)
    (MMAP_THRESHOLD : Int)
    (SHF : T1 → Int)
    (size_overflows : Int → Bool)
    (h1 : (0 ≤ SH ∧ SH ≤ 16))
    (h2 : (1004 < n ∧ n < MMAP_THRESHOLD))
    (h3 : (SHF st) ≤ SH)
    (h4 : (size_overflows n) = false) :
    ((W + (2 ^ (20 : Nat))) + (AMW SH)) = (W + ((AMW SH) + (2 ^ (20 : Nat)))) := by
  lia

-- json-c/json_object_fuzzer: lib/Q3dN.v (replace)
example
    {T1 T2 T3 : Type}
    (SH : Int)
    (W : Int)
    (st : T1)
    (n : Int)
    (g : T2)
    (AMW : Int → Int)
    (MMAP_THRESHOLD : Int)
    (SHF : T1 → Int)
    (m_avail : T3 → Int)
    (MR : T1 → T2 → T3)
    (m_freed : T3 → Int)
    (size_overflows : Int → Bool)
    (st' : T1)
    (h1 : (0 ≤ SH ∧ SH ≤ 16))
    (h2 : (1004 < n ∧ n < MMAP_THRESHOLD))
    (h3 : (SHF st) ≤ SH)
    (h4 : (m_avail (MR st g)) = 0)
    (h5 : (m_freed (MR st g)) = 0)
    (h6 : (size_overflows n) = false)
    (h7 : (SHF st') ≤ SH) :
    ((W + (2 ^ (20 : Nat))) + (AMW SH)) = (W + ((AMW SH) + (2 ^ (20 : Nat)))) := by
  lia

-- json-c/json_object_fuzzer: lib/Q4KR.v (replace)
example (q : Int) (h1 : (q - 8656) ≤ ((q + (-120)) - (((Int.toNat 6000) : Nat) : Int))) :
    (q + (-6120)) = ((q + (-120)) - (((Int.toNat 6000) : Nat) : Int)) := by
  lia

-- json-c/json_object_fuzzer: lib/Q4KR.v (replace)
example
    (q : Int)
    (h1 : (q - 8656) ≤ ((q + (-120)) - (((Int.toNat 6000) : Nat) : Int)))
    (h2 : (q - 8656) ≤ ((q + (-6120)) - ((8 : Nat) : Int))) :
    (q + (-6128)) = ((q + (-6120)) - ((8 : Nat) : Int)) := by
  lia

-- json-c/json_object_fuzzer: lib/Q5m9.v (replace)
example (RDEBRUIJN : Int) (sc : Int) :
    ((RDEBRUIJN + 32) + (sc * 2)) = ((RDEBRUIJN + 32) + (2 * sc)) := by
  lia

-- json-c/json_object_fuzzer: lib/Q63E.v (replace)
example
    {heap_iface_A_A4L word list_frame bud list_option_jshape T6 T7 T8 T9 : Type}
    (HIx : heap_iface_A_A4L)
    (ra : word)
    (FRS : list_frame)
    (B0 : bud)
    (lo : Int)
    (lv : Int)
    (bpos0 : Int)
    (cap0 : Int)
    (w : Int)
    (kids : list_option_jshape)
    (acc : Int)
    (sdepth : T6 → Int)
    (Sobj : list_option_jshape → T6)
    (alloc_ceiling : Int)
    (usp : Int)
    (ser_budgetA : T6 → Int)
    (hiA_top : T7 → heap_iface_A_A4L → Int)
    (A4L : T7)
    (bv_unsigned : word → Int)
    (ser_need : Int → Int → Int → Int)
    (bB : bud → Int)
    (length : list_frame → Nat)
    (key_w : T8 → Int)
    (oe_kn : T9 → T8)
    (e : T9)
    (h1 : 0 ≤ lv)
    (h2 : (lv + (sdepth (Sobj kids))) ≤ 1000)
    (h3 : alloc_ceiling ≤ lo)
    (h4 : lo ≤ (usp - (ser_budgetA (Sobj kids))))
    (h5 : (usp % 16) = 0)
    (h6 : usp ≤ (hiA_top A4L HIx))
    (h7 : ((bv_unsigned ra) % 2) = 0)
    (h8 : (32 ≤ cap0 ∧ cap0 < (2 ^ (30 : Nat))))
    (h9 : (bpos0 + w) < (2 ^ (28 : Nat)))
    (h10 : (ser_need cap0 bpos0 w) ≤ (bB B0))
    (h11 : ((((length FRS) : Nat) : Int) + 1) < 4096)
    (h12 : (acc + (key_w (oe_kn e))) ≤ w)
    (h13 : 14 ≤ (key_w (oe_kn e))) :
    (acc - 1) = ((acc - 2) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/Q6oO.v (replace)
example
    {T1 : Type}
    (r : Int)
    (len : Int)
    (sb : Int)
    (length : T1 → Nat)
    (junk0 : T1)
    (str_objsize : Int → Int)
    (h1 : r ≠ sb)
    (h2 : (length junk0) = (Int.toNat (str_objsize len)))
    (h3 : ((49 + (max len 8)) % 8) ≠ 0)
    (h4 : ((48 + len) / 8) = ((49 + (max len 8)) / 8)) :
    (r + 40) = ((r + 16) + ((24 : Nat) : Int)) := by
  lia

-- json-c/json_object_fuzzer: lib/Q91D.v (replace)
example
    {T1 : Type}
    (w_4 : Int)
    (w_5 : Int)
    (G_11878 : Int)
    (k : Int)
    (is_ecall : T1 → Bool)
    (Z_to_bv : Nat → Int → T1)
    (h1 : (is_ecall (Z_to_bv 32 w_4)) = false)
    (h2 : (is_ecall (Z_to_bv 32 w_5)) = false)
    (h3 : (0 ≤ k ∧ (k + 4) ≤ 68)) :
    (G_11878 + k) = (k + G_11878) := by
  lia

-- json-c/json_object_fuzzer: lib/Q9Mh.v (replace)
example {T1 : Type} (i : Int) (length : T1 → Nat) (ps : T1) :
    (Int.toNat (i - (((length ps) : Nat) : Int))) = ((Int.toNat i) - (length ps)) := by
  lia

-- json-c/json_object_fuzzer: lib/Q9ch.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (bv_unsigned : T1 → Int)
    (sp0 : T1)
    (edenot : T2 → T3 → T1)
    (ENV : T4 → T5 → T2)
    (BL : T4)
    (vals : T5)
    (EVar : Int → T3)
    (h1 : (bv_unsigned (edenot (ENV BL vals) (EVar 114))) < (2 ^ (31 : Nat))) :
    ((bv_unsigned sp0) + (-544)) = ((((bv_unsigned sp0) + (-560)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) := by
  lia

-- json-c/json_object_fuzzer: lib/QArX.v (replace)
example (q : Int) :
    ((q / 8) + 2147450880) = ((((q / 8) + (4 * 0)) + 0) + 2147450880) := by
  lia

-- json-c/json_object_fuzzer: lib/QB6X.v (replace)
example
    {T1 : Type}
    (q : Int)
    (k : Int)
    (bk : Int)
    (length : T1 → Nat)
    (junk0 : T1)
    (str_objsize : Int → Int)
    (h1 : (0 ≤ k ∧ k < (2 ^ (31 : Nat))))
    (h2 : q ≠ bk)
    (h3 : (length junk0) = (Int.toNat (str_objsize k))) :
    (((q + 48) + k) + 1) = (((q + 48) + k) + ((1 : Nat) : Int)) := by
  lia

-- json-c/json_object_fuzzer: lib/QDUx.v (replace)
example
    {T1 : Type}
    (l : T1)
    (i : Int)
    (n : Int)
    (k : Nat)
    (length : T1 → Nat)
    (h1 : 0 ≤ i)
    (h2 : k < (Int.toNat n))
    (h3 : ((Int.toNat i) + k) < (length l)) :
    ((Int.toNat i) + k) = (Int.toNat (i + ((k : Nat) : Int))) := by
  lia

-- json-c/json_object_fuzzer: lib/QEDI.v (replace)
example
    {T1 : Type}
    (SH : Int → Int)
    (f : Int)
    (ae_fs_base : T1 → Int)
    (RE : T1)
    (fs_frame : Int → Int → Int → Int)
    (pos : Int)
    (fs_flag : Int → Int → Int → Int)
    (h1 : (((ae_fs_base RE) + 3182592) ≤ f ∧ (f + 512) ≤ (((ae_fs_base RE) + 3182592) + 1048576)))
    (h2 : (SH (f + 512)) = ((SH f) + 64))
    (h3 : (2147450880 ≤ (SH (ae_fs_base RE)) ∧ (SH ((ae_fs_base RE) + 11571200)) ≤ 17594333495296))
    (h4 : ((SH (ae_fs_base RE)) ≤ (SH f) ∧ (SH (f + 512)) ≤ (SH ((ae_fs_base RE) + 11571200))))
    (h5 : f = (fs_frame (ae_fs_base RE) 3 pos))
    (h6 : (fs_flag (ae_fs_base RE) 3 pos) = (((ae_fs_base RE) + 32768) + pos))
    (h7 : (fs_flag (ae_fs_base RE) 3 0) = ((ae_fs_base RE) + 32768))
    (h8 : (SH ((ae_fs_base RE) + 11571200)) = ((SH (ae_fs_base RE)) + 1446400)) :
    ((SH f) + 56) = (((SH f) + 48) + 8) := by
  lia
