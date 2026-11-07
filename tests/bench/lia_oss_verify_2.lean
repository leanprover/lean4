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

Part 2 of 4. `lia_oss_verify_failing.lean` has the goals that `lia` does not prove yet.
-/

set_option linter.unusedVariables false

-- json-c/json_object_fuzzer: lib/QG64.v (replace)
example
    {list_Segment bv_32 list_byte T4 T5 T6 : Type}
    (SEGS : list_Segment)
    (x : Int)
    (w0 : bv_32)
    (w1 : bv_32)
    (w2 : bv_32)
    (w3 : bv_32)
    (w4 : bv_32)
    (p : Int)
    (pn : Int)
    (s : list_byte)
    (j : Nat)
    (Z_to_bv : Int → Int → T4)
    (is_ecall : bv_32 → Bool)
    (length : list_byte → Nat)
    (store_ok : list_Segment → T5 → T4 → Int → Bool)
    (M0 : T5)
    (b : T6)
    (bv_unsigned : T6 → Int)
    (h1 : (8 ≤ x ∧ (x + 12) < (2 ^ (64 : Nat))))
    (h2 : (is_ecall w0) = false)
    (h3 : (is_ecall w1) = false)
    (h4 : (is_ecall w2) = false)
    (h5 : (is_ecall w3) = false)
    (h6 : (is_ecall w4) = false)
    (h7 : (0 ≤ p ∧ (p + 8) ≤ (2 ^ (64 : Nat))))
    (h8 : (0 ≤ pn ∧ ((pn + (((length s) : Nat) : Int)) + 2) < (2 ^ (64 : Nat))))
    (h9 : ((p + 8) ≤ pn ∨ ((pn + (((length s) : Nat) : Int)) + 1) ≤ p))
    (h10 : (store_ok SEGS M0 (Z_to_bv 64 p) 8) = true)
    (h11 : j = (length s))
    (h12 : j < (length s))
    (h13 : (bv_unsigned b) ≠ 0) :
    (1 + j) = (j + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/QIjw.v (replace)
example (c1 : Int) (c2 : Int) (h1 : c1 ≤ c2) :
    (Int.toNat c1) = (min (Int.toNat c1) (Int.toNat c2)) := by
  lia

-- json-c/json_object_fuzzer: lib/QIjw.v (replace)
example (ptr : Int) (cur : Int) :
    ((ptr + (cur - 1)) - 1) = ((ptr + (cur - 1)) + (-1)) := by
  lia

-- json-c/json_object_fuzzer: lib/QIjw.v (replace)
example (n : Nat) :
    n = ((n + 1) - 1) := by
  lia

-- json-c/json_object_fuzzer: lib/QIsM.v (replace)
example
    {T1 : Type}
    (depth : Nat)
    (stn : Int)
    (length : T1 → Nat)
    (levels : T1)
    (h1 : (0 ≤ stn ∧ stn ≤ 26))
    (h2 : (depth + 1) < (length levels)) :
    (((depth + 1) : Nat) : Int) = (((depth : Nat) : Int) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/QKZH.v (assert)
example (c : Int) (h1 : ((65 ≤ c ∧ c ≤ 70) ∨ (97 ≤ c ∧ c ≤ 102))) :
    (0 ≤ c ∧ c < 256) := by
  lia

-- json-c/json_object_fuzzer: lib/QLbz.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (lenr : Int)
    (len : Int)
    (LENW_C : Int)
    (sb : Int)
    (Z_to_bv : Int → Int → T1)
    (length : T2 → Nat)
    (str0 : T2)
    (slack : T2)
    (h1 : ((0 ≤ lenr ∧ lenr < (2 ^ (64 : Nat))) ∧ (lenr = len ∨ (lenr = LENW_C ∧ 1 ≤ len))))
    (h2 : ((-(((bv_unsigned (Z_to_bv 64 sb)) + (((length str0) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h3 : (((length str0) : Nat) : Int) = (len - 1)) :
    (bv_unsigned sp) = (((bv_unsigned sp) + (-144)) + 144) := by
  lia

-- json-c/json_object_fuzzer: lib/QMmN.v (replace)
example (q : Int) (h1 : (q % 8) = 0) :
    q = (q + (32 * ((0 : Nat) : Int))) := by
  lia

-- json-c/json_object_fuzzer: lib/QOy4.v (replace)
example
    {T1 T2 : Type}
    (q : Int)
    (k : Int)
    (t : Int)
    (p10 : Int)
    (v : Int)
    (znth : T1 → Int → Int)
    (x' : T1)
    (cb : Bool)
    (a : Int)
    (Z_lor : T2 → Int → Int)
    (Z_lxor : Int → Int → T2)
    (h1 : (0 ≤ (Int.fdiv t p10) ∧ (Int.fdiv t p10) < 214748365))
    (h2 : (0 ≤ v ∧ v < (2 ^ (31 : Nat))))
    (h3 : (0 ≤ ((Int.fmod t p10) * (Int.fdiv 1000000000 p10)) ∧ ((Int.fmod t p10) * (Int.fdiv 1000000000 p10)) < 1000000000))
    (h4 : (znth x' k) = v)
    (h5 : cb = (!((k == a) && (v == 0))))
    (h6 : (Z_lor (Z_lxor k a) v) ≠ 0) :
    ((q + (-8312)) + (4 * (k + 1))) = (((q + (-8312)) + (4 * k)) + 4) := by
  lia

-- json-c/json_object_fuzzer: lib/QQLG.v (replace)
example
    {word list_byte : Type}
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (src : list_byte)
    (Q : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : (length src) = (Int.toNat (bv_unsigned a2)))
    (h2 : (0 ≤ (bv_unsigned a1) ∧ (((bv_unsigned a1) + (bv_unsigned a2)) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ (bv_unsigned a0) ∧ (((bv_unsigned a0) + (bv_unsigned a2)) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ (bv_unsigned a2) ∧ (bv_unsigned a2) < (2 ^ (63 : Nat))))))))
    (h3 : (0 ≤ Q ∧ Q ≤ (bv_unsigned a2)))
    (h4 : (bv_unsigned a1) < (bv_unsigned a0)) :
    ((bv_unsigned a0) + (Q - 1)) = ((bv_unsigned a0) + (Q + (-1))) := by
  lia

-- json-c/json_object_fuzzer: lib/QQLG.v (replace)
example
    {word list_byte T3 : Type}
    (w_15 : Int)
    (w_16 : Int)
    (w_17 : Int)
    (w_18 : Int)
    (a0 : word)
    (str : list_byte)
    (slack : list_byte)
    (bv_unsigned : word → Int)
    (j : Int)
    (is_ecall : T3 → Bool)
    (Z_to_bv : Int → Int → T3)
    (length : list_byte → Nat)
    (chunk : list_byte)
    (h1 : (is_ecall (Z_to_bv 32 w_15)) = false)
    (h2 : (is_ecall (Z_to_bv 32 w_16)) = false)
    (h3 : (is_ecall (Z_to_bv 32 w_17)) = false)
    (h4 : (is_ecall (Z_to_bv 32 w_18)) = false)
    (h5 : ((-(((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h6 : (length chunk) = 8) :
    (((bv_unsigned a0) + j) - 1) = ((((bv_unsigned a0) + j) - 9) + 8) := by
  lia

-- json-c/json_object_fuzzer: lib/QQPy.v (replace)
example
    (sp0 : Int)
    (lenr : Int)
    (len : Int)
    (LENW_C : Int)
    (h1 : (0 ≤ sp0 ∧ sp0 < (2 ^ (64 : Nat))))
    (h2 : ((0 ≤ lenr ∧ lenr < (2 ^ (64 : Nat))) ∧ (lenr = len ∨ (lenr = LENW_C ∧ 1 ≤ len)))) :
    (sp0 - 104) = ((sp0 + (-416)) + 312) := by
  lia

-- json-c/json_object_fuzzer: lib/QQRC.v (replace)
example
    {list___Z_Z mstate aptr T4 : Type}
    (RIMG_HI : Int)
    (ref_reserved : list___Z_Z)
    (st : mstate)
    (rid : Nat)
    (b : aptr)
    (nb : Int)
    (nd : Int)
    (G : Int)
    (fst : aptr → Nat)
    (snd : aptr → Int)
    (alloc_ceiling : Int)
    (ranges_free : list___Z_Z → Int → Int → Bool)
    (a : T4)
    (conc : mstate → T4 → Int)
    (q : T4)
    (AREA_HDR : Int)
    (META_SIZE : Int)
    (k : Int)
    (h1 : (fst b) = rid)
    (h2 : (snd b) = 0)
    (h3 : 0 < nb)
    (h4 : (nb % 4096) = 0)
    (h5 : (nd % 4096) = 0)
    (h6 : 16 ≤ nd)
    (h7 : (nb + nd) ≤ alloc_ceiling)
    (h8 : (ranges_free ref_reserved nb nd) = true)
    (h9 : (conc st q) = (((conc st a) + AREA_HDR) + (META_SIZE * k)))
    (h10 : (conc st q) = G)
    (h11 : ((G + 40) ≤ 65536 ∨ RIMG_HI ≤ G)) :
    (G + 24) = (((G + 8) + 8) + 8) := by
  lia

-- json-c/json_object_fuzzer: lib/QQRC.v (replace)
example
    {list___Z_Z region aptr : Type}
    (ref_reserved : list___Z_Z)
    (rid : Nat)
    (r : region)
    (b : aptr)
    (nb : Int)
    (nd : Int)
    (r_base : region → Int)
    (o : Int)
    (i : Int)
    (fst : aptr → Nat)
    (snd : aptr → Int)
    (alloc_ceiling : Int)
    (ranges_free : list___Z_Z → Int → Int → Bool)
    (h1 : (fst b) = rid)
    (h2 : (snd b) = 0)
    (h3 : 0 < nb)
    (h4 : (nb % 4096) = 0)
    (h5 : (nd % 4096) = 0)
    (h6 : 16 ≤ nd)
    (h7 : (nb + nd) ≤ alloc_ceiling)
    (h8 : (ranges_free ref_reserved nb nd) = true) :
    ((r_base r) + (o + i)) = (((r_base r) + o) + i) := by
  lia

-- json-c/json_object_fuzzer: lib/QTq4.v (replace)
example
    {list_byte byte T3 : Type}
    (buf : Int)
    (txt : list_byte)
    (j : Int)
    (b : byte)
    (length : list_byte → Nat)
    (len : Int)
    (isdig : T3 → Bool)
    (bv_unsigned : byte → T3)
    (h1 : 0 ≤ buf)
    (h2 : ((buf + (((length txt) : Nat) : Int)) + 1) < (2 ^ (63 : Nat)))
    (h3 : (0 ≤ j ∧ j ≤ len))
    (h4 : (isdig (bv_unsigned b)) = false)
    (h5 : j < len) :
    ((buf + j) + 1) = (buf + (j + 1)) := by
  lia

-- json-c/json_object_fuzzer: lib/QTq4.v (replace)
example
    {list_byte byte T3 : Type}
    (buf : Int)
    (txt : list_byte)
    (j : Int)
    (b : byte)
    (length : list_byte → Nat)
    (len : Int)
    (isdig : T3 → Bool)
    (bv_unsigned : byte → T3)
    (h1 : 0 ≤ buf)
    (h2 : ((buf + (((length txt) : Nat) : Int)) + 1) < (2 ^ (63 : Nat)))
    (h3 : (0 ≤ j ∧ j ≤ len))
    (h4 : (isdig (bv_unsigned b)) = false)
    (h5 : j < len) :
    ((buf + (j + 1)) - 1) = (buf + j) := by
  lia

-- json-c/json_object_fuzzer: lib/QTq4.v (replace)
example
    {list_byte : Type}
    (buf : Int)
    (txt : list_byte)
    (n0 : Int)
    (length : list_byte → Nat)
    (len : Int)
    (h1 : 0 ≤ buf)
    (h2 : ((buf + (((length txt) : Nat) : Int)) + 1) < (2 ^ (63 : Nat)))
    (h3 : 0 ≤ len)
    (h4 : n0 < len) :
    (buf + (n0 + 1)) = ((buf + n0) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/QVbl.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (a0 : T1)
    (i : Int)
    (length : T2 → Nat)
    (ls : T2)
    (rs : T2)
    (h1 : (Int.toNat i) < (length ls))
    (h2 : (Int.toNat i) < (length rs)) :
    ((bv_unsigned a0) + (i + 1)) = (((bv_unsigned a0) + i) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/QWQx.v (replace)
example
    {heap_iface_A_A4L word T3 : Type}
    (HIx : heap_iface_A_A4L)
    (sp : word)
    (lo : Int)
    (nz : Nat)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (hiA_top : T3 → heap_iface_A_A4L → Int)
    (A4L : T3)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : lo ≤ (((bv_unsigned sp) + (-112)) - 4352))
    (h3 : ((bv_unsigned sp) % 16) = 0)
    (h4 : (bv_unsigned sp) ≤ (hiA_top A4L HIx)) :
    (((nz + 1) : Nat) : Int) = (((nz : Nat) : Int) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/QWrz.v (replace)
example
    {T1 : Type}
    (sb : Int)
    (co : Int)
    (Ff : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : T1 → Int)
    (cb : T1)
    (len : Int)
    (h1 : 0 ≤ Ff)
    (h2 : Ff < alloc_ceiling)
    (h3 : 0 < sb)
    (h4 : (bv_unsigned cb) ≠ 0)
    (h5 : (sb + len) ≤ alloc_ceiling)
    (h6 : (sb + len) ≤ (2 ^ (47 : Nat)))
    (h7 : ((((((sb + co) + 1) / 8) + 2147450880) + 1) ≤ Ff ∨ (Ff + 256) ≤ ((((sb + co) + 1) / 8) + 2147450880))) :
    ((sb + co) + 1) = (sb + (co + 1)) := by
  lia

-- json-c/json_object_fuzzer: lib/QWrz.v (replace)
example
    {T1 : Type}
    (sb : Int)
    (co : Int)
    (Ff : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : T1 → Int)
    (cb : T1)
    (len : Int)
    (h1 : 0 ≤ Ff)
    (h2 : Ff < alloc_ceiling)
    (h3 : (bv_unsigned cb) ≠ 0)
    (h4 : (sb + len) ≤ alloc_ceiling)
    (h5 : (sb + len) ≤ (2 ^ (47 : Nat)))
    (h6 : ((((((sb + co) + 1) / 8) + 2147450880) + 1) ≤ Ff ∨ (Ff + 256) ≤ ((((sb + co) + 1) / 8) + 2147450880))) :
    (sb + (co + 1)) = ((sb + co) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/QYyZ.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (A : Int)
    (c : Int)
    (lo : Int)
    (buf : list_byte)
    (cw : word)
    (L : Int)
    (i : Nat)
    (band_lo : Int)
    (bv_unsigned : word → Int)
    (MEMCHR_ICPT_STACK : Int)
    (length : list_byte → Nat)
    (h1 : band_lo ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - MEMCHR_ICPT_STACK))
    (h3 : 0 < A)
    (h4 : ((bv_unsigned cw) % 256) = c)
    (h5 : ((A + (((length buf) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ A))
    (h6 : L = (((i : Nat) : Int) + 1)) :
    L = (((A + ((i : Nat) : Int)) + (-A)) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/QYyZ.v (replace)
example
    {T1 : Type}
    (ae_fs_base : T1 → Int)
    (RE : T1)
    (f : Int)
    (SH : Int → Int)
    (fs_frame : Int → Int → Int → Int)
    (pos : Int)
    (fs_flag : Int → Int → Int → Int)
    (h1 : (((ae_fs_base RE) + 1085440) ≤ f ∧ (f + 128) ≤ (((ae_fs_base RE) + 1085440) + 1048576)))
    (h2 : (SH (f + 128)) = ((SH f) + 16))
    (h3 : (2147450880 ≤ (SH (ae_fs_base RE)) ∧ (SH ((ae_fs_base RE) + 11571200)) ≤ 17594333495296))
    (h4 : ((SH (ae_fs_base RE)) ≤ (SH f) ∧ (SH (f + 128)) ≤ (SH ((ae_fs_base RE) + 11571200))))
    (h5 : f = (fs_frame (ae_fs_base RE) 1 pos))
    (h6 : (fs_flag (ae_fs_base RE) 1 pos) = (((ae_fs_base RE) + 20480) + pos))
    (h7 : (fs_flag (ae_fs_base RE) 1 0) = ((ae_fs_base RE) + 20480))
    (h8 : (SH ((ae_fs_base RE) + 11571200)) = ((SH (ae_fs_base RE)) + 1446400)) :
    ((ae_fs_base RE) + (1446400 * 8)) = ((ae_fs_base RE) + 11571200) := by
  lia

-- json-c/json_object_fuzzer: lib/QZxv.v (replace)
example (RATP : Int) (sc : Int) :
    ((RATP + 131960) + (8 * sc)) = ((RATP + 131960) + (sc * 8)) := by
  lia

-- json-c/json_object_fuzzer: lib/QcYs.v (replace)
example
    (A : Int)
    (n' : Int)
    (SH : Int → Int)
    (AB : Int)
    (up : Int)
    (ngran : Int → Int)
    (ssz : Int)
    (sz : Int)
    (h1 : (0 ≤ (n' / 8) ∧ ((0 ≤ (n' % 8) ∧ (n' % 8) < 8) ∧ n' = ((8 * (n' / 8)) + (n' % 8)))))
    (h2 : ((8 * (n' / 8)) / 8) = (n' / 8))
    (h3 : (SH AB) = ((AB / 8) + 2147450880))
    (h4 : (SH A) = ((SH AB) + 256))
    (h5 : (SH up) = ((SH A) + (ngran n')))
    (h6 : (SH (AB + ssz)) = ((SH up) + 256))
    (h7 : ((((AB + sz) - up) / 8) = (256 + ((sz - ssz) / 8)) ∧ 0 ≤ ((sz - ssz) / 8)))
    (h8 : 6574080 ≤ (SH AB)) :
    A = ((A + (-16)) + 16) := by
  lia

-- json-c/json_object_fuzzer: lib/QdWK.v (replace)
example
    {aentry rlay list_byte T4 T5 T6 T7 T8 : Type}
    (RE : aentry)
    (X : rlay)
    (src : Int)
    (lo : Int)
    (bp : Int)
    (str : list_byte)
    (stl : list_byte)
    (sb : list_byte)
    (u4 : Int)
    (AB : Int)
    (rz_size : Int → Int)
    (length : list_byte → Nat)
    (rl_T : rlay → Int)
    (KHI : Int)
    (kLowEnd : Int)
    (band_lo : Int)
    (STRDUP_STACK : Int)
    (DEPOT_CAP : Int)
    (from_primary : Int → Bool)
    (SH : Int → Int)
    (fa_beg : T4 → T5 → Int)
    (ae_L : aentry → T4)
    (c : T5)
    (reg_beg : T4 → T5 → Int)
    (c_alloc_user : T6 → Int)
    (cls : T7 → T5 → T6)
    (a : T7)
    (z : Int)
    (class_size : T5 → Int)
    (slot_beg : aentry → T5 → T8 → Int)
    (i : T8)
    (h1 : (src + (((length sb) : Nat) : Int)) ≤ lo)
    (h2 : 0 ≤ src)
    (h3 : ((src + (((length sb) : Nat) : Int)) ≤ ((rl_T X) + 3168) ∨ ((rl_T X) + 3169) ≤ src))
    (h4 : (KHI ≤ src ∨ (0 < src ∧ (src + ((((length str) : Nat) : Int) + 1)) ≤ kLowEnd)))
    (h5 : ((((length str) : Nat) : Int) + 1) ≤ (2 ^ (26 : Nat)))
    (h6 : (src + ((((length str) : Nat) : Int) + 1)) ≤ band_lo)
    (h7 : band_lo ≤ lo)
    (h8 : lo ≤ (bp - STRDUP_STACK))
    (h9 : (0 ≤ bp ∧ bp < (2 ^ (64 : Nat))))
    (h10 : (u4 + 1) ≤ DEPOT_CAP)
    (h11 : (from_primary ((((length str) : Nat) : Int) + 1)) = true)
    (h12 : 0 ≤ ((((length str) : Nat) : Int) + 1))
    (h13 : (2201439137792 ≤ (SH (fa_beg (ae_L RE) c)) ∧ (((SH (fa_beg (ae_L RE) c)) + 67108864) ≤ (SH band_lo) ∧ (SH band_lo) ≤ 17594332971008)))
    (h14 : (2201439137792 ≤ (SH (reg_beg (ae_L RE) c)) ∧ (((SH (reg_beg (ae_L RE) c)) + 469762048) ≤ (SH band_lo) ∧ (SH band_lo) ≤ 17594332971008)))
    (h15 : ((SH (reg_beg (ae_L RE) c)) ≤ (SH ((reg_beg (ae_L RE) c) + (c_alloc_user (cls a c)))) ∧ (SH ((reg_beg (ae_L RE) c) + (c_alloc_user (cls a c)))) ≤ ((SH (reg_beg (ae_L RE) c)) + 469762048)))
    (h16 : z ≠ ((rl_T X) + 3168))
    (h17 : ((((length str) : Nat) : Int) + 1) ≤ ((class_size c) - (rz_size ((((length str) : Nat) : Int) + 1))))
    (h18 : ((SH (reg_beg (ae_L RE) c)) ≤ (SH (slot_beg RE c i)) ∧ ((SH (slot_beg RE c i)) + ((class_size c) / 8)) ≤ ((SH (reg_beg (ae_L RE) c)) + 469762048)))
    (h19 : ((src + ((((length str) : Nat) : Int) + 1)) ≤ (AB + (rz_size ((((length str) : Nat) : Int) + 1))) ∨ ((AB + (rz_size ((((length str) : Nat) : Int) + 1))) + ((((length str) : Nat) : Int) + 1)) ≤ src))
    (h20 : (((length sb) : Nat) : Int) = (((((length str) : Nat) : Int) + 1) + (((length stl) : Nat) : Int))) :
    ((AB + (rz_size ((((length str) : Nat) : Int) + 1))) + (((Int.toNat ((((length str) : Nat) : Int) + 1)) : Nat) : Int)) = ((AB + (rz_size ((((length str) : Nat) : Int) + 1))) + ((((length str) : Nat) : Int) + 1)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qdkw.v (replace)
example
    {T1 : Type}
    (n : Int)
    (n0 : Int)
    (length : T1 → Nat)
    (old : T1)
    (h1 : (length old) ≤ (Int.toNat n0)) :
    (min (Int.toNat (min n n0)) (length old)) = (Int.toNat (min n (((length old) : Nat) : Int))) := by
  lia

-- json-c/json_object_fuzzer: lib/Qeia.v (replace)
example
    {T1 : Type}
    (length : T1 → Nat)
    (uds : T1)
    (q : Int)
    (p : Int)
    (rd : Int)
    (h1 : q ≠ p)
    (h2 : ((rd + ((((length uds) : Nat) : Int) + 1)) ≤ q ∨ (q + 48) ≤ rd))
    (h3 : rd ≠ q) :
    ((((length uds) : Nat) : Int) + 1) = ((((Int.toNat ((((length uds) : Nat) : Int) + 1)) + 0) : Nat) : Int) := by
  lia

-- json-c/json_object_fuzzer: lib/QfHY.v (replace)
example (acc : Int) (wi : Int) :
    (acc + wi) = ((acc + (2 + wi)) - 2) := by
  lia

-- json-c/json_object_fuzzer: lib/QfJh.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    ((((bv_unsigned sp) + (-192)) + 80) + 8) = (((((bv_unsigned sp) + (-192)) + 80) + 1) + 7) := by
  lia

-- json-c/json_object_fuzzer: lib/Qi1S.v (replace)
example
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (i : Int)
    (n : Int)
    (j : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : (q + 16) ≤ 140737488355328)
    (h4 : ((945072 ≤ Fp ∧ (Fp + 232) ≤ 6565536) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((6566104 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : 0 ≤ BS)
    (h10 : j = n)
    (h11 : (j + 1) = n) :
    ((A + i) + n) = (((A + i) + j) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/Qi1S.v (replace)
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
    (i : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (znth : list_Z → Int → Int)
    (k1 : Int)
    (k2' : Int)
    (k2 : Int)
    (n3 : Nat)
    (k' : Int)
    (is_digit : Int → Bool)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : (q + 16) ≤ 140737488355328)
    (h4 : ((945072 ≤ Fp ∧ (Fp + 232) ≤ 6565536) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((6566104 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : 0 ≤ BS)
    (h10 : (i + 1) < (zlength fmt))
    (h11 : k2' = k2)
    (h12 : 0 ≤ ((k2 + 1) + ((n3 : Nat) : Int)))
    (h13 : ((k2 + 1) + ((n3 : Nat) : Int)) < (zlength fmt))
    (h14 : (32 ≤ (znth fmt (i + 1)) ∧ (znth fmt (i + 1)) < 64))
    (h15 : k' = k1)
    (h16 : (is_digit (znth fmt (i + 1))) = true)
    (h17 : (i + 2) < (zlength fmt)) :
    (i + 2) = ((i + 1) + 1) := by
  lia

-- json-c/json_object_fuzzer: lib/Qi1S.v (replace)
example
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : (q + 16) ≤ 140737488355328)
    (h4 : ((945072 ≤ Fp ∧ (Fp + 232) ≤ 6565536) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((6566104 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : 0 ≤ BS) :
    (q + (-368)) = (((q + (-544)) + ((152 : Nat) : Int)) + ((24 : Nat) : Int)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qi1S.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (j : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (x : Int)
    (dec_digits : Int → list_Z)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : (q + 16) ≤ 140737488355328)
    (h4 : ((954304 ≤ Fp ∧ (Fp + 232) ≤ 6575456) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((6576024 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : 0 ≤ BS)
    (h10 : (x / 10) < 1844674407370955162)
    (h11 : 2 ≤ (zlength (dec_digits x))) :
    ((q + (-392)) + (j - 1)) = (((q + (-392)) + j) + (-1)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qi8L.v (replace)
example
    {T1 T2 : Type}
    (cur : Int)
    (Z_land : Int → T1 → Int)
    (bv_unsigned : T2 → T1)
    (Z_to_bv : Int → Int → T2)
    (h1 : (Z_land 4095 (bv_unsigned (Z_to_bv 64 (0 + (-cur))))) = 0) :
    cur = (0 + cur) := by
  lia

-- json-c/json_object_fuzzer: lib/QiVi.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    ((bv_unsigned sp) - (16 * 5)) = ((bv_unsigned sp) + (-80)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qiiq.v (replace)
example
    (tbl : Int)
    (next_ix : Int → Int → Int)
    (size : Int)
    (n : Int)
    (f : Int)
    (Z_lxor : Int → Int → Int)
    (h1 : f = n)
    (h2 : n ≠ f)
    (h3 : (Z_lxor size (n + 1)) ≠ 0)
    (h4 : (0 ≤ (next_ix size n) ∧ (next_ix size n) < size)) :
    (tbl + (40 * (next_ix size n))) = (tbl + ((next_ix size n) * 40)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qiiq.v (replace)
example
    (tbl : Int)
    (next_ix : Int → Int → Int)
    (size : Int)
    (n : Int)
    (f : Int)
    (Z_lxor : Int → Int → Int)
    (h1 : f = n)
    (h2 : n ≠ f)
    (h3 : (Z_lxor size (n + 1)) ≠ 0)
    (h4 : (0 ≤ (next_ix size n) ∧ (next_ix size n) < size)) :
    (tbl + ((next_ix size n) * 40)) = (tbl + (40 * (next_ix size n))) := by
  lia

-- json-c/json_object_fuzzer: lib/Qiiq.v (replace)
example (cap : Int) :
    ((Int.toNat cap) - 8) = (Int.toNat (cap - 8)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qiiq.v (replace)
example (p : Int) (a : Int) (pd : Int) (h1 : p ≠ a) (h2 : p ≠ pd) (h3 : pd ≠ a) :
    (p + 48) = ((p + 40) + 8) := by
  lia

-- json-c/json_object_fuzzer: lib/QjDJ.v (replace)
example (szrz : Int) (beg : Int) :
    (szrz / 8) = (((2147450880 + (((beg / 8) + (szrz / 8)) - 1)) + 1) - (2147450880 + (beg / 8))) := by
  lia

-- json-c/json_object_fuzzer: lib/QnCn.v (replace)
example
    {T1 : Type}
    (length : T1 → Nat)
    (ps : T1)
    (junk : T1)
    (size : Int)
    (h1 : (length junk) = (Int.toNat (8 * (size - (((length ps) : Nat) : Int))))) :
    (8 * (((length ps) : Nat) : Int)) = (((8 * (length ps)) : Nat) : Int) := by
  lia

-- json-c/json_object_fuzzer: lib/QnRU.v (replace)
example
    {T1 T2 : Type}
    (rl_dn : T1 → Int)
    (X : T1)
    (n : Int)
    (length : T2 → Nat)
    (ks : T2)
    (sz : Int)
    (dn : Int)
    (h1 : (length ks) = (Int.toNat sz))
    (h2 : sz = (((length ks) : Nat) : Int))
    (h3 : (1 ≤ sz ∧ sz ≤ 30))
    (h4 : n = dn)
    (h5 : (n + 1) ≤ 32000) :
    (((rl_dn X) + (16 * (n + 1))) + ((16 : Nat) : Int)) = ((rl_dn X) + (16 * ((n + 1) + 1))) := by
  lia

-- json-c/json_object_fuzzer: lib/QnaW.v (replace)
example {rlay : Type} (X : rlay) (rl_T : rlay → Int) :
    ((rl_T X) + 2128) = (((rl_T X) + 208) + (80 * 24)) := by
  lia

-- json-c/json_object_fuzzer: lib/QpNt.v (replace)
example (i : Int) (rem1 : Int) (rem : Int) (h1 : (0 ≤ rem1 ∧ rem1 ≤ rem)) :
    ((8 * (i + 1)) + (-8)) = (8 * i) := by
  lia

-- json-c/json_object_fuzzer: lib/QpNt.v (replace)
example
    {T1 : Type}
    (b : Int)
    (len : Int)
    (xa : T1)
    (bv_unsigned : T1 → Int)
    (k : Nat)
    (h1 : (bv_unsigned xa) = 0)
    (h2 : ((k : Nat) : Int) = (len + 1))
    (h3 : ((b / 8) ≤ ((b + len) / 8) ∧ ((b + len) / 8) ≤ ((b / 8) + 8))) :
    (b + len) = (len + b) := by
  lia

-- json-c/json_object_fuzzer: lib/QsTj.v (assert)
example (sc : Int) (h1 : sc < 9) :
    (Int.toNat sc) < 9 := by
  lia

-- json-c/json_object_fuzzer: lib/QscU.v (replace)
example
    {QZsi_heap_iface_A_A4L list_byte T3 T4 : Type}
    (H6 : QZsi_heap_iface_A_A4L)
    (USP : Int)
    (LO : Int)
    (data : list_byte)
    (len : Int)
    (cap : Int)
    (cnt : Int)
    (nb : Nat)
    (A4L : T3)
    (hi5_of_v6 : T3 → QZsi_heap_iface_A_A4L → T4)
    (alloc_ceiling : Int)
    (hiA_top : T3 → T4 → Int)
    (hiA_bot : T3 → T4 → Int)
    (length : list_byte → Nat)
    (bs : list_byte)
    (buf : Int)
    (h1 : ((USP % 16) = 0 ∧ ((2 ^ (33 : Nat)) ≤ USP ∧ USP ≤ (2 ^ (47 : Nat)))))
    (h2 : (alloc_ceiling ≤ LO ∧ (LO + (2 ^ (22 : Nat))) ≤ (USP - 48)))
    (h3 : (USP ≤ ((hiA_top A4L (hi5_of_v6 A4L H6)) + 160) ∧ (hiA_bot A4L (hi5_of_v6 A4L H6)) ≤ LO))
    (h4 : (((length data) : Nat) : Int) < (2 ^ (40 : Nat)))
    (h5 : len < cap)
    (h6 : (1 ≤ cnt ∧ cnt ≤ 65536))
    (h7 : cnt ≤ (cap - len))
    (h8 : (length bs) = (min (Int.toNat cnt) ((length data) - (Int.toNat len))))
    (h9 : (((nb : Nat) : Int) ≤ cnt ∧ ((len + ((nb : Nat) : Int)) ≤ (((length data) : Nat) : Int) ∧ (nb = 0 ∨ (((nb : Nat) : Int) = cnt ∨ (len + ((nb : Nat) : Int)) = (((length data) : Nat) : Int))))))
    (h10 : len = (((length data) : Nat) : Int))
    (h11 : 6574080 ≤ buf) :
    (len + ((nb : Nat) : Int)) = (((nb : Nat) : Int) + len) := by
  lia

-- json-c/json_object_fuzzer: lib/QscU.v (replace)
example
    {QZsi_heap_iface_A_A4L list_byte T3 T4 : Type}
    (H6 : QZsi_heap_iface_A_A4L)
    (USP : Int)
    (LO : Int)
    (data : list_byte)
    (cap : Int)
    (A4L : T3)
    (hi5_of_v6 : T3 → QZsi_heap_iface_A_A4L → T4)
    (alloc_ceiling : Int)
    (hiA_top : T3 → T4 → Int)
    (hiA_bot : T3 → T4 → Int)
    (length : list_byte → Nat)
    (acostA : Int → Int)
    (h1 : ((USP % 16) = 0 ∧ ((2 ^ (33 : Nat)) ≤ USP ∧ USP ≤ (2 ^ (47 : Nat)))))
    (h2 : (alloc_ceiling ≤ LO ∧ (LO + (2 ^ (22 : Nat))) ≤ (USP - 48)))
    (h3 : (USP ≤ ((hiA_top A4L (hi5_of_v6 A4L H6)) + 160) ∧ (hiA_bot A4L (hi5_of_v6 A4L H6)) ≤ LO))
    (h4 : (((length data) : Nat) : Int) < (2 ^ (40 : Nat)))
    (h5 : cap = (2 ^ (26 : Nat)))
    (h6 : cap ≤ (2 ^ (25 : Nat)))
    (h7 : (acostA (cap * 2)) = ((3 * (cap * 2)) + 45101)) :
    (Int.toNat cap) = ((Int.toNat (cap * 2)) - (Int.toNat cap)) := by
  lia

-- json-c/json_object_fuzzer: lib/QscU.v (replace)
example
    {QZsi_heap_iface_A_A4L list_byte T3 T4 : Type}
    (H6 : QZsi_heap_iface_A_A4L)
    (USP : Int)
    (LO : Int)
    (data : list_byte)
    (len : Int)
    (cap : Int)
    (cnt : Int)
    (buf : Int)
    (nb : Nat)
    (A4L : T3)
    (hi5_of_v6 : T3 → QZsi_heap_iface_A_A4L → T4)
    (alloc_ceiling : Int)
    (hiA_top : T3 → T4 → Int)
    (hiA_bot : T3 → T4 → Int)
    (length : list_byte → Nat)
    (bs : list_byte)
    (h1 : ((USP % 16) = 0 ∧ ((2 ^ (33 : Nat)) ≤ USP ∧ USP ≤ (2 ^ (47 : Nat)))))
    (h2 : (alloc_ceiling ≤ LO ∧ (LO + (2 ^ (22 : Nat))) ≤ (USP - 48)))
    (h3 : (USP ≤ ((hiA_top A4L (hi5_of_v6 A4L H6)) + 160) ∧ (hiA_bot A4L (hi5_of_v6 A4L H6)) ≤ LO))
    (h4 : (((length data) : Nat) : Int) < (2 ^ (40 : Nat)))
    (h5 : len < cap)
    (h6 : (1 ≤ cnt ∧ cnt ≤ 65536))
    (h7 : cnt ≤ (cap - len))
    (h8 : (length bs) = (min (Int.toNat cnt) ((length data) - (Int.toNat len))))
    (h9 : (((nb : Nat) : Int) ≤ cnt ∧ ((len + ((nb : Nat) : Int)) ≤ (((length data) : Nat) : Int) ∧ (nb = 0 ∨ (((nb : Nat) : Int) = cnt ∨ (len + ((nb : Nat) : Int)) = (((length data) : Nat) : Int))))))
    (h10 : len = (((length data) : Nat) : Int))
    (h11 : 6582272 ≤ buf) :
    ((buf + len) + ((nb : Nat) : Int)) = (buf + (((Int.toNat (len + ((nb : Nat) : Int))) : Nat) : Int)) := by
  lia

-- json-c/json_object_fuzzer: lib/QscU.v (replace)
example
    {QZsi_heap_iface_A_A4L list_byte T3 T4 : Type}
    (H6 : QZsi_heap_iface_A_A4L)
    (USP : Int)
    (LO : Int)
    (data : list_byte)
    (len : Int)
    (cap : Int)
    (cnt : Int)
    (nb : Nat)
    (A4L : T3)
    (hi5_of_v6 : T3 → QZsi_heap_iface_A_A4L → T4)
    (alloc_ceiling : Int)
    (hiA_top : T3 → T4 → Int)
    (hiA_bot : T3 → T4 → Int)
    (length : list_byte → Nat)
    (bs : list_byte)
    (buf : Int)
    (h1 : ((USP % 16) = 0 ∧ ((2 ^ (33 : Nat)) ≤ USP ∧ USP ≤ (2 ^ (47 : Nat)))))
    (h2 : (alloc_ceiling ≤ LO ∧ (LO + (2 ^ (22 : Nat))) ≤ (USP - 48)))
    (h3 : (USP ≤ ((hiA_top A4L (hi5_of_v6 A4L H6)) + 160) ∧ (hiA_bot A4L (hi5_of_v6 A4L H6)) ≤ LO))
    (h4 : (((length data) : Nat) : Int) < (2 ^ (40 : Nat)))
    (h5 : len < cap)
    (h6 : (1 ≤ cnt ∧ cnt ≤ 65536))
    (h7 : cnt ≤ (cap - len))
    (h8 : (length bs) = (min (Int.toNat cnt) ((length data) - (Int.toNat len))))
    (h9 : (((nb : Nat) : Int) ≤ cnt ∧ ((len + ((nb : Nat) : Int)) ≤ (((length data) : Nat) : Int) ∧ (nb = 0 ∨ (((nb : Nat) : Int) = cnt ∨ (len + ((nb : Nat) : Int)) = (((length data) : Nat) : Int))))))
    (h10 : len = (((length data) : Nat) : Int))
    (h11 : 6582272 ≤ buf) :
    ((Int.toNat (cap - len)) - nb) = (Int.toNat (cap - (len + ((nb : Nat) : Int)))) := by
  lia

-- json-c/json_object_fuzzer: lib/Qt1H.v (replace)
example
    {heap_iface_A_A4L word list_byte T4 : Type}
    (HIx : heap_iface_A_A4L)
    (sp0 : word)
    (sp1 : Int)
    (lo : Int)
    (Fr : Int)
    (data0 : Int)
    (size : Int)
    (payload : list_byte)
    (ptr : Int)
    (rem : Int)
    (i : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (hiA_top : T4 → heap_iface_A_A4L → Int)
    (A4L : T4)
    (hiA_bot : T4 → heap_iface_A_A4L → Int)
    (length : list_byte → Nat)
    (A_SB : Int)
    (A_HMB : Int)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : lo ≤ (sp1 - ((2 ^ (20 : Nat)) - 144)))
    (h3 : (sp1 % 32) = 0)
    (h4 : (sp1 + 32) ≤ (bv_unsigned sp0))
    (h5 : ((bv_unsigned sp0) + 32) ≤ (hiA_top A4L HIx))
    (h6 : (hiA_bot A4L HIx) ≤ lo)
    (h7 : (((length payload) : Nat) : Int) = size)
    (h8 : (0 ≤ size ∧ size < (2 ^ (26 : Nat))))
    (h9 : 0 < data0)
    (h10 : (data0 + size) ≤ alloc_ceiling)
    (h11 : (Fr % 256) = 0)
    (h12 : 6574080 ≤ Fr)
    (h13 : (Fr + 256) ≤ alloc_ceiling)
    (h14 : (((Fr + 256) + 8) ≤ A_SB ∨ A_HMB ≤ Fr)) :
    (ptr + ((rem - i) + (-1))) = (ptr + ((rem - i) - 1)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qt1H.v (replace)
example
    {heap_iface_A_A4L word list_byte T4 : Type}
    (HIx : heap_iface_A_A4L)
    (sp0 : word)
    (sp1 : Int)
    (lo : Int)
    (Fr : Int)
    (data0 : Int)
    (size : Int)
    (payload : list_byte)
    (rem : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (hiA_top : T4 → heap_iface_A_A4L → Int)
    (A4L : T4)
    (hiA_bot : T4 → heap_iface_A_A4L → Int)
    (length : list_byte → Nat)
    (A_SB : Int)
    (A_HMB : Int)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : lo ≤ (sp1 - ((2 ^ (20 : Nat)) - 144)))
    (h3 : (sp1 % 32) = 0)
    (h4 : (sp1 + 32) ≤ (bv_unsigned sp0))
    (h5 : ((bv_unsigned sp0) + 32) ≤ (hiA_top A4L HIx))
    (h6 : (hiA_bot A4L HIx) ≤ lo)
    (h7 : (((length payload) : Nat) : Int) = size)
    (h8 : (0 ≤ size ∧ size < (2 ^ (26 : Nat))))
    (h9 : 0 < data0)
    (h10 : (data0 + size) ≤ alloc_ceiling)
    (h11 : (Fr % 256) = 0)
    (h12 : 6574080 ≤ Fr)
    (h13 : (Fr + 256) ≤ alloc_ceiling)
    (h14 : (((Fr + 256) + 8) ≤ A_SB ∨ A_HMB ≤ Fr)) :
    ((rem - 0) + (-1)) = (rem + (-1)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qt1H.v (replace)
example {T1 : Type} (length : T1 → Nat) (str : T1) :
    ((((length str) : Nat) : Int) + 1) = ((((Int.toNat ((((length str) : Nat) : Int) + 1)) + 0) : Nat) : Int) := by
  lia

-- json-c/json_object_fuzzer: lib/QteI.v (replace)
example
    {T1 : Type}
    (j : Nat)
    (nfk : Nat)
    (length : T1 → Nat)
    (FL : T1)
    (k : Int)
    (nf : Int)
    (h1 : (length FL) = (nfk + (Int.toNat k)))
    (h2 : ((nfk : Nat) : Int) = (nf - k)) :
    j = ((nfk + j) - (min nfk (length FL))) := by
  lia

-- json-c/json_object_fuzzer: lib/QteI.v (replace)
example
    {T1 : Type}
    (fb : Int)
    (nf : Int)
    (k : Int)
    (nfk : Nat)
    (length : T1 → Nat)
    (FL : T1)
    (h1 : (length FL) = (nfk + (Int.toNat k)))
    (h2 : ((nfk : Nat) : Int) = (nf - k)) :
    (fb + (4 * (nf - k))) = (fb + (4 * (((min nfk (length FL)) : Nat) : Int))) := by
  lia

-- json-c/json_object_fuzzer: lib/QteI.v (replace)
example (parr : Int) (nch : Int) :
    ((parr + (8 * nch)) + 8) = (parr + (8 * (nch + 1))) := by
  lia

-- json-c/json_object_fuzzer: lib/QtkK.v (replace)
example (usp0 : Int) :
    ((usp0 - 128) + 8) = (usp0 - 120) := by
  lia

-- json-c/json_object_fuzzer: lib/QtkK.v (replace)
example
    {list_byte : Type}
    (data : list_byte)
    (len : Int)
    (cap : Int)
    (cnt : Int)
    (nb : Nat)
    (length : list_byte → Nat)
    (junk : list_byte)
    (bs : list_byte)
    (h1 : len < cap)
    (h2 : (1 ≤ cnt ∧ cnt ≤ 65536))
    (h3 : cnt ≤ (cap - len))
    (h4 : (length junk) = (Int.toNat (cap - len)))
    (h5 : (length bs) = (min (Int.toNat cnt) ((length data) - (Int.toNat len))))
    (h6 : len = (((length data) : Nat) : Int)) :
    (len + ((nb : Nat) : Int)) = (((nb : Nat) : Int) + len) := by
  lia

-- json-c/json_object_fuzzer: lib/Quoa.v (replace)
example
    {heap_iface_S4L word T3 : Type}
    (HIx : heap_iface_S4L)
    (ra : word)
    (sp : word)
    (lo : Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (usp : Int)
    (hi_top : T3 → heap_iface_S4L → Int)
    (S4L : T3)
    (Z_to_bv : Int → Int → word)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : lo ≤ ((usp - 192) - 8320))
    (h3 : (usp % 16) = 0)
    (h4 : usp ≤ (hi_top S4L HIx))
    (h5 : ((bv_unsigned ra) % 2) = 0)
    (h6 : (bv_unsigned (Z_to_bv 64 (usp + (-192)))) = (usp + (-192))) :
    ((bv_unsigned sp) - (16 * 12)) = ((bv_unsigned sp) + (-192)) := by
  lia

-- json-c/json_object_fuzzer: lib/QvPk.v (replace)
example (ns : Int) (h1 : (1 ≤ (ns * 40) ∧ (ns * 40) < (2 ^ (40 : Nat)))) :
    (Int.toNat (40 * (((Int.toNat ns) : Nat) : Int))) = (Int.toNat (ns * 40)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qw5U.v (replace)
example
    (AB : Int)
    (j : Int)
    (b : Int)
    (sz : Int)
    (AE : Int)
    (h1 : ((b ≤ AB ∧ AB ≤ (b + 7)) ∧ (AB % 8) = 0))
    (h2 : ((((b + sz) - 7) ≤ AE ∧ AE ≤ (b + sz)) ∧ (AE % 8) = 0))
    (h3 : ((AB + (8 * j)) + 8) ≤ AE) :
    (AB + (8 * (j + 1))) = ((AB + (8 * j)) + 8) := by
  lia

-- json-c/json_object_fuzzer: lib/QwKH.v (assert)
example
    {byte : Type}
    (c : byte)
    (bv_unsigned : byte → Int)
    (h1 : (32 ≤ (bv_unsigned c) ∧ (bv_unsigned c) ≤ 47))
    (h2 : (bv_unsigned c) ≠ 34)
    (h3 : (bv_unsigned c) ≠ 47) :
    ((bv_unsigned c) = 32 ∨ ((bv_unsigned c) = 33 ∨ ((bv_unsigned c) = 35 ∨ ((bv_unsigned c) = 36 ∨ ((bv_unsigned c) = 37 ∨ ((bv_unsigned c) = 38 ∨ ((bv_unsigned c) = 39 ∨ ((bv_unsigned c) = 40 ∨ ((bv_unsigned c) = 41 ∨ ((bv_unsigned c) = 42 ∨ ((bv_unsigned c) = 43 ∨ ((bv_unsigned c) = 44 ∨ ((bv_unsigned c) = 45 ∨ (bv_unsigned c) = 46))))))))))))) := by
  lia

-- json-c/json_object_fuzzer: lib/Qylf.v (replace)
example
    {T1 : Type}
    (Bx : Int)
    (tbl : Int)
    (le_ix : T1 → Nat)
    (el : T1)
    (e : T1)
    (x0 : T1)
    (size : Int)
    (Bl : Int)
    (h1 : (le_ix el) ≠ (le_ix e))
    (h2 : (le_ix x0) ≠ (le_ix e))
    (h3 : Bx = (tbl + (40 * (((le_ix e) : Nat) : Int))))
    (h4 : (Bx % 8) = 0)
    (h5 : (tbl ≤ Bx ∧ (Bx + 40) ≤ (tbl + (40 * size))))
    (h6 : Bl = (tbl + (40 * (((le_ix el) : Nat) : Int))))
    (h7 : (Bl % 8) = 0)
    (h8 : (tbl ≤ Bl ∧ (Bl + 40) ≤ (tbl + (40 * size)))) :
    Bx = (tbl + (Bx - tbl)) := by
  lia

-- json-c/json_object_fuzzer: lib/Qzoi.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    (bv_unsigned sp) = (((bv_unsigned sp) - 144) + 144) := by
  lia

-- jsoncons/fuzz_bigint: lib/ArtAllocate3.v (replace)
example
    (qr : Int)
    (qz : Int)
    (n : Int)
    (rs : Int)
    (rz : Int)
    (h1 : ((n + 7) / 8) = qr)
    (h2 : rs = ((((max n 8) + 7) / 8) * 8))
    (h3 : ((rs + rz) % 8) = 0) :
    ((qr + (2 * qz)) * 8) = ((8 * qr) + (16 * qz)) := by
  lia

-- jsoncons/fuzz_bigint: lib/ArtAllocate3.v (replace)
example
    (qs : Int)
    (c : Int)
    (w : Int)
    (qz : Int)
    (ab : Int)
    (spb : Int)
    (shb : Int)
    (km : Int)
    (n : Int)
    (qr : Int)
    (rs : Int)
    (rz : Int)
    (h1 : ab = ((spb + (c * (2 ^ (32 : Nat)))) + (w * 16)))
    (h2 : shb = ((2147450880 + (8192 * qs)) + (c * (2 ^ (29 : Nat)))))
    (h3 : 0 ≤ km)
    (h4 : (262144 * km) ≤ 3758096384)
    (h5 : ((n + 7) / 8) = qr)
    (h6 : rs = ((((max n 8) + 7) / 8) * 8))
    (h7 : ((rs + rz) % 8) = 0)
    (h8 : (ab % 16) = 0)
    (h9 : (rz % 16) = 0)
    (h10 : (ab / 8) = (((8192 * qs) + (c * (2 ^ (29 : Nat)))) + (2 * w)))
    (h11 : ((ab + rz) / 8) = ((((8192 * qs) + (c * (2 ^ (29 : Nat)))) + (2 * w)) + (2 * qz))) :
    (((((8192 * qs) + (c * (2 ^ (29 : Nat)))) + (2 * w)) + (2 * qz)) * 8) = ((((65536 * qs) + (c * (2 ^ (32 : Nat)))) + (w * 16)) + (16 * qz)) := by
  lia

-- jsoncons/fuzz_bigint: lib/ArtClsPop3.v (replace)
example
    (fa : Int)
    (j : Nat)
    (nf : Int)
    (new : Int)
    (k : Nat)
    (h1 : 0 ≤ nf)
    (h2 : k < (Int.toNat new))
    (h3 : ((j : Nat) : Int) = (nf + ((k : Nat) : Int))) :
    (fa + (4 * ((j : Nat) : Int))) = ((fa + (4 * (nf + new))) - (4 * (((new - 1) - ((k : Nat) : Int)) + 1))) := by
  lia

-- jsoncons/fuzz_bigint: lib/BrtClsPop2.v (replace)
example
    (q : Int)
    (kf : Int)
    (mfa : Int)
    (h1 : (kf + 1) ≤ q)
    (h2 : (((262144 * q) - mfa) % 4096) = 0) :
    ((64 * (q - kf)) * 4096) = ((262144 * q) - (262144 * kf)) := by
  lia

-- jsoncons/fuzz_bigint: lib/BrtInvFree.v (replace)
example
    {art_run : Type}
    (rn : art_run)
    (Sp : Int)
    (u : Int)
    (q16 : Int)
    (rn_HI : art_run → Int)
    (HeapIfaceA_S : Int → Int)
    (h1 : u = (16 * q16))
    (h2 : ((rn_HI rn) + 4096) ≤ (Sp - 4096))
    (h3 : Sp < (2 ^ (47 : Nat)))
    (h4 : (HeapIfaceA_S u) = (2147450880 + (2 * q16))) :
    (16 * q16) = (((65536 * 0) + (0 * (2 ^ (32 : Nat)))) + (8 * (2 * q16))) := by
  lia

-- jsoncons/fuzz_bigint: lib/BrtInvMallocPure.v (replace)
example (sz : Int) (ka : Int) (i : Int) (w0 : Int) (h1 : (16 * w0) = (sz * (ka + i))) :
    (sz * (ka + i)) = ((sz * ka) + (i * sz)) := by
  lia

-- jsoncons/fuzz_bigint: lib/BrtRecycle3L.v (replace)
example
    {T1 T2 : Type}
    (ca : Int)
    (c : Int)
    (k : Nat)
    (j : Nat)
    (cnt : Int)
    (h_1 : Int)
    (r : Int)
    (ris : Int)
    (fa : Int)
    (spb : Int)
    (nf : Int)
    (hn : Nat)
    (length : T1 → Nat)
    (ws : T1)
    (cl : T2)
    (cl_cache : T2 → T1)
    (h1 : r = (ris + (128 * c)))
    (h2 : fa = ((spb + (c * (2 ^ (32 : Nat)))) + 3758096384))
    (h3 : 0 ≤ cnt)
    (h4 : 0 ≤ nf)
    (h5 : ((hn : Nat) : Int) = h_1)
    (h6 : ((k : Nat) : Int) = (cnt - h_1))
    (h7 : (length ws) = hn)
    (h8 : (k + j) < (length (cl_cache cl))) :
    (((ca + (80 * c)) + 16) + (4 * (((k + j) : Nat) : Int))) = ((((ca + (80 * c)) + 16) + (4 * (cnt - h_1))) + (4 * ((j : Nat) : Int))) := by
  lia

-- jsoncons/fuzz_bigint: lib/BrtRecycle3L.v (replace)
example
    {T1 T2 : Type}
    (sp : Int)
    (r : Int)
    (ris : Int)
    (c : Int)
    (fa : Int)
    (spb : Int)
    (cnt : Int)
    (nf : Int)
    (hn : Nat)
    (h_1 : Int)
    (k : Nat)
    (length : T1 → Nat)
    (ws : T1)
    (cl : T2)
    (j : Nat)
    (cl_cache : T2 → T1)
    (h1 : r = (ris + (128 * c)))
    (h2 : fa = ((spb + (c * (2 ^ (32 : Nat)))) + 3758096384))
    (h3 : 0 ≤ cnt)
    (h4 : 0 ≤ nf)
    (h5 : ((hn : Nat) : Int) = h_1)
    (h6 : ((k : Nat) : Int) = (cnt - h_1))
    (h7 : (length ws) = hn)
    (h8 : (k + j) < (length (cl_cache cl))) :
    (sp - 320) = ((sp - 48) - 272) := by
  lia

-- jsoncons/fuzz_bigint: lib/BrtRecycle4.v (replace)
example (m : Int) (h1 : (m % 4) = 0) :
    ((4 * (m / 16)) * 4) = ((16 * (m / 16)) + 0) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5AdddPU.v (replace)
example
    {T1 T2 T3 : Type}
    (last : Bool)
    (wrap : Bool)
    (sp : Int)
    (o : Int)
    (data : Int)
    (X : Int)
    (i : Nat)
    (n : Nat)
    (bv_unsigned : T1 → Int)
    (ev : T2 → Int → T1)
    (E : T2)
    (edenot : T2 → T3 → T1)
    (e_qi : T3)
    (e_qn : T3)
    (h1 : (0 ≤ o ∧ o < (2 ^ (64 : Nat))))
    (h2 : (sp % 16) = 0)
    (h3 : (140735332483072 + 112) ≤ sp)
    (h4 : sp ≤ (2 ^ (47 : Nat)))
    (h5 : 4096 ≤ data)
    (h6 : (data % 8) = 0)
    (h7 : (data + (8 * ((n : Nat) : Int))) ≤ (2 ^ (47 : Nat)))
    (h8 : (2 ≤ n ∧ n ≤ ((2 ^ 23) + 1)))
    (h9 : (0 ≤ X ∧ X < (2 ^ (64 : Nat))))
    (h10 : (last = false → (wrap = true ↔ X = ((2 ^ (64 : Nat)) - 1))))
    (h11 : (2 ≤ i ∧ i ≤ n))
    (h12 : (bv_unsigned (ev E 2)) = sp)
    (h13 : (bv_unsigned (ev E 35)) = o)
    (h14 : (bv_unsigned (ev E 32)) = ((n : Nat) : Int))
    (h15 : (bv_unsigned (ev E 37)) = data)
    (h16 : (bv_unsigned (ev E 39)) = ((i : Nat) : Int))
    (h17 : (bv_unsigned (ev E 40)) = X)
    (h18 : (bv_unsigned (edenot E e_qi)) = (data + (8 * ((i : Nat) : Int))))
    (h19 : (bv_unsigned (edenot E e_qn)) = (data + (8 * ((n : Nat) : Int)))) :
    (data + (8 * (((i : Nat) : Int) - 1))) = ((data + (8 * ((i : Nat) : Int))) + (-8)) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5AdddPU.v (replace)
example
    {T1 T2 T3 : Type}
    (last : Bool)
    (wrap : Bool)
    (sp : Int)
    (o : Int)
    (data : Int)
    (X : Int)
    (i : Nat)
    (n : Nat)
    (bv_unsigned : T1 → Int)
    (ev : T2 → Int → T1)
    (E : T2)
    (edenot : T2 → T3 → T1)
    (e_qi : T3)
    (e_qn : T3)
    (h1 : (0 ≤ o ∧ o < (2 ^ (64 : Nat))))
    (h2 : (sp % 16) = 0)
    (h3 : (140735332483072 + 112) ≤ sp)
    (h4 : sp ≤ (2 ^ (47 : Nat)))
    (h5 : 4096 ≤ data)
    (h6 : (data % 8) = 0)
    (h7 : (data + (8 * ((n : Nat) : Int))) ≤ (2 ^ (47 : Nat)))
    (h8 : (2 ≤ n ∧ n ≤ ((2 ^ 23) + 1)))
    (h9 : (0 ≤ X ∧ X < (2 ^ (64 : Nat))))
    (h10 : (last = false → (wrap = true ↔ X = ((2 ^ (64 : Nat)) - 1))))
    (h11 : (2 ≤ i ∧ i ≤ n))
    (h12 : (bv_unsigned (ev E 2)) = sp)
    (h13 : (bv_unsigned (ev E 35)) = o)
    (h14 : (bv_unsigned (ev E 32)) = ((n : Nat) : Int))
    (h15 : (bv_unsigned (ev E 37)) = data)
    (h16 : (bv_unsigned (ev E 39)) = ((i : Nat) : Int))
    (h17 : (bv_unsigned (ev E 40)) = X)
    (h18 : (bv_unsigned (edenot E e_qi)) = (data + (8 * ((i : Nat) : Int))))
    (h19 : (bv_unsigned (edenot E e_qn)) = (data + (8 * ((n : Nat) : Int)))) :
    (data + (8 * (((n : Nat) : Int) - 1))) = ((data + (8 * ((n : Nat) : Int))) + (-8)) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5AdddPU.v (replace)
example
    (k : Nat)
    (dd : Nat)
    (sp : Int)
    (o : Int)
    (data : Int)
    (V : Int)
    (d : Int)
    (len : Nat)
    (j : Nat)
    (W_M : Int)
    (Zpow : Int → Int → Int)
    (acarry : Int → Int → Nat → Int)
    (h1 : (dd + k) = len)
    (h2 : 1 ≤ dd)
    (h3 : ((len : Nat) : Int) ≤ (2 ^ (23 : Nat)))
    (h4 : (0 ≤ V ∧ V < (Zpow W_M ((len : Nat) : Int))))
    (h5 : (0 ≤ d ∧ d ≤ 9))
    (h6 : 4096 ≤ data)
    (h7 : (data % 8) = 0)
    (h8 : (data + (8 * (((len : Nat) : Int) + 1))) ≤ (2 ^ (47 : Nat)))
    (h9 : ((data + (8 * (((len : Nat) : Int) + 1))) ≤ (sp - 112) ∨ sp ≤ data))
    (h10 : (0 ≤ o ∧ o < (2 ^ (64 : Nat))))
    (h11 : (sp % 16) = 0)
    (h12 : (140735332483072 + 112) ≤ sp)
    (h13 : sp ≤ (2 ^ (47 : Nat)))
    (h14 : (acarry d V dd) = 1)
    (h15 : j = len) :
    (data + (8 * ((j : Nat) : Int))) = (data + (8 * ((((j + 1) : Nat) : Int) - 1))) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5CoreKitS.v (replace)
example :
    ((1 + (7 + (8 + (8 + 8)))) : Int) = 32 := by
  lia

-- jsoncons/fuzz_bigint: lib/L5DetailPU.v (assert)
example (h1 : ((0 : Int) ≤ 1 ∧ (1 : Int) ≤ 255)) :
    ((0 : Int) ≤ 1 ∧ (1 : Int) < (2 ^ (64 : Nat))) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5DetailPU.v (assert)
example
    (sp : Int)
    (A : Int)
    (cap : Int)
    (h1 : (0 ≤ sp ∧ sp < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ A ∧ A < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ cap ∧ cap < (2 ^ (64 : Nat))))
    (h4 : (140735332483184 ≤ sp ∧ sp ≤ 140737488355328))
    (h5 : ((0 : Int) ≤ 1 ∧ (1 : Int) ≤ 255))
    (h6 : (4096 ≤ A ∧ A ≤ 140737488355327))
    (h7 : (1 ≤ cap ∧ cap ≤ 134217728))
    (h8 : ((0 : Int) ≤ 1 ∧ (1 : Int) < (2 ^ (64 : Nat))))
    (h9 : ((0 : Int) ≤ 0 ∧ (0 : Int) < (2 ^ (64 : Nat)))) :
    (140735332483184 ≤ sp ∧ sp ≤ 140737488355328) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5DetailU.v (replace)
example (sp : Int) :
    (sp + (8 * (-14))) = (sp - 112) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5DivEq.v (replace)
example (sp : Int) (a : Int) :
    ((sp - (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224))))))))) + (a - (sp - (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224))))))))))) = a := by
  lia

-- jsoncons/fuzz_bigint: lib/L5Mul10P.v (replace)
example (q : Int) (i : Nat) (n : Nat) (h1 : n = (i + 1)) :
    (q + (8 * (((i + 1) : Nat) : Int))) = ((q + (8 * (((i : Nat) : Int) + 1))) + 0) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5Mul10PU.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (R : T1)
    (sp : Int)
    (data : Int)
    (X : Int)
    (C : Int)
    (NEXT : Int)
    (I : Nat)
    (n : Nat)
    (getr : T1 → T2 → T3)
    (reg : Int → T2)
    (bv_unsigned : T3 → Int)
    (ev : T4 → Int → T3)
    (E : T4)
    (edenot : T4 → T5 → T3)
    (e_qI : T5)
    (e_qn : T5)
    (e_bl : T5)
    (e_nI : T5)
    (E' : T4)
    (h1 : (bv_unsigned (getr R (reg 20))) = X)
    (h2 : (bv_unsigned (getr R (reg 22))) = C)
    (h3 : (sp % 16) = 0)
    (h4 : (140735332483072 + 96) ≤ sp)
    (h5 : sp ≤ (2 ^ (47 : Nat)))
    (h6 : 4096 ≤ data)
    (h7 : (data % 8) = 0)
    (h8 : (data + (8 * (((n : Nat) : Int) + 1))) ≤ (2 ^ (47 : Nat)))
    (h9 : ((data + (8 * (((n : Nat) : Int) + 1))) ≤ (sp - 96) ∨ sp ≤ data))
    (h10 : 1 ≤ n)
    (h11 : ((n : Nat) : Int) ≤ (2 ^ (23 : Nat)))
    (h12 : (0 ≤ NEXT ∧ NEXT < (2 ^ (64 : Nat))))
    (h13 : (I + 1) ≤ n)
    (h14 : (bv_unsigned (ev E 2)) = sp)
    (h15 : (bv_unsigned (ev E 33)) = ((n : Nat) : Int))
    (h16 : (bv_unsigned (ev E 35)) = data)
    (h17 : (bv_unsigned (ev E 36)) = NEXT)
    (h18 : (bv_unsigned (ev E 40)) = ((I : Nat) : Int))
    (h19 : (bv_unsigned (ev E 32)) = X)
    (h20 : (bv_unsigned (ev E 41)) = C)
    (h21 : (bv_unsigned (edenot E e_qI)) = (data + (8 * ((I : Nat) : Int))))
    (h22 : (bv_unsigned (edenot E e_qn)) = (data + (8 * ((n : Nat) : Int))))
    (h23 : (bv_unsigned (edenot E e_bl)) = (8 * (((n : Nat) : Int) + 1)))
    (h24 : (bv_unsigned (edenot E e_nI)) = (((n : Nat) : Int) - ((I : Nat) : Int)))
    (h25 : (bv_unsigned (edenot E' e_qI)) = (data + (8 * ((I : Nat) : Int)))) :
    ((data + (8 * ((I : Nat) : Int))) + 0) = (data + (8 * ((I : Nat) : Int))) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5Mul10PU.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (R : T1)
    (o : Int)
    (data : Int)
    (c : Int)
    (sp : Int)
    (n : Nat)
    (getr : T1 → T2 → T3)
    (reg : Int → T2)
    (bv_unsigned : T3 → Int)
    (ev : T4 → Int → T3)
    (E : T4)
    (edenot : T4 → T5 → T3)
    (e_qn : T5)
    (e_bl : T5)
    (E' : T4)
    (h1 : (bv_unsigned (getr R (reg 22))) = c)
    (h2 : (0 ≤ o ∧ o < (2 ^ (64 : Nat))))
    (h3 : 4096 ≤ data)
    (h4 : (data % 8) = 0)
    (h5 : ((n : Nat) : Int) ≤ (2 ^ (23 : Nat)))
    (h6 : (data + (8 * (((n : Nat) : Int) + 1))) ≤ (2 ^ (47 : Nat)))
    (h7 : ((data + (8 * (((n : Nat) : Int) + 1))) ≤ (sp - 96) ∨ sp ≤ data))
    (h8 : (sp % 16) = 0)
    (h9 : (140735332483072 + 96) ≤ sp)
    (h10 : sp ≤ (2 ^ (47 : Nat)))
    (h11 : (bv_unsigned (ev E 2)) = sp)
    (h12 : (bv_unsigned (ev E 42)) = o)
    (h13 : (bv_unsigned (ev E 35)) = data)
    (h14 : (bv_unsigned (ev E 33)) = ((n : Nat) : Int))
    (h15 : (bv_unsigned (ev E 41)) = c)
    (h16 : (bv_unsigned (edenot E e_qn)) = (data + (8 * ((n : Nat) : Int))))
    (h17 : (bv_unsigned (edenot E e_bl)) = (8 * (((n : Nat) : Int) + 1)))
    (h18 : (bv_unsigned (edenot E' e_qn)) = (data + (8 * ((n : Nat) : Int)))) :
    ((data + (8 * ((n : Nat) : Int))) + 0) = (data + (8 * ((n : Nat) : Int))) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5Mul10TU.v (replace)
example
    {T1 : Type}
    (o : Int)
    (len : Nat)
    (length : T1 → Nat)
    (wl : T1)
    (h1 : (length wl) = (len + 1)) :
    (o + 24) = ((o + 16) + (8 * ((1 : Nat) : Int))) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5ReduceGU.v (replace)
example
    {word T2 : Type}
    (o : Int)
    (fb : Int)
    (bv_unsigned : word → Int)
    (ev : T2 → Int → word)
    (E : T2)
    (E' : T2)
    (h1 : (2 ^ (20 : Nat)) ≤ o)
    (h2 : (o + 32) ≤ (2 ^ (47 : Nat)))
    (h3 : (o % 8) = 0)
    (h4 : (0 ≤ fb ∧ fb < 256))
    (h5 : (bv_unsigned (ev E 10)) = o)
    (h6 : (bv_unsigned (ev E 33)) = fb)
    (h7 : (bv_unsigned (ev E' 10)) = o)
    (h8 : (bv_unsigned (ev E' 33)) = fb) :
    (o + 0) = o := by
  lia

-- jsoncons/fuzz_bigint: lib/L5ReduceGU.v (replace)
example
    {L5_bigobj list_Z : Type}
    (o : Int)
    (b : L5_bigobj)
    (ws : list_Z)
    (length : list_Z → Nat)
    (L5_bo_len : L5_bigobj → Nat)
    (h1 : (o % 8) = 0)
    (h2 : (2 ^ (20 : Nat)) ≤ o)
    (h3 : (o + 32) ≤ (2 ^ (47 : Nat)))
    (h4 : (length ws) = (L5_bo_len b)) :
    (o + (2 * 8)) = (o + 16) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5Reserve.v (replace)
example
    {T1 T2 : Type}
    (o : Int)
    (n : Int)
    (sp : Int)
    (fb : Int)
    (len : Int)
    (v0 : Int)
    (v1 : Int)
    (Z_testbit : Int → Int → Bool)
    (bv_unsigned : T1 → Int)
    (ev : T2 → Int → T1)
    (E : T2)
    (E' : T2)
    (h1 : (3 ≤ n ∧ n ≤ (2 ^ (23 : Nat))))
    (h2 : (sp % 16) = 0)
    (h3 : (140735332483072 + 64) ≤ sp)
    (h4 : sp ≤ (2 ^ (47 : Nat)))
    (h5 : (o % 8) = 0)
    (h6 : sp ≤ o)
    (h7 : (o + 32) ≤ (2 ^ (47 : Nat)))
    (h8 : (0 ≤ fb ∧ fb < 256))
    (h9 : (Z_testbit fb 0) = false)
    (h10 : (0 ≤ len ∧ len < (2 ^ (64 : Nat))))
    (h11 : (0 ≤ v0 ∧ v0 < (2 ^ (64 : Nat))))
    (h12 : (0 ≤ v1 ∧ v1 < (2 ^ (64 : Nat))))
    (h13 : (bv_unsigned (ev E 2)) = sp)
    (h14 : (bv_unsigned (ev E 10)) = o)
    (h15 : (bv_unsigned (ev E 11)) = n)
    (h16 : (bv_unsigned (ev E 33)) = fb)
    (h17 : (bv_unsigned (ev E 34)) = len)
    (h18 : (bv_unsigned (ev E 36)) = v0)
    (h19 : (bv_unsigned (ev E 37)) = v1)
    (h20 : (bv_unsigned (ev E' 2)) = sp)
    (h21 : (bv_unsigned (ev E' 10)) = o) :
    (sp + (-16)) = (sp - 16) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5SubMul.v (replace)
example (sp : Int) (h1 : ((sp % 16) = 0 ∧ (1048592 ≤ sp ∧ sp ≤ 140737488355328))) :
    (sp - 8) = (sp + (-8)) := by
  lia

-- jsoncons/fuzz_bigint: lib/L5TStrinitU.v (replace)
example
    (sp : Int)
    (i : Int)
    (o : Int)
    (cap : Int)
    (A : Int)
    (a : Int)
    (h1 : (¬ (o ≤ a ∧ a < (o + 24))))
    (h2 : (¬ ((sp - 8288) ≤ a ∧ a < sp)))
    (h3 : (¬ (A ≤ a ∧ a < (A + cap)))) :
    (((sp + (-48)) - (16 + 8224)) + i) = ((sp - (48 + (16 + 8224))) + i) := by
  lia

-- jsoncons/fuzz_bigint: lib/Ub0DrvG.v (replace)
example
    {list_byte T2 T3 T4 word : Type}
    (path : list_byte)
    (Kc : Int)
    (Bc : Int)
    (A : Int)
    (len : Int)
    (i : Int)
    (length : list_byte → Nat)
    (LEN : Int)
    (want : Int)
    (CAPk : T2 → Int)
    (k : T2)
    (bs : list_byte)
    (M1 : T3)
    (RSEGS : T4)
    (Z_to_bv : Int → Int → word)
    (vals1 : list_byte)
    (nb : Int)
    (store_ok : T4 → T3 → word → Nat → Bool)
    (h1 : (length path) ≤ 4095)
    (h2 : 0 ≤ Kc)
    (h3 : 0 ≤ Bc)
    (h4 : ((1 ≤ want ∧ want ≤ 65536) ∧ want ≤ ((CAPk k) - len)))
    (h5 : (((length bs) : Nat) : Int) = (min want (LEN - len)))
    (h6 : len = LEN)
    (h7 : (length vals1) = 73)
    (h8 : (length bs) = (Int.toNat nb))
    (h9 : (store_ok RSEGS M1 (Z_to_bv 64 (A + len)) (length bs)) = true) :
    (A + (len + i)) = ((A + len) + i) := by
  lia

-- jsoncons/fuzz_bigint: lib/Ub0OpenFail_tail2.v (replace)
example
    {word list_byte : Type}
    (sp0 : word)
    (path : list_byte)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : (((length path) : Nat) : Int) = 63) :
    ((bv_unsigned sp0) + (-544)) = ((((bv_unsigned sp0) + (-560)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) := by
  lia

-- jsoncons/fuzz_bigint: lib/asan/L5AMulArith.v (replace)
example
    {T1 : Type}
    (x : Int)
    (c : Int)
    (vhh : Int)
    (M64 : Int)
    (Datatypes_S : T1 → Nat)
    (i : T1)
    (Zpow : Int → Int → Int)
    (P : Int)
    (vh : Int)
    (v : Int)
    (vl : Int)
    (h1 : (Zpow M64 (((Datatypes_S i) : Nat) : Int)) = (P * M64))
    (h2 : 0 ≤ vh)
    (h3 : (Int.fdiv (10 * v) P) = ((10 * vh) + (Int.fdiv (10 * vl) P)))
    (h4 : (0 ≤ c ∧ c < 10))
    (h5 : c = (Int.fdiv (10 * vl) P)) :
    (((10 * x) + c) + ((10 * vhh) * M64)) = ((10 * ((M64 * vhh) + x)) + c) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/Ba0PgSrcFillTb.v (replace)
example
    {T1 T2 T3 : Type}
    (sp : Int)
    (os : Int)
    (bv_unsigned : T1 → Int)
    (getr : T2 → T3 → T1)
    (R : T2)
    (reg : Int → T3)
    (qc : Int)
    (B : Int)
    (h1 : (bv_unsigned (getr R (reg 10))) = os)
    (h2 : B ≠ qc)
    (h3 : ((sp - 18432) % 8) = 0)
    (h4 : (((sp - 48) - 16384) % 8) = 0) :
    (sp + ((-1027) * 16)) = ((sp - 48) - 16384) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/Ba0PgVu8Rz.v (replace)
example
    (sp : Int)
    (v : Int)
    (h1 : ((v + 24) ≤ (sp - 16) ∨ sp ≤ v))
    (h2 : ((sp - 14336) % 8) = 0)
    (h3 : ((sp - 0) % 16) = 0) :
    (sp + ((-896) * 16)) = (sp - 14336) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/BatDepotB.v (replace)
example (s : Int) :
    (s - 208) = (((s - 112) - 32) - 64) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/BatFxBatch1.v (replace)
example (cnt : Int) :
    ((4 * (cnt - 1)) * (2 ^ (30 : Nat))) = ((cnt + (-1)) * (2 ^ (32 : Nat))) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/BatFxBatch2.v (replace)
example
    {T1 : Type}
    (ca : Int)
    (t : Int)
    (c : Int)
    (b : Int)
    (spb : Int)
    (art_ca_cptr : Int → T1 → Int)
    (cl : T1)
    (L : Int)
    (B : Int)
    (cl_au : T1 → Int)
    (h1 : ((1 : Int) ≤ 24 ∧ (24 : Int) ≤ 30))
    (h2 : c = (t + 80))
    (h3 : ca = (t + 208))
    (h4 : b = ((spb + (24 * (2 ^ (32 : Nat)))) + (16 * (art_ca_cptr 24 cl))))
    (h5 : (L ≠ 0 → ((spb + (24 * (2 ^ (32 : Nat)))) ≤ B ∧ (B + 8192) ≤ ((spb + (24 * (2 ^ (32 : Nat)))) + (cl_au cl))))) :
    (ca + (80 * 24)) = (ca + 1920) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/BatInvFrameS.v (replace)
example {art_run : Type} (rn : art_run) (c : Int) (w : Int) (rn_qs : art_run → Int) :
    ((((8192 * (rn_qs rn)) + (c * (2 ^ (29 : Nat)))) + (2 * w)) * 8) = (((65536 * (rn_qs rn)) + (c * (2 ^ (32 : Nat)))) + (16 * w)) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/BatInvFree.v (replace)
example
    {art_run T2 : Type}
    (rn : art_run)
    (Sp : Int)
    (u : Int)
    (q16 : Int)
    (km : Int)
    (x : Int)
    (rn_qs : art_run → Int)
    (rn_HI : art_run → Int)
    (cl_mu : T2 → Int)
    (cl24 : T2)
    (newb : Bool)
    (art_ca_pre : Int → T2 → T2)
    (cl_au : T2 → Int)
    (h1 : u = (16 * q16))
    (h2 : ((rn_HI rn) + 4096) ≤ (Sp - 4096))
    (h3 : Sp < (2 ^ (47 : Nat)))
    (h4 : (cl_mu cl24) = (262144 * km))
    (h5 : newb = true)
    (h6 : ((cl_au cl24) ≤ x ∧ x < (cl_mu (art_ca_pre 24 cl24))))
    (h7 : (x % 8) = 0)
    (h8 : x = (8 * (x / 8))) :
    (((2147450880 + (8192 * (rn_qs rn))) + (24 * (2 ^ (29 : Nat)))) + (x / 8)) = ((((2147450880 + (8192 * (rn_qs rn))) + (24 * (2 ^ (29 : Nat)))) + (32768 * km)) + ((x / 8) - (32768 * km))) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/BatInvRecycle.v (replace)
example
    {art_run : Type}
    (rn : art_run)
    (sp : Int)
    (rn_qs : art_run → Int)
    (wb : Int)
    (rn_HI : art_run → Int)
    (h1 : (rn_HI rn) ≤ (sp - 512)) :
    ((((8192 * (rn_qs rn)) + (3 * (2 ^ (32 : Nat)))) + (2 * wb)) * 8) = (((65536 * (rn_qs rn)) + (24 * (2 ^ (32 : Nat)))) + (16 * wb)) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/BatRecycle3R.v (replace)
example
    (sp : Int)
    (ia : Int)
    (mp : Int)
    (st : Int)
    (c : Int)
    (chp : Int)
    (n : Int)
    (spb : Int)
    (ris : Int)
    (qris : Int)
    (h1 : (6897664 + 128) ≤ sp)
    (h2 : sp < (2 ^ (64 : Nat)))
    (h3 : 65536 ≤ ia)
    (h4 : (ia + 4096) ≤ 6897664)
    (h5 : (1 ≤ c ∧ c ≤ 31))
    (h6 : 0 ≤ spb)
    (h7 : (spb + (2 ^ (37 : Nat))) < (2 ^ (47 : Nat)))
    (h8 : 0 ≤ ris)
    (h9 : (ris + (128 * 64)) < (2 ^ (47 : Nat)))
    (h10 : ris = (128 * qris))
    (h11 : (0 ≤ mp ∧ mp < (2 ^ (64 : Nat))))
    (h12 : (0 ≤ st ∧ st < (2 ^ (64 : Nat))))
    (h13 : (0 ≤ chp ∧ chp < (2 ^ (64 : Nat))))
    (h14 : (0 ≤ n ∧ n < (2 ^ (64 : Nat))))
    (h15 : ((ris + (c * (2 ^ (7 : Nat)))) % 8) = 0) :
    (((16 * qris) + (16 * c)) * 8) = ((128 * qris) + (c * (2 ^ (7 : Nat)))) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/Bs0HeapBridge.v (replace)
example
    {word list_byte list_list_byte : Type}
    (sp0 : word)
    (a0s : list_byte)
    (path : list_byte)
    (envv : list_list_byte)
    (tid : word)
    (bv_unsigned : word → Int)
    (rnd : word → list_byte → list_byte → list_list_byte → word)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat)))) :
    ((bv_unsigned (rnd sp0 a0s path envv)) + ((8 : Nat) : Int)) = ((bv_unsigned (rnd sp0 a0s path envv)) + 8) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/Bs0PgSrcFillTb.v (replace)
example
    {heap_layout : Type}
    (L : heap_layout)
    (ois : Int)
    (sp : Int)
    (os : Int)
    (hl_sptop : heap_layout → Int)
    (p' : Int)
    (p : Int)
    (qc : Int)
    (B : Int)
    (g : Int)
    (eg : Int)
    (h1 : (sp ≤ os ∧ (sp ≤ ois ∧ ((os + 296) ≤ (hl_sptop L) ∧ ((ois + 272) ≤ (hl_sptop L) ∧ ((os + 296) ≤ ois ∨ (ois + 272) ≤ os))))))
    (h2 : (0 : Int) ≤ 18432)
    (h3 : p' = p)
    (h4 : B ≠ qc)
    (h5 : (hl_sptop L) ≤ (2 ^ (47 : Nat)))
    (h6 : ((p + 16384) ≤ g ∨ eg ≤ p))
    (h7 : (0 : Int) ≤ 16384) :
    ((ois + 120) + 32) = (ois + 152) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/PnSBarrG.v (replace)
example
    {T1 T2 T3 : Type}
    (m : Int)
    (L : T1)
    (k : Int)
    (Zpow : Int → Int → Int)
    (PM_sr_qc : T2 → Int)
    (PNM_b_src : T3 → T2)
    (s1 : T3)
    (b : Int)
    (hl_k_per_malloc : T1 → Int)
    (hl_b_overhead : T1 → Int)
    (h1 : 1 ≤ m)
    (h2 : k ≤ 10)
    (h3 : (Zpow 2 (k + 1)) = (2 * m))
    (h4 : (PM_sr_qc (PNM_b_src s1)) ≠ b)
    (h5 : ((hl_k_per_malloc L) * 1) ≤ ((hl_k_per_malloc L) * (11 - k)))
    (h6 : (1 * (hl_b_overhead L)) ≤ ((11 - k) * (hl_b_overhead L))) :
    (80 * m) = (40 * (2 * m)) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/PnSEnd.v (replace)
example (fb : Int) (h1 : ((fb + 40) % 8) = 0) (h2 : ((fb + 464) % 8) = 0) :
    ((fb + 40) + 400) = (fb + 440) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/PnSHarness11.v (replace)
example (sp : Int) (a : Int) :
    (((sp - 784) - (65536 - 784)) + (a - (sp - 65536))) = a := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/PnSParse.v (replace)
example
    (fb : Int)
    (h1 : ((fb + 40) % 8) = 0)
    (h2 : ((fb + 464) % 8) = 0)
    (h3 : ((fb + 472) % 8) = 0) :
    (((fb + 472) + 120) + 32) = ((fb + 472) + 152) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/PnSPushBack.v (replace)
example (k : Int) :
    ((((2 * k) - 1) * 8) + 6) = ((4 * ((4 * k) + 0)) - 2) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/PnStepA.v (replace)
example
    (o : Int)
    (n : Int)
    (i : Int)
    (SB : Int)
    (h1 : (o % 8) = 0)
    (h2 : (n % 8) = 0)
    (h3 : 0 ≤ n)
    (h4 : (8 * (n / 8)) = n)
    (h5 : (8 * (o / 8)) = o) :
    (((o / 8) + i) + SB) = (((o / 8) + SB) + i) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/PnTxtKit.v (replace)
example
    (w : Int)
    (n0 : Int)
    (h1 : (0 ≤ w ∧ w < (2 ^ (64 : Nat))))
    (h2 : (w % 256) = (2 * n0))
    (h3 : (0 ≤ n0 ∧ n0 ≤ 22))
    (h4 : (Int.fmod (72057594037927936 * w) (2 ^ (64 : Nat))) = (72057594037927936 * (w % 256))) :
    (n0 * 144115188075855872) = (72057594037927936 * (2 * n0)) := by
  lia

-- jsoncons/fuzz_bson_parser_max: lib/asan/L5StepAR.v (replace)
example (a : Int) (n : Int) (b : Int) (m : Int) (h1 : 0 < n) (h2 : 0 < m) :
    (a + ((max a b) - a)) = (b + ((max a b) - b)) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/BigFactsDigits.v (replace)
example
    (W_M : Int)
    (y : Int)
    (i : Nat)
    (Zpow : Int → Int → Int)
    (v : Int)
    (wordi : Int → Nat → Int)
    (h1 : y < (Zpow W_M ((i : Nat) : Int)))
    (h2 : (v + y) = (((Int.fmod v (Zpow W_M ((i : Nat) : Int))) + y) + (((wordi v i) + ((Int.fdiv v (Zpow W_M (((i + 1) : Nat) : Int))) * W_M)) * (Zpow W_M ((i : Nat) : Int)))))
    (h3 : (Zpow W_M ((i : Nat) : Int)) ≤ ((Int.fmod v (Zpow W_M ((i : Nat) : Int))) + y)) :
    W_M = ((W_M - 1) + 1) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/CJ/Pm10/RF_aligned.v (replace)
example
    {T1 : Type}
    (last_idx : Int)
    (freeable : Int)
    (sc : Int)
    (maplen : Int)
    (P : Int)
    (mword : Int)
    (idx : Int)
    (Z_to_bv : Int → Int → T1)
    (G : Int)
    (bv_unsigned : T1 → Int)
    (gw : T1)
    (Z_land : Int → Int → Int)
    (Zpow : Int → Int → Int)
    (avail : Int)
    (freed : Int)
    (Z_shiftr : Int → Int → Int)
    (Z_shiftl : Int → Int → Int)
    (h1 : (P + 16) ≤ (2 ^ (64 : Nat)))
    (h2 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ idx ∧ idx < 32))
    (h4 : (bv_unsigned gw) = G)
    (h5 : (Z_land mword 31) = last_idx)
    (h6 : (0 ≤ (Zpow 2 idx) ∧ (Zpow 2 idx) < (2 ^ (32 : Nat))))
    (h7 : (Z_land avail (Zpow 2 idx)) = 0)
    (h8 : (Z_land freed (Zpow 2 idx)) = 0)
    (h9 : (Z_shiftr (bv_unsigned (Z_to_bv 64 (Z_shiftl mword 52))) 58) = sc)
    (h10 : (Z_shiftr mword 12) = maplen)
    (h11 : (mword - (mword % 4096)) = (4096 * maplen)) :
    (((last_idx + (32 * freeable)) + (64 * sc)) + (maplen * 4096)) = (((last_idx + (32 * freeable)) + (64 * sc)) + (4096 * maplen)) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/CJ/Spec/SoftFloatProps.v (replace)
example
    (u : Int)
    (s : Int)
    (Zpow : Int → Int → Int)
    (h1 : (0 ≤ s ∧ s ≤ 31))
    (h2 : ((Zpow 2 s) ≤ u ∧ u < (Zpow 2 (s + 1))))
    (h3 : u < (2 ^ (32 : Nat)))
    (h4 : s ≠ 31)
    (h5 : (Zpow 2 (s + 1)) ≤ (2 ^ (31 : Nat))) :
    ((((2 ^ (32 : Nat)) - 1) * (2 ^ (32 : Nat))) + u) = (((2 ^ (64 : Nat)) - (2 ^ (32 : Nat))) + u) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/CJ/TUB/DtHeadB.v (replace)
example
    {T1 : Type}
    (FR : Int)
    (k : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Nat → Int → T1)
    (GSP : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 GSP)) = GSP)
    (h2 : FR = (64 * (FR / 64)))
    (h3 : (FR / 8) = (8 * (FR / 64)))
    (h4 : ((FR / 8) * 8) = FR)
    (h5 : GSP = (32 * (GSP / 32)))
    (h6 : (GSP / 8) = (4 * (GSP / 32)))
    (h7 : (((GSP + 8) / 8) = ((GSP / 8) + 1) ∧ ((GSP + 12) / 8) = ((GSP / 8) + 1)))
    (h8 : ((GSP / 8) ≤ (2 ^ (44 : Nat)) ∧ (2 ^ (41 : Nat)) ≤ (GSP / 8)))
    (h9 : (862280 ≤ (FR / 8) ∧ ((FR / 8) + 32) ≤ (GSP / 8)))
    (h10 : (0 ≤ (k / 8) ∧ (k / 8) ≤ 2)) :
    (((FR / 8) + 2147450880) + (((Int.toNat (4 + (k / 8))) : Nat) : Int)) = (((FR / 8) + (4 + (k / 8))) + 2147450880) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/CutCert/CutRtA.v (replace)
example
    {asan_layout asan_run env T4 T5 T6 T7 T8 : Type}
    (L : asan_layout)
    (ar : asan_run)
    (IMGHI : Int)
    (NF : Nat)
    (E0 : env)
    (sp0 : Int)
    (E2 : env)
    (k : Int)
    (a0v : Nat)
    (flv : Nat)
    (F : Int)
    (fl : Int)
    (kd : T4)
    (x : Int)
    (hl_img_lo : asan_layout → Int)
    (hl_img_hi : asan_layout → Int)
    (BIGSHADOW_LO : Int)
    (segs_below_b : T5 → Int → Bool)
    (hl_segs : asan_layout → T5)
    (FS_BYTES : Int)
    (ahl_ceil : asan_run → Int)
    (SCR : Int)
    (ar_sptop : asan_run → Int)
    (bv_unsigned : T6 → Int)
    (ev : env → Int → T6)
    (fst : T7 → Int)
    (snd : T7 → Int)
    (CL5A_uv : env → T8 → Int)
    (EVar : Nat → T8)
    (ar_fs : asan_run → Int)
    (ff_bytes : Int → Int)
    (ivl : Int → Int → T4 → T7)
    (h1 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ BIGSHADOW_LO))
    (h2 : (segs_below_b (hl_segs L) (hl_img_hi L)) = true)
    (h3 : (IMGHI ≤ (hl_img_hi L) ∧ (hl_img_lo L) < FS_BYTES))
    (h4 : ((sp0 % 16) = 0 ∧ ((((ahl_ceil ar) + 4096) + SCR) ≤ sp0 ∧ sp0 ≤ (ar_sptop ar))))
    (h5 : 0 ≤ SCR)
    (h6 : 32 ≤ NF)
    (h7 : (bv_unsigned (ev E0 2)) = sp0)
    (h8 : (CL5A_uv E2 (EVar a0v)) = F)
    (h9 : (CL5A_uv E2 (EVar flv)) = fl)
    (h10 : ((F + (ff_bytes k)) ≤ (hl_img_lo L) ∨ (hl_img_hi L) ≤ F))
    (h11 : ((ar_fs ar) ≤ fl ∧ fl < ((ar_fs ar) + FS_BYTES)))
    (h12 : ((F + (ff_bytes k)) ≤ fl ∨ (fl + 1) ≤ F))
    (h13 : ((fst (ivl F fl kd)) ≤ x ∧ x < ((fst (ivl F fl kd)) + (snd (ivl F fl kd))))) :
    (F + (x - F)) = x := by
  lia

-- jsoncons/fuzz_json_cursor: lib/CutGen/StrPushBackCB.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (sp : Int)
    (hl_img_lo : T1 → Int)
    (L : T1)
    (hl_img_hi : T1 → Int)
    (BIGSHADOW_LO : Int)
    (segs_below_b : T2 → Int → Bool)
    (hl_segs : T1 → T2)
    (ahl_ceil : T3 → Int)
    (ar : T3)
    (p : Int)
    (ar_fs : T3 → Int)
    (cap : Int)
    (k : Int)
    (o : Int)
    (ev : T4 → Int → T5)
    (E0 : T4)
    (c : Int)
    (bv_unsigned : T5 → Int)
    (FT_NF : Nat)
    (CH_hd_scr : T6 → Int)
    (F_HDECL : T6)
    (ar_sptop : T3 → Int)
    (asc_got_lo : T7 → Int)
    (C : T7)
    (FT_GLO : Int)
    (FT_GHI : Int)
    (asc_got_hi : T7 → Int)
    (h1 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ BIGSHADOW_LO))
    (h2 : (segs_below_b (hl_segs L) (hl_img_hi L)) = true)
    (h3 : ((hl_img_lo L) ≤ 65536 ∧ 7028736 ≤ (hl_img_hi L)))
    (h4 : (ahl_ceil ar) ≤ sp)
    (h5 : (hl_img_hi L) ≤ (ar_fs ar))
    (h6 : cap = (2 * k))
    (h7 : (cap % 2) = 0)
    (h8 : (bv_unsigned (ev E0 2)) = sp)
    (h9 : (bv_unsigned (ev E0 10)) = o)
    (h10 : (bv_unsigned (ev E0 11)) = c)
    (h11 : (bv_unsigned (ev E0 32)) = k)
    (h12 : (bv_unsigned (ev E0 34)) = p)
    (h13 : (CH_hd_scr F_HDECL) = 4368)
    (h14 : ((sp % 16) = 0 ∧ ((((ahl_ceil ar) + 4096) + (CH_hd_scr F_HDECL)) ≤ sp ∧ sp ≤ (ar_sptop ar))))
    (h15 : 0 ≤ (CH_hd_scr F_HDECL))
    (h16 : 32 ≤ FT_NF)
    (h17 : ((asc_got_lo C) ≤ FT_GLO ∧ (FT_GHI ≤ (asc_got_hi C) ∧ (0 ≤ FT_GLO ∧ FT_GHI ≤ (hl_img_hi L)))))
    (h18 : ((sp - 4368) % 8) = 0) :
    (((2 * (sp / 16)) - 546) * 8) = ((16 * (sp / 16)) - 4368) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/CutGen/VecPushCB.v (replace)
example
    {asan_layout asan_run T3 T4 T5 T6 : Type}
    (L : asan_layout)
    (ar : asan_run)
    (q : Int)
    (hl_img_lo : asan_layout → Int)
    (hl_img_hi : asan_layout → Int)
    (BIGSHADOW_LO : Int)
    (segs_below_b : T3 → Int → Bool)
    (hl_segs : asan_layout → T3)
    (b : Int)
    (ahl_ceil : asan_run → Int)
    (sp : Int)
    (shv : Int)
    (ev : T4 → Int → T5)
    (E0 : T4)
    (o : Int)
    (len : Int)
    (cap : Int)
    (she : Int)
    (xm : Int)
    (bv_unsigned : T5 → Int)
    (CH_hd_scr : T6 → Int)
    (G_HDECL : T6)
    (ar_sptop : asan_run → Int)
    (h1 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ BIGSHADOW_LO))
    (h2 : (segs_below_b (hl_segs L) (hl_img_hi L)) = true)
    (h3 : (hl_img_hi L) ≤ b)
    (h4 : (ahl_ceil ar) ≤ sp)
    (h5 : (0 ≤ shv ∧ shv ≤ 7))
    (h6 : (bv_unsigned (ev E0 2)) = sp)
    (h7 : (bv_unsigned (ev E0 10)) = o)
    (h8 : (bv_unsigned (ev E0 32)) = b)
    (h9 : (bv_unsigned (ev E0 33)) = len)
    (h10 : (bv_unsigned (ev E0 34)) = cap)
    (h11 : (bv_unsigned (ev E0 35)) = shv)
    (h12 : (bv_unsigned (ev E0 36)) = she)
    (h13 : (bv_unsigned (ev E0 37)) = xm)
    (h14 : (CH_hd_scr G_HDECL) = 8240)
    (h15 : ((sp % 16) = 0 ∧ ((((ahl_ceil ar) + 4096) + (CH_hd_scr G_HDECL)) ≤ sp ∧ sp ≤ (ar_sptop ar))))
    (h16 : 0 ≤ (CH_hd_scr G_HDECL))
    (h17 : ((sp - 80) % 8) = 0)
    (h18 : ((ar_sptop ar) / 8) = (2 * q)) :
    ((2 * q) * 8) = (q * 16) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/CutGen/VecPushSlowCA.v (replace)
example
    {asan_layout asan_run T3 T4 T5 T6 : Type}
    (L : asan_layout)
    (ar : asan_run)
    (sp : Int)
    (hl_img_lo : asan_layout → Int)
    (hl_img_hi : asan_layout → Int)
    (BIGSHADOW_LO : Int)
    (segs_below_b : T3 → Int → Bool)
    (hl_segs : asan_layout → T3)
    (b : Int)
    (ahl_ceil : asan_run → Int)
    (ar_fs : asan_run → Int)
    (shv : Int)
    (ev : T4 → Int → T5)
    (E0 : T4)
    (o : Int)
    (cap : Int)
    (xm : Int)
    (bv_unsigned : T5 → Int)
    (CH_hd_scr : T6 → Int)
    (G_HDECL : T6)
    (ar_sptop : asan_run → Int)
    (GT_NF : Nat)
    (h1 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ BIGSHADOW_LO))
    (h2 : (segs_below_b (hl_segs L) (hl_img_hi L)) = true)
    (h3 : ((hl_img_lo L) ≤ 65536 ∧ 7024640 ≤ (hl_img_hi L)))
    (h4 : (hl_img_hi L) ≤ b)
    (h5 : (ahl_ceil ar) ≤ sp)
    (h6 : (hl_img_hi L) ≤ (ar_fs ar))
    (h7 : (0 ≤ shv ∧ shv ≤ 7))
    (h8 : (bv_unsigned (ev E0 2)) = sp)
    (h9 : (bv_unsigned (ev E0 10)) = o)
    (h10 : (bv_unsigned (ev E0 32)) = b)
    (h11 : (bv_unsigned (ev E0 33)) = cap)
    (h12 : (bv_unsigned (ev E0 34)) = shv)
    (h13 : (bv_unsigned (ev E0 35)) = xm)
    (h14 : (CH_hd_scr G_HDECL) = 8192)
    (h15 : ((sp % 16) = 0 ∧ ((((ahl_ceil ar) + 4096) + (CH_hd_scr G_HDECL)) ≤ sp ∧ sp ≤ (ar_sptop ar))))
    (h16 : 0 ≤ (CH_hd_scr G_HDECL))
    (h17 : 32 ≤ GT_NF)
    (h18 : ((sp - 104) % 8) = 0) :
    (((2 * (sp / 16)) - 13) * 8) = ((16 * (sp / 16)) - 104) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/DecOkLazyA.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (SP : Int)
    (k : Int)
    (N_1 : Int)
    (hl_img_lo : T1 → Int)
    (L : T1)
    (ERRNO : Int)
    (hl_img_hi : T1 → Int)
    (GA : Int)
    (ev : T2 → Int → T3)
    (E0 : T2)
    (bv_unsigned : T3 → Int)
    (F : Int)
    (Q : Int)
    (CH_hd_scr : T4 → Int)
    (HD : T4)
    (ahl_ceil : T5 → Int)
    (ar : T5)
    (ar_sptop : T5 → Int)
    (NF : Nat)
    (h1 : 0 ≤ N_1)
    (h2 : ((hl_img_lo L) ≤ ERRNO ∧ (ERRNO + 4) ≤ (hl_img_hi L)))
    (h3 : ((hl_img_lo L) ≤ GA ∧ (GA + 8) ≤ (hl_img_hi L)))
    (h4 : (bv_unsigned (ev E0 2)) = SP)
    (h5 : (bv_unsigned (ev E0 21)) = F)
    (h6 : (bv_unsigned (ev E0 32)) = Q)
    (h7 : (bv_unsigned (ev E0 47)) = N_1)
    (h8 : (bv_unsigned (ev E0 4)) = (ERRNO + 164))
    (h9 : ((140735332483072 + 256) ≤ SP ∧ (SP + 8416) ≤ (2 ^ (47 : Nat))))
    (h10 : (140735332483072 ≤ F ∧ (F + 256) ≤ (2 ^ (47 : Nat))))
    (h11 : (4096 ≤ Q ∧ ((Q + N_1) < (2 ^ (47 : Nat)) ∧ N_1 < (2 ^ (26 : Nat)))))
    (h12 : (0 ≤ ERRNO ∧ (ERRNO + 4) ≤ 140735332483072))
    (h13 : (CH_hd_scr HD) = 256)
    (h14 : ((SP % 16) = 0 ∧ ((((ahl_ceil ar) + 4096) + (CH_hd_scr HD)) ≤ SP ∧ SP ≤ (ar_sptop ar))))
    (h15 : 0 ≤ (CH_hd_scr HD))
    (h16 : 32 ≤ NF) :
    (((SP + 8416) - 8672) + ((8672 - 8416) + k)) = (SP + k) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/DecOkLazyA.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (SP : Int)
    (k : Int)
    (N_1 : Int)
    (hl_img_lo : T1 → Int)
    (L : T1)
    (ERRNO : Int)
    (hl_img_hi : T1 → Int)
    (GA : Int)
    (ev : T2 → Int → T3)
    (E0 : T2)
    (bv_unsigned : T3 → Int)
    (F : Int)
    (Q : Int)
    (CH_hd_scr : T4 → Int)
    (HD : T4)
    (ahl_ceil : T5 → Int)
    (ar : T5)
    (ar_sptop : T5 → Int)
    (NF : Nat)
    (h1 : 0 ≤ N_1)
    (h2 : ((hl_img_lo L) ≤ ERRNO ∧ (ERRNO + 4) ≤ (hl_img_hi L)))
    (h3 : ((hl_img_lo L) ≤ GA ∧ (GA + 8) ≤ (hl_img_hi L)))
    (h4 : (bv_unsigned (ev E0 2)) = SP)
    (h5 : (bv_unsigned (ev E0 21)) = F)
    (h6 : (bv_unsigned (ev E0 32)) = Q)
    (h7 : (bv_unsigned (ev E0 47)) = N_1)
    (h8 : (bv_unsigned (ev E0 4)) = (ERRNO + 164))
    (h9 : ((140735332483072 + 256) ≤ SP ∧ (SP + 8416) ≤ (2 ^ (47 : Nat))))
    (h10 : (140735332483072 ≤ F ∧ (F + 256) ≤ (2 ^ (47 : Nat))))
    (h11 : (4096 ≤ Q ∧ ((Q + N_1) < (2 ^ (47 : Nat)) ∧ N_1 < (2 ^ (26 : Nat)))))
    (h12 : (0 ≤ ERRNO ∧ (ERRNO + 4) ≤ 140735332483072))
    (h13 : (CH_hd_scr HD) = 256)
    (h14 : ((SP % 16) = 0 ∧ ((((ahl_ceil ar) + 4096) + (CH_hd_scr HD)) ≤ SP ∧ SP ≤ (ar_sptop ar))))
    (h15 : 0 ≤ (CH_hd_scr HD))
    (h16 : 32 ≤ NF) :
    ((SP + 8416) + (k - 8416)) = (SP + k) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/DecOkSemA.v (replace)
example
    {env T2 T3 T4 T5 T6 T7 T8 : Type}
    (ERRNO : Int)
    (Q : Int)
    (F : Int)
    (SP : Int)
    (E0 : env)
    (i : T2)
    (c : T3)
    (ps : T4)
    (j : T2)
    (cj : T3)
    (s : T5)
    (E : env)
    (E' : env)
    (N_1 : Int)
    (k : Int)
    (bv_unsigned : T6 → Int)
    (ev : env → Int → T6)
    (PDC_STK_FLOOR : Int)
    (cut_chk : T2 → T3 → Bool)
    (CC_goto_chk : Nat → T3 → T4 → T3 → T5 → Bool)
    (NF : Nat)
    (goto_chk2 : T2 → T3 → T4 → T2 → T3 → T5 → Bool)
    (CC_cp_nx : T3 → Nat)
    (E2 : env)
    (uE : env → T7 → Int)
    (CC_slook : T5 → Int → T7)
    (EVar : Int → T7)
    (flag : T8 → T3 → env → Bool)
    (f' : T8)
    (reg_e : T3 → Int → T7)
    (CC_esubstL : Nat → T5 → T7 → T7)
    (h1 : (bv_unsigned (ev E0 2)) = SP)
    (h2 : (bv_unsigned (ev E0 21)) = F)
    (h3 : (bv_unsigned (ev E0 32)) = Q)
    (h4 : (bv_unsigned (ev E0 47)) = N_1)
    (h5 : ((PDC_STK_FLOOR + 256) ≤ SP ∧ (SP + 8416) ≤ (2 ^ (47 : Nat))))
    (h6 : (PDC_STK_FLOOR ≤ F ∧ (F + 256) ≤ (2 ^ (47 : Nat))))
    (h7 : (4096 ≤ Q ∧ ((Q + N_1) < (2 ^ (47 : Nat)) ∧ N_1 < (2 ^ (26 : Nat)))))
    (h8 : (0 ≤ ERRNO ∧ (ERRNO + 4) ≤ PDC_STK_FLOOR))
    (h9 : (bv_unsigned (ev E0 4)) = (ERRNO + 164))
    (h10 : (cut_chk i c) = true)
    (h11 : (cut_chk j cj) = true)
    (h12 : (CC_goto_chk NF c ps cj s) = true)
    (h13 : (goto_chk2 i c ps j cj s) = true)
    (h14 : NF ≤ (CC_cp_nx c))
    (h15 : 1 ≤ N_1)
    (h16 : (bv_unsigned (ev E2 48)) = (uE E' (CC_slook s 48)))
    (h17 : (uE E' (EVar 47)) = N_1)
    (h18 : (flag f' cj E2) = false)
    (h19 : (uE E2 (reg_e cj 20)) = (uE E' (CC_esubstL NF s (reg_e cj 20))))
    (h20 : (uE E' (EVar 48)) = (bv_unsigned (ev E 48)))
    (h21 : 1 ≤ k)
    (h22 : k = 0) :
    ((N_1 - k) + 1) = (N_1 - (k - 1)) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/DecOkSemA.v (replace)
example
    {env T2 T3 T4 T5 T6 T7 T8 : Type}
    (ERRNO : Int)
    (Q : Int)
    (F : Int)
    (SP : Int)
    (E0 : env)
    (i : T2)
    (c : T3)
    (ps : T4)
    (j : T2)
    (cj : T3)
    (s : T5)
    (E : env)
    (E' : env)
    (N_1 : Int)
    (k : Int)
    (D : Int)
    (bv_unsigned : T6 → Int)
    (ev : env → Int → T6)
    (PDC_STK_FLOOR : Int)
    (cut_chk : T2 → T3 → Bool)
    (CC_goto_chk : Nat → T3 → T4 → T3 → T5 → Bool)
    (NF : Nat)
    (goto_chk2 : T2 → T3 → T4 → T2 → T3 → T5 → Bool)
    (CC_cp_nx : T3 → Nat)
    (E2 : env)
    (uE : env → T7 → Int)
    (CC_slook : T5 → Int → T7)
    (EVar : Int → T7)
    (flag : T8 → T3 → env → Bool)
    (f' : T8)
    (reg_e : T3 → Int → T7)
    (CC_esubstL : Nat → T5 → T7 → T7)
    (GS4 : T8)
    (h1 : (bv_unsigned (ev E0 2)) = SP)
    (h2 : (bv_unsigned (ev E0 21)) = F)
    (h3 : (bv_unsigned (ev E0 32)) = Q)
    (h4 : (bv_unsigned (ev E0 47)) = N_1)
    (h5 : ((PDC_STK_FLOOR + 256) ≤ SP ∧ (SP + 8416) ≤ (2 ^ (47 : Nat))))
    (h6 : (PDC_STK_FLOOR ≤ F ∧ (F + 256) ≤ (2 ^ (47 : Nat))))
    (h7 : (4096 ≤ Q ∧ ((Q + N_1) < (2 ^ (47 : Nat)) ∧ N_1 < (2 ^ (26 : Nat)))))
    (h8 : (0 ≤ ERRNO ∧ (ERRNO + 4) ≤ PDC_STK_FLOOR))
    (h9 : (bv_unsigned (ev E0 4)) = (ERRNO + 164))
    (h10 : (cut_chk i c) = true)
    (h11 : (cut_chk j cj) = true)
    (h12 : (CC_goto_chk NF c ps cj s) = true)
    (h13 : (goto_chk2 i c ps j cj s) = true)
    (h14 : NF ≤ (CC_cp_nx c))
    (h15 : 1 ≤ N_1)
    (h16 : (bv_unsigned (ev E2 48)) = (uE E' (CC_slook s 48)))
    (h17 : (uE E' (EVar 47)) = N_1)
    (h18 : (flag f' cj E2) = false)
    (h19 : (uE E2 (reg_e cj 20)) = (uE E' (CC_esubstL NF s (reg_e cj 20))))
    (h20 : (uE E' (EVar 48)) = (bv_unsigned (ev E 48)))
    (h21 : 1 ≤ k)
    (h22 : k = 0)
    (h23 : (flag GS4 cj E2) = (flag GS4 c E))
    (h24 : D = (N_1 - k)) :
    ((((Q + N_1) + 1) - k) - 1) = (Q + D) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/DecOkSemA.v (replace)
example
    {env T2 T3 T4 T5 T6 T7 T8 : Type}
    (ERRNO : Int)
    (Q : Int)
    (F : Int)
    (SP : Int)
    (E0 : env)
    (i : T2)
    (c : T3)
    (ps : T4)
    (j : T2)
    (cj : T3)
    (s : T5)
    (E : env)
    (E' : env)
    (D : Int)
    (bv_unsigned : T6 → Int)
    (ev : env → Int → T6)
    (N_1 : Int)
    (PDC_STK_FLOOR : Int)
    (cut_chk : T2 → T3 → Bool)
    (CC_goto_chk : Nat → T3 → T4 → T3 → T5 → Bool)
    (NF : Nat)
    (goto_chk2 : T2 → T3 → T4 → T2 → T3 → T5 → Bool)
    (CC_cp_nx : T3 → Nat)
    (E2 : env)
    (uE : env → T7 → Int)
    (CC_slook : T5 → Int → T7)
    (EVar : Int → T7)
    (flag : T8 → T3 → env → Bool)
    (f' : T8)
    (reg_e : T3 → Int → T7)
    (CC_esubstL : Nat → T5 → T7 → T7)
    (k : Int)
    (GS4 : T8)
    (cell_dec : T3 → T4 → Bool)
    (h1 : (bv_unsigned (ev E0 2)) = SP)
    (h2 : (bv_unsigned (ev E0 21)) = F)
    (h3 : (bv_unsigned (ev E0 32)) = Q)
    (h4 : (bv_unsigned (ev E0 47)) = N_1)
    (h5 : ((PDC_STK_FLOOR + 256) ≤ SP ∧ (SP + 8416) ≤ (2 ^ (47 : Nat))))
    (h6 : (PDC_STK_FLOOR ≤ F ∧ (F + 256) ≤ (2 ^ (47 : Nat))))
    (h7 : (4096 ≤ Q ∧ ((Q + N_1) < (2 ^ (47 : Nat)) ∧ N_1 < (2 ^ (26 : Nat)))))
    (h8 : (0 ≤ ERRNO ∧ (ERRNO + 4) ≤ PDC_STK_FLOOR))
    (h9 : (bv_unsigned (ev E0 4)) = (ERRNO + 164))
    (h10 : (cut_chk i c) = true)
    (h11 : (cut_chk j cj) = true)
    (h12 : (CC_goto_chk NF c ps cj s) = true)
    (h13 : (goto_chk2 i c ps j cj s) = true)
    (h14 : NF ≤ (CC_cp_nx c))
    (h15 : 1 ≤ N_1)
    (h16 : (bv_unsigned (ev E2 48)) = (uE E' (CC_slook s 48)))
    (h17 : (uE E' (EVar 47)) = N_1)
    (h18 : (flag f' cj E2) = false)
    (h19 : (uE E2 (reg_e cj 20)) = (uE E' (CC_esubstL NF s (reg_e cj 20))))
    (h20 : (uE E' (EVar 48)) = (bv_unsigned (ev E 48)))
    (h21 : 1 ≤ k)
    (h22 : k = 0)
    (h23 : (flag GS4 cj E2) = (flag GS4 c E))
    (h24 : D = (N_1 - k))
    (h25 : (cell_dec c ps) = true) :
    (((Q + D) + 1) - 1) = (Q + D) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/DecOkSemM.v (replace)
example
    {T1 T2 : Type}
    (N_1 : Int)
    (k : Int)
    (bv_unsigned : T1 → Int)
    (ev : T2 → Int → T1)
    (E : T2)
    (Q : Int)
    (F : Int)
    (h1 : (bv_unsigned (ev E 32)) = Q)
    (h2 : (bv_unsigned (ev E 47)) = N_1)
    (h3 : (bv_unsigned (ev E 21)) = F)
    (h4 : (0 ≤ k ∧ k < (2 ^ (64 : Nat)))) :
    (((N_1 - k) + (2 ^ (64 : Nat))) + ((-1) * (2 ^ (64 : Nat)))) = (N_1 - k) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/DecfloatOk.v (replace)
example
    {T1 T2 : Type}
    (SP : Int)
    (d : Int)
    (N_1 : Int)
    (bv_unsigned : T1 → Int)
    (ev : T2 → Int → T1)
    (E0 : T2)
    (F : Int)
    (Q : Int)
    (PDC_STK_FLOOR : Int)
    (ERRNO : Int)
    (h1 : 0 ≤ N_1)
    (h2 : (bv_unsigned (ev E0 2)) = SP)
    (h3 : (bv_unsigned (ev E0 21)) = F)
    (h4 : (bv_unsigned (ev E0 32)) = Q)
    (h5 : (bv_unsigned (ev E0 47)) = N_1)
    (h6 : ((PDC_STK_FLOOR + 256) ≤ SP ∧ (SP + 8416) ≤ (2 ^ (47 : Nat))))
    (h7 : (PDC_STK_FLOOR ≤ F ∧ (F + 256) ≤ (2 ^ (47 : Nat))))
    (h8 : (4096 ≤ Q ∧ ((Q + N_1) < (2 ^ (47 : Nat)) ∧ N_1 < (2 ^ (26 : Nat)))))
    (h9 : (0 ≤ ERRNO ∧ (ERRNO + 4) ≤ PDC_STK_FLOOR)) :
    ((SP - 256) + (8560 + d)) = (((SP + 8416) - 112) + d) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/IslChainA.v (replace)
example
    {asan_layout cfg T3 T4 : Type}
    (L : asan_layout)
    (CF : cfg)
    (sp0 : Int)
    (SCR : Int)
    (tpv : Int)
    (scr_ms : Int)
    (spoff : Int)
    (scr : Int)
    (i : Int)
    (hl_img_lo : asan_layout → Int)
    (hl_img_hi : asan_layout → Int)
    (BIGSHADOW_LO : Int)
    (segs_below_b : T3 → Int → Bool)
    (hl_segs : asan_layout → T3)
    (bv_unsigned : T4 → Int)
    (E : Nat → T4)
    (c_spk : cfg → Nat)
    (hl_tp : asan_layout → Int)
    (hl_scr_mem : asan_layout → Int)
    (c_abs_hi : cfg → Int)
    (h1 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ BIGSHADOW_LO))
    (h2 : (segs_below_b (hl_segs L) (hl_img_hi L)) = true)
    (h3 : 0 ≤ SCR)
    (h4 : (SCR % 8) = 0)
    (h5 : (bv_unsigned (E (c_spk CF))) = sp0)
    (h6 : tpv = (hl_tp L))
    (h7 : (0 ≤ (hl_scr_mem L) ∧ (hl_scr_mem L) ≤ scr_ms))
    (h8 : (c_abs_hi CF) ≤ (hl_img_hi L))
    (h9 : 0 ≤ scr)
    (h10 : (spoff % 16) = 0)
    (h11 : spoff ≤ 0)
    (h12 : (-SCR) ≤ (spoff - scr)) :
    ((sp0 - SCR) + ((spoff + i) + SCR)) = ((sp0 + spoff) + i) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/IslChainA.v (replace)
example
    {asan_layout cfg T3 T4 : Type}
    (L : asan_layout)
    (CF : cfg)
    (sp0 : Int)
    (SCR : Int)
    (tpv : Int)
    (scr_ms : Int)
    (spoff : Int)
    (scr : Int)
    (i : Int)
    (hl_img_lo : asan_layout → Int)
    (hl_img_hi : asan_layout → Int)
    (BIGSHADOW_LO : Int)
    (segs_below_b : T3 → Int → Bool)
    (hl_segs : asan_layout → T3)
    (bv_unsigned : T4 → Int)
    (E : Nat → T4)
    (c_spk : cfg → Nat)
    (hl_tp : asan_layout → Int)
    (hl_scr_mem : asan_layout → Int)
    (c_abs_hi : cfg → Int)
    (h1 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ BIGSHADOW_LO))
    (h2 : (segs_below_b (hl_segs L) (hl_img_hi L)) = true)
    (h3 : 0 ≤ SCR)
    (h4 : (SCR % 8) = 0)
    (h5 : (bv_unsigned (E (c_spk CF))) = sp0)
    (h6 : tpv = (hl_tp L))
    (h7 : (0 ≤ (hl_scr_mem L) ∧ (hl_scr_mem L) ≤ scr_ms))
    (h8 : (c_abs_hi CF) ≤ (hl_img_hi L))
    (h9 : 0 ≤ scr)
    (h10 : (spoff % 16) = 0)
    (h11 : spoff ≤ 0)
    (h12 : (-SCR) ≤ (spoff - scr)) :
    (sp0 + (spoff + i)) = ((sp0 + spoff) + i) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/Pm10Usage_tail.v (replace)
example
    {word list_byte T3 T4 T5 : Type}
    (sp0 : word)
    (a0s : list_byte)
    (pp : word)
    (L : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (edenot : T3 → T4 → word)
    (ENV : T5 → T3)
    (vals : T5)
    (EVar : Int → T4)
    (h1 : (((length a0s) : Nat) : Int) = L)
    (h2 : (74 ≤ L ∧ L ≤ 131071))
    (h3 : (bv_unsigned sp0) ≤ (bv_unsigned pp))
    (h4 : (((bv_unsigned pp) + L) + 8) ≤ ((bv_unsigned sp0) + 4194304))
    (h5 : (((bv_unsigned pp) + L) + 8) ≤ 140737488355328)
    (h6 : (bv_unsigned (edenot (ENV vals) (EVar 112))) < (2 ^ (31 : Nat))) :
    ((bv_unsigned sp0) + (-560)) = ((bv_unsigned sp0) + (-560)) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/Pm8MemsetIcpt.v (replace)
example
    {word T2 T3 T4 : Type}
    (sp : word)
    (pd : Int)
    (n : Int)
    (s : Int)
    (kD : Int)
    (fD : Int)
    (lD : Int)
    (faD : Int)
    (laD : Int)
    (bv_unsigned : word → Int)
    (SB : Int)
    (store_ok : T2 → T3 → T4 → Nat → Bool)
    (ASEGS : T2)
    (mem0 : T3)
    (Z_to_bv : Nat → Int → T4)
    (h1 : (bv_unsigned sp) = s)
    (h2 : fD = (SB + (pd / 8)))
    (h3 : lD = (SB + (((pd + n) - 1) / 8)))
    (h4 : faD = (fD - (fD % 8)))
    (h5 : laD = (lD - (lD % 8)))
    (h6 : (0 ≤ n ∧ n ≤ (2 ^ (40 : Nat))))
    (h7 : (16777216 ≤ (s - 2216) ∧ s < (2 ^ (64 : Nat))))
    (h8 : (lD + 8) ≤ (s - 2216))
    (h9 : (0 < n → ((pd + n) ≤ (s - 2216) ∨ s ≤ pd)))
    (h10 : (store_ok ASEGS mem0 (Z_to_bv 64 pd) (Int.toNat n)) = true)
    (h11 : (kD = 0 ∨ ((((pd + n) - 1) % 8) < kD ∧ kD ≤ 7))) :
    (s - 2216) = ((s - 2144) - 72) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/Pm9ArtClsPop1.v (replace)
example (a : Int) (b : Int) (c : Int) :
    (((a + (b * (2 ^ (20 : Nat)))) + c) * 4096) = (((4096 * a) + (b * (2 ^ (32 : Nat)))) + (4096 * c)) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/Pm9ArtRecycle5D.v (replace)
example
    {T1 : Type}
    (sp : Int)
    (b : Int)
    (spb : Int)
    (wb : Int)
    (items : T1)
    (i : Nat)
    (length : T1 → Nat)
    (h1 : b = ((spb + (24 * (2 ^ (32 : Nat)))) + (16 * wb)))
    (h2 : (0 ≤ wb ∧ ((16 * wb) + 8192) ≤ 3758096384))
    (h3 : i < (length items)) :
    (sp - 104) = ((sp - 112) + 8) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/Pm9IslandA.v (replace)
example
    {asan_layout asan_run T3 T4 : Type}
    (L : asan_layout)
    (ar : asan_run)
    (sp : Int)
    (off : Int)
    (hl_img_lo : asan_layout → Int)
    (hl_img_hi : asan_layout → Int)
    (BIGSHADOW_LO : Int)
    (segs_below_b : T3 → Int → Bool)
    (hl_segs : asan_layout → T3)
    (ahl_ceil : asan_run → Int)
    (ABS_HI : Int)
    (o : Int)
    (bv_unsigned : T4 → Int)
    (E : Nat → T4)
    (h1 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ BIGSHADOW_LO))
    (h2 : (segs_below_b (hl_segs L) (hl_img_hi L)) = true)
    (h3 : (ahl_ceil ar) ≤ sp)
    (h4 : ABS_HI ≤ o)
    (h5 : (bv_unsigned (E 2)) = sp)
    (h6 : (bv_unsigned (E 10)) = o) :
    ((sp - 10240) + (off + 10240)) = (sp + off) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmParse/ParseBridges.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (cap' : Int)
    (CH2_ci_nx : T1 → Int)
    (ci : T1)
    (nx : Int)
    (E2 : T2)
    (bv_unsigned : T3 → Int)
    (ev : T2 → Int → T3)
    (p' : Int)
    (uv : T2 → T4 → Int)
    (PSU_emul2 : T5 → T4)
    (EVar : Int → T5)
    (APC_eaddz : T6 → Int → T4)
    (se : T6)
    (size : Int)
    (h1 : (CH2_ci_nx ci) = nx)
    (h2 : (bv_unsigned (ev E2 nx)) = p')
    (h3 : (0 ≤ (cap' / 2) ∧ (cap' / 2) < (2 ^ (64 : Nat))))
    (h4 : (bv_unsigned (ev E2 (nx + 1))) = (cap' / 2))
    (h5 : cap' = (2 * (cap' / 2)))
    (h6 : (uv E2 (PSU_emul2 (EVar (nx + 1)))) = cap')
    (h7 : (4096 ≤ p' ∧ p' ≤ (2 ^ (47 : Nat))))
    (h8 : (uv E2 (APC_eaddz se 1)) = (size + 1)) :
    ((4 * (cap' / 8)) * 2) = ((8 * (cap' / 8)) + 0) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmParse/ParseBridges.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (wseg : Int)
    (q : Int)
    (i0 : Int)
    (estart : T1 → T2 → Int)
    (E' : T1)
    (SA : T3 → T4 → T2)
    (OB : T3)
    (OK : T4)
    (oaddr : Int)
    (n : Int)
    (uv : T1 → T5 → Int)
    (WSEG : T5)
    (WLEN : T5)
    (wlen : Int)
    (size : Int)
    (h1 : (estart E' (SA OB OK)) = oaddr)
    (h2 : (uv E' WSEG) = wseg)
    (h3 : (uv E' WLEN) = wlen)
    (h4 : 0 ≤ wlen)
    (h5 : (4096 ≤ wseg ∧ (wseg + wlen) ≤ (2 ^ (47 : Nat))))
    (h6 : (size + n) ≤ ((2 ^ (26 : Nat)) - 1)) :
    (wseg + ((q - wseg) + i0)) = (q + i0) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmParse/ParseBridges4.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (cap' : Int)
    (CH2_ci_nx : T1 → Int)
    (ci : T1)
    (nx : Int)
    (uv : T2 → T3 → Int)
    (E2 : T2)
    (bv_unsigned : T4 → Int)
    (ev : T2 → Int → T4)
    (p' : Int)
    (PSU_emul2 : T5 → T3)
    (EVar : Int → T5)
    (APC_eaddz : T6 → Int → T3)
    (se : T6)
    (size : Int)
    (h1 : (CH2_ci_nx ci) = nx)
    (h2 : (bv_unsigned (ev E2 nx)) = p')
    (h3 : (0 ≤ (cap' / 2) ∧ (cap' / 2) < (2 ^ (64 : Nat))))
    (h4 : (bv_unsigned (ev E2 (nx + 1))) = (cap' / 2))
    (h5 : cap' = (2 * (cap' / 2)))
    (h6 : (uv E2 (PSU_emul2 (EVar (nx + 1)))) = cap')
    (h7 : (4096 ≤ p' ∧ p' ≤ (2 ^ (47 : Nat))))
    (h8 : (uv E2 (APC_eaddz se 1)) = (size + 1)) :
    ((4 * (cap' / 8)) * 2) = ((8 * (cap' / 8)) + 0) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmParse/ParseBridges6.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (cap' : Nat)
    (CH2_ci_nx : T1 → Nat)
    (ci : T1)
    (nx : Nat)
    (uv : T2 → T3 → Nat)
    (E2 : T2)
    (bv_unsigned : T4 → Nat)
    (ev : T2 → Nat → T4)
    (p' : Nat)
    (PSU_emul2 : T5 → T3)
    (EVar : Nat → T5)
    (APC_eaddz : T6 → Nat → T3)
    (se : T6)
    (size : Nat)
    (h1 : (CH2_ci_nx ci) = nx)
    (h2 : (bv_unsigned (ev E2 nx)) = p')
    (h3 : (0 ≤ (cap' / 2) ∧ (cap' / 2) < (2 ^ 64)))
    (h4 : (bv_unsigned (ev E2 (nx + 1))) = (cap' / 2))
    (h5 : cap' = (2 * (cap' / 2)))
    (h6 : (uv E2 (PSU_emul2 (EVar (nx + 1)))) = cap')
    (h7 : (4096 ≤ p' ∧ p' ≤ (2 ^ 47)))
    (h8 : (uv E2 (APC_eaddz se 1)) = (size + 1)) :
    ((4 * (cap' / 8)) * 2) = ((8 * (cap' / 8)) + 0) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmSmall/SmallAt.v (replace)
example
    {PSK_consts expr env T4 T5 : Type}
    (C : PSK_consts)
    (Pe : expr)
    (Ve : expr)
    (Ee : expr)
    (spe : expr)
    (E : env)
    (Pv : Int)
    (Ev : Int)
    (Vv : Int)
    (spv : Int)
    (PSK_c_scr : PSK_consts → Int)
    (uv : env → expr → Int)
    (elenZ : env → T4 → Int)
    (ELit : Int → T4)
    (estart : env → T5 → Int)
    (SA : expr → Int → T5)
    (h1 : (0 ≤ (PSK_c_scr C) ∧ (PSK_c_scr C) ≤ (2 ^ (20 : Nat))))
    (h2 : (uv E Pe) = Pv)
    (h3 : (uv E Ee) = Ev)
    (h4 : (uv E Ve) = Vv)
    (h5 : (uv E spe) = spv)
    (h6 : ((2 ^ (40 : Nat)) ≤ Pv ∧ (Pv + 272) ≤ (2 ^ (47 : Nat))))
    (h7 : ((2 ^ (40 : Nat)) ≤ Ev ∧ (Ev + 16) ≤ (2 ^ (47 : Nat))))
    (h8 : ((2 ^ (40 : Nat)) ≤ Vv ∧ (Vv + 48) ≤ (2 ^ (47 : Nat))))
    (h9 : ((2 ^ (40 : Nat)) ≤ (spv - (PSK_c_scr C)) ∧ spv ≤ (2 ^ (47 : Nat))))
    (h10 : (Pv % 8) = 0)
    (h11 : (spv % 16) = 0)
    (h12 : (spv ≤ Pv ∧ (spv ≤ Ev ∧ spv ≤ Vv)))
    (h13 : (((Pv + 272) ≤ Ev ∨ (Ev + 16) ≤ Pv) ∧ (((Pv + 272) ≤ Vv ∨ (Vv + 48) ≤ Pv) ∧ ((Ev + 16) ≤ Vv ∨ (Vv + 48) ≤ Ev))))
    (h14 : (elenZ E (ELit (PSK_c_scr C))) = (PSK_c_scr C))
    (h15 : (estart E (SA spe (-(PSK_c_scr C)))) = (spv - (PSK_c_scr C))) :
    Vv = (Vv + 0) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmSmall/SmallPt.v (replace)
example
    {list_Z : Type}
    (xv : list_Z)
    (k : Nat)
    (z : Int)
    (NF : Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (49 + k) < NF)
    (h2 : (nth k xv 0) = z)
    (h3 : (0 ≤ z ∧ z < (2 ^ (64 : Nat)))) :
    k = ((17 + k) - 17) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmTU/TuWd.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (a : Int)
    (sp : Int)
    (r : Int)
    (bv_unsigned : T1 → Int)
    (ev : T2 → Int → T1)
    (EW : T3 → T4 → T2)
    (R1 : T3)
    (gh : T4)
    (o : Int)
    (h1 : (0 ≤ r ∧ r < (2 ^ (64 : Nat))))
    (h2 : (bv_unsigned (ev (EW R1 gh) 2)) = (sp - 400))
    (h3 : (bv_unsigned (ev (EW R1 gh) 8)) = o)
    (h4 : (bv_unsigned (ev (EW R1 gh) 33)) = r) :
    a = ((sp - 9600) + (a - (sp - 9600))) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmTU/TuWdCert.v (replace)
example
    {T1 T2 T3 T4 T5 T6 reg : Type}
    (o : Int)
    (j : Int)
    (hl_ceil : T1 → Int)
    (L : T1)
    (hl_img_lo : T1 → Int)
    (hl_img_hi : T1 → Int)
    (hl_errno : T1 → Int)
    (CH_hd_scr : T2 → Int)
    (U_HDECL : T2)
    (sp : Int)
    (hl_sptop : T1 → Int)
    (UT_NF : Nat)
    (bv_unsigned : T3 → Int)
    (edenot : T4 → T5 → T3)
    (E1' : T4)
    (CA_ps_reg : T6 → Int → T5)
    (ps : T6)
    (ridx : reg → Nat)
    (y : reg)
    (h1 : 140735332483072 ≤ (hl_ceil L))
    (h2 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ 140735332483072))
    (h3 : ((hl_img_lo L) ≤ (hl_errno L) ∧ ((hl_errno L) + 4) ≤ (hl_img_hi L)))
    (h4 : (CH_hd_scr U_HDECL) = 9200)
    (h5 : ((sp % 16) = 0 ∧ ((((hl_sptop L) - 8388608) + (CH_hd_scr U_HDECL)) ≤ sp ∧ (sp ≤ (hl_sptop L) ∧ (140735340871680 ≤ (hl_sptop L) ∧ (hl_sptop L) ≤ (2 ^ (47 : Nat)))))))
    (h6 : 0 ≤ (CH_hd_scr U_HDECL))
    (h7 : 32 ≤ UT_NF)
    (h8 : (bv_unsigned (edenot E1' (CA_ps_reg ps 10))) = 48)
    (h9 : (ridx y) < UT_NF) :
    (o + (1 + j)) = ((o + 1) + j) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmTop/CCtorTail.v (replace)
example
    {T1 T2 T3 : Type}
    (sp : Int)
    (SCR : Int)
    (PMCS_RN_SCR : T1 → Int)
    (STRTOD_SCR : T1)
    (bv_unsigned : T2 → Int)
    (getr : T3 → Int → T2)
    (R0 : T3)
    (h1 : (SCR = (400 + (PMCS_RN_SCR STRTOD_SCR)) ∧ 9520 ≤ (PMCS_RN_SCR STRTOD_SCR)))
    (h2 : (0 ≤ (bv_unsigned (getr R0 22)) ∧ (bv_unsigned (getr R0 22)) < (2 ^ (64 : Nat)))) :
    ((sp - 384) + 8) = (sp - 376) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmTop/SbufCtorStretch.v (replace)
example
    {T1 T2 T3 : Type}
    (SB : Int)
    (j : Int)
    (i : Int)
    (rav : Int)
    (E' : T1)
    (estart : T1 → T2 → Int)
    (SA : T3 → Int → T2)
    (EVar : Int → T3)
    (h1 : (0 ≤ rav ∧ rav < (2 ^ (64 : Nat))))
    (h2 : (estart E' (SA (EVar 40) 40)) = (SB + 40))
    (h3 : (estart E' (SA (EVar 40) 16)) = (SB + 16)) :
    ((SB + 16) + ((8 * j) + i)) = (((SB + 16) + (8 * j)) + i) := by
  lia

-- jsoncons/fuzz_json_cursor: lib/PmTop/VisitD.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (V : Int)
    (Z_to_bv : Int → Int → T1)
    (RSEGS : T2)
    (M' : T3)
    (store_ok : T2 → T3 → T1 → Int → Bool)
    (estart : T4 → T5 → Int)
    (E' : T4)
    (SA : T6 → Int → T5)
    (EVar : Int → T6)
    (elenZ : T4 → T7 → Int)
    (ELit : Int → T7)
    (h1 : (store_ok RSEGS M' (Z_to_bv 64 (V + 32)) 8) = true)
    (h2 : (estart E' (SA (EVar 42) 8)) = (V + 8))
    (h3 : (elenZ E' (ELit 40)) = 40) :
    (V + 32) = ((V + 8) + 24) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/BigFactsDiv.v (assert)
example
    (q : Int)
    (c2 : Int)
    (W_divu : Int → Int → Int)
    (A : Int)
    (dHi : Int)
    (qHi : Int)
    (m : Int)
    (W_M : Int)
    (l : Int)
    (c : Int)
    (W_mul : Int → Int → Int)
    (dLo : Int)
    (sl : Int)
    (sh : Int)
    (H : Int)
    (d : Int)
    (B : Int)
    (A1 : Int)
    (x : Int)
    (T : Int)
    (MH : Int)
    (K : Int)
    (h1 : (W_divu A (dHi + 1)) = (Int.fdiv A (dHi + 1)))
    (h2 : (qHi * (dHi + 1)) ≤ A)
    (h3 : A < ((dHi + 1) * (qHi + 1)))
    (h4 : 0 ≤ qHi)
    (h5 : qHi < (2 ^ (33 : Nat)))
    (h6 : (0 ≤ m ∧ m < (2 * W_M)))
    (h7 : (0 ≤ l ∧ l < (2 * W_M)))
    (h8 : (0 ≤ c ∧ c ≤ 1))
    (h9 : (0 ≤ c2 ∧ c2 ≤ 1))
    (h10 : (W_mul qHi dLo) = (m - (c * W_M)))
    (h11 : (W_mul qHi dHi) = (l - (c2 * W_M)))
    (h12 : 0 ≤ sh)
    (h13 : ((sh * W_M) + sl) = ((((m * H) + (l * W_M)) - (c * (W_M * H))) - (c2 * (W_M * W_M))))
    (h14 : (qHi * (d * H)) = ((l * W_M) + (m * H)))
    (h15 : 0 ≤ (((A * W_M) + B) - (qHi * (d * H))))
    (h16 : (((A * W_M) + B) - (qHi * (d * H))) < (W_M * ((qHi + dHi) + 1)))
    (h17 : (W_M * ((qHi + dHi) + 1)) ≤ (W_M * (2 ^ (34 : Nat))))
    (h18 : ((W_M * (2 ^ (34 : Nat))) + (W_M * H)) ≤ (W_M * W_M))
    (h19 : ((A1 * W_M) + x) = (((((A * W_M) + B) - (qHi * (d * H))) + (c * (W_M * H))) + ((q + c2) * (W_M * W_M))))
    (h20 : 0 ≤ (W_M * H))
    (h21 : (q + c2) = 0)
    (h22 : (0 ≤ (T + (c * MH)) ∧ (T + (c * MH)) < K)) :
    ((q + c2) = 0 ∨ (1 ≤ (q + c2) ∨ (q + c2) ≤ (-1))) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/CJ/TUX/WdHeadX.v (replace)
example (SP : Int) (h1 : (((2 ^ (41 : Nat)) + 9344) ≤ SP ∧ SP ≤ (2 ^ (47 : Nat)))) :
    (SP + (-118)) = (((SP + (-144)) + ((4 : Nat) : Int)) + ((22 : Nat) : Int)) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/CJIX/IcptHapp.v (replace)
example (p : Int) (n : Int) (h1 : (p / 8) ≤ (((p + n) - 1) / 8)) :
    n = ((p + n) - p) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/CJIXB/IcptQcW.v (assert)
example (D : Int) (c : Int) (h1 : (1 ≤ c ∧ c ≤ 64)) (h2 : (0 ≤ D ∧ (D + c) ≤ (2 ^ (47 : Nat)))) :
    (0 ≤ D ∧ D < (2 ^ (61 : Nat))) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/CJMX/IcptMemsetZ.v (assert)
example
    (K : Int)
    (q : Int)
    (D : Int)
    (N_1 : Int)
    (h1 : 2216 ≤ K)
    (h2 : ((17594333495296 + K) ≤ q ∧ q ≤ 140737488355072))
    (h3 : (0 ≤ D ∧ D < (2 ^ (64 : Nat))))
    (h4 : (0 ≤ N_1 ∧ N_1 ≤ (2 ^ (40 : Nat))))
    (h5 : (0 < N_1 → ((D + N_1) ≤ (q - K) ∨ q ≤ D))) :
    (((Int.toNat N_1) : Nat) : Int) = N_1 := by
  lia

-- jsoncons/fuzz_json_encoder: lib/CutGenW/SmallPtXBW.v (lemma)
example {list_Z : Type} (w : list_Z) (length : list_Z → Nat) :
    (Int.toNat ((((length w) : Nat) : Int) - (((length w) : Nat) : Int))) = 0 := by
  lia

-- jsoncons/fuzz_json_encoder: lib/FCutCert/CutOpsD.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (nx0 : T1)
    (BR : T2)
    (F : T3)
    (a : T4)
    (E : T5)
    (estart : T5 → T4 → Int)
    (j : Nat)
    (SA : T6 → T7 → T4)
    (kb : T6)
    (kk : T7)
    (forallb : T8 → T3 → Bool)
    (SGP_region_vars_lt : T1 → T8)
    (SGP_bfacts_vars_lt : T2 → T1 → Bool)
    (h1 : (forallb (SGP_region_vars_lt nx0) F) = true)
    (h2 : (SGP_bfacts_vars_lt BR nx0) = true) :
    ((estart E a) + ((j : Nat) : Int)) = ((estart E (SA kb kk)) + (((estart E a) - (estart E (SA kb kk))) + ((j : Nat) : Int))) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/HandoffBInvK.v (assert)
example
    {list_Segment atable acs list___Z_Z list_amap T6 T7 T8 T9 : Type}
    (SEGS : list_Segment)
    (A : atable)
    (LIMIT : Int)
    (cs : acs)
    (BUDGET : Int)
    (LENMAX : Int)
    (KMAX : Int)
    (EXTRA : list___Z_Z)
    (img_hi : atable → Int)
    (SHB_LO : Int)
    (no_fog : list_amap → Bool)
    (a_maps : acs → list_amap)
    (hops_in_maps : list_amap → T6 → Bool)
    (a_hna : acs → T6)
    (a_hlz : acs → T6)
    (forallb : T7 → T8 → Bool)
    (vis_sh_wr : atable → T9 → T7)
    (kn : acs → T9)
    (a_vis : acs → T8)
    (a_eager : acs → Int)
    (a_abytes : acs → Int)
    (A_bytes : list___Z_Z → Int)
    (AsanCeil_bottomup_floor : Int)
    (a_totsz : acs → Int)
    (length : list_amap → Nat)
    (segments_reserved : list_Segment → list_amap)
    (AsanCeil_alloc_ceiling : Int)
    (h1 : (img_hi A) ≤ SHB_LO)
    (h2 : (no_fog (a_maps cs)) = true)
    (h3 : (hops_in_maps (a_maps cs) (a_hna cs)) = true)
    (h4 : (hops_in_maps (a_maps cs) (a_hlz cs)) = true)
    (h5 : (forallb (vis_sh_wr A (kn cs)) (a_vis cs)) = true)
    (h6 : (0 ≤ BUDGET ∧ (0 ≤ KMAX ∧ (0 ≤ LENMAX ∧ LENMAX < (2 ^ (62 : Nat))))))
    (h7 : ((((a_eager cs) + (a_abytes cs)) + (A_bytes EXTRA)) + BUDGET) ≤ LIMIT)
    (h8 : (((AsanCeil_bottomup_floor + LENMAX) + ((a_totsz cs) + BUDGET)) + ((((((length (segments_reserved SEGS)) + (length (a_maps cs))) : Nat) : Int) + KMAX) * (LENMAX + 4095))) ≤ AsanCeil_alloc_ceiling) :
    0 ≤ (LENMAX + 4095) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/Pm5ArtAllocA16.v (replace)
example
    (sp : Int)
    (ia : Int)
    (n : Int)
    (r : Int)
    (rs : Int)
    (rz : Int)
    (t : Int)
    (q16 : Int)
    (Zpow : Int → Int → Int)
    (h1 : 16 ≤ sp)
    (h2 : sp < (2 ^ (64 : Nat)))
    (h3 : 4096 ≤ ia)
    (h4 : (ia + 4096) ≤ 7094272)
    (h5 : (7094272 + 16) ≤ sp)
    (h6 : (1 ≤ n ∧ n < (2 ^ (40 : Nat))))
    (h7 : (0 ≤ r ∧ r ≤ 7))
    (h8 : rs = ((((max n 8) + 15) / 16) * 16))
    (h9 : rz = (16 * (Zpow 2 r)))
    (h10 : ((rs + rz) + 16) ≤ 65536)
    (h11 : 1 ≤ t)
    (h12 : ((rs + 16) % 8) = 0) :
    (((2 * q16) + 2) * 8) = ((16 * q16) + 16) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/Pm5ArtFree1.v (replace)
example
    (a : Int)
    (x0 : Int)
    (x1 : Int)
    (x2 : Int)
    (w : Int)
    (h1 : 0 ≤ a)
    (h2 : (a + 4) < (2 ^ (64 : Nat)))
    (h3 : (0 ≤ x0 ∧ x0 < 256))
    (h4 : (0 ≤ x1 ∧ x1 < 256))
    (h5 : (0 ≤ x2 ∧ x2 < 65536))
    (h6 : (w % 256) = (x0 % 256)) :
    (x0 + ((x1 + (256 * x2)) * 256)) = ((x0 + (256 * x1)) + (65536 * x2)) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/Pm5ArtFree1.v (replace)
example
    (m : Int)
    (b1 : Int)
    (h1 : 16 ≤ m)
    (h2 : (m + 16) < (2 ^ (47 : Nat)))
    (h3 : (m % 16) = 0)
    (h4 : (0 ≤ b1 ∧ b1 < 256))
    (h5 : (m % 4) = 0) :
    (2 + (b1 * 256)) = (2 + (256 * b1)) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmEnc/EncBeginScalar.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (V : Int)
    (hl_ceil : T1 → Int)
    (L : T1)
    (b : Int)
    (ev : T2 → Int → T3)
    (E0 : T2)
    (sp : Int)
    (S2 : Int)
    (bv_unsigned : T3 → Int)
    (CH_hd_scr : T4 → Int)
    (G_HDECL : T4)
    (hl_sptop : T1 → Int)
    (GT_NF : Nat)
    (h1 : 140735332483072 ≤ (hl_ceil L))
    (h2 : (0 ≤ b ∧ b < (2 ^ (64 : Nat))))
    (h3 : (bv_unsigned (ev E0 2)) = sp)
    (h4 : (bv_unsigned (ev E0 10)) = V)
    (h5 : (bv_unsigned (ev E0 32)) = S2)
    (h6 : (bv_unsigned (ev E0 34)) = b)
    (h7 : (CH_hd_scr G_HDECL) = 8592)
    (h8 : ((sp % 16) = 0 ∧ (((hl_ceil L) + (CH_hd_scr G_HDECL)) ≤ sp ∧ (sp ≤ (hl_sptop L) ∧ (140735340871680 ≤ (hl_sptop L) ∧ (hl_sptop L) ≤ (2 ^ (47 : Nat)))))))
    (h9 : (((hl_ceil L) + 8592) ≤ sp ∧ (sp ≤ (hl_sptop L) ∧ (140735340871680 ≤ (hl_sptop L) ∧ (hl_sptop L) ≤ (2 ^ (47 : Nat))))))
    (h10 : 0 ≤ (CH_hd_scr G_HDECL))
    (h11 : 32 ≤ GT_NF) :
    ((V + 264) + 8) = (V + 272) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmEnc/EncKit3.v (replace)
example {T1 : Type} (length : T1 → Nat) (r : T1) :
    1 = (((((length r) + 1) + 1) - 1) - (length r)) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmEncA/EncKitXB.v (replace)
example
    (cap : Int)
    (n : Int)
    (m : Int)
    (h1 : 8 ≤ cap)
    (h2 : (cap % 8) = 0)
    (h3 : 0 ≤ n)
    (h4 : (((2 * cap) - 2) ≤ m ∧ n ≤ m))
    (h5 : (((2 * cap) - 2) / 8) ≤ (m / 8))
    (h6 : (((2 * cap) - 2) / 8) = ((cap / 4) - 1))
    (h7 : (4 * (cap / 4)) = cap) :
    (0 + (((m / 8) + 1) * 8)) = (((8 * (m / 8)) + 7) + 1) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmFloatX/VbhArrInobjX.v (replace)
example
    {heap_layout T2 T3 T4 T5 : Type}
    (L : heap_layout)
    (sp : Int)
    (j : Int)
    (d : Int)
    (hl_ceil : heap_layout → Int)
    (capb : Int)
    (b : Int)
    (depth : T2 → Int)
    (r0 : T2)
    (V : Int)
    (r : Int)
    (ev : T3 → Int → T4)
    (E0 : T3)
    (S2 : Int)
    (bv_unsigned : T4 → Int)
    (hl_img_lo : heap_layout → Int)
    (hl_img_hi : heap_layout → Int)
    (hl_errno : heap_layout → Int)
    (CH_hd_scr : T5 → Int)
    (G_HDECL : T5)
    (hl_sptop : heap_layout → Int)
    (GT_NF : Nat)
    (hl_stack : heap_layout → Int)
    (CH_hd_hstk : T5 → Int)
    (h1 : 1 ≤ d)
    (h2 : 0 ≤ d)
    (h3 : 140735332483072 ≤ (hl_ceil L))
    (h4 : (32 ≤ capb ∧ capb ≤ 32768))
    (h5 : capb ≠ 0)
    (h6 : (depth r0) = (d - 1))
    (h7 : (0 ≤ r ∧ r < (2 ^ (64 : Nat))))
    (h8 : (bv_unsigned (ev E0 1)) = r)
    (h9 : (bv_unsigned (ev E0 2)) = sp)
    (h10 : (bv_unsigned (ev E0 10)) = V)
    (h11 : (bv_unsigned (ev E0 32)) = S2)
    (h12 : (bv_unsigned (ev E0 33)) = d)
    (h13 : (bv_unsigned (ev E0 34)) = b)
    (h14 : (bv_unsigned (ev E0 35)) = capb)
    (h15 : (0 ≤ (hl_img_lo L) ∧ (hl_img_hi L) ≤ 140735332483072))
    (h16 : ((hl_img_lo L) ≤ (hl_errno L) ∧ ((hl_errno L) + 4) ≤ (hl_img_hi L)))
    (h17 : ((sp % 16) = 0 ∧ (((hl_ceil L) + (CH_hd_scr G_HDECL)) ≤ sp ∧ (sp ≤ (hl_sptop L) ∧ (140735340871680 ≤ (hl_sptop L) ∧ (hl_sptop L) ≤ (2 ^ (47 : Nat)))))))
    (h18 : 0 ≤ (CH_hd_scr G_HDECL))
    (h19 : 32 ≤ GT_NF)
    (h20 : (hl_stack L) = (CH_hd_hstk G_HDECL))
    (h21 : 0 ≤ (hl_stack L)) :
    ((sp - 10624) + (j + 1952)) = ((sp - 8672) + j) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmGrow/MallocXCps.v (replace)
example
    {T1 T2 : Type}
    (sp : Int)
    (PML_HEAP_STACK : Int)
    (i : Int)
    (bv_unsigned : T1 → Int)
    (getr : T2 → Int → T1)
    (R : T2)
    (h1 : PML_HEAP_STACK = 8224)
    (h2 : (bv_unsigned (getr R 2)) = sp) :
    ((sp - PML_HEAP_STACK) + i) = ((sp - PML_HEAP_STACK) + i) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmSmall/SmallAt.v (replace)
example
    {PSK_consts expr env T4 T5 : Type}
    (C : PSK_consts)
    (Pe : expr)
    (Ve : expr)
    (Ee : expr)
    (spe : expr)
    (E : env)
    (Pv : Int)
    (Ev : Int)
    (Vv : Int)
    (spv : Int)
    (PSK_c_scr : PSK_consts → Int)
    (uv : env → expr → Int)
    (elenZ : env → T4 → Int)
    (ELit : Int → T4)
    (estart : env → T5 → Int)
    (SA : expr → Int → T5)
    (h1 : (0 ≤ (PSK_c_scr C) ∧ (PSK_c_scr C) ≤ (2 ^ (20 : Nat))))
    (h2 : (uv E Pe) = Pv)
    (h3 : (uv E Ee) = Ev)
    (h4 : (uv E Ve) = Vv)
    (h5 : (uv E spe) = spv)
    (h6 : ((2 ^ (40 : Nat)) ≤ Pv ∧ (Pv + 272) ≤ (2 ^ (47 : Nat))))
    (h7 : ((2 ^ (40 : Nat)) ≤ Ev ∧ (Ev + 16) ≤ (2 ^ (47 : Nat))))
    (h8 : ((2 ^ (40 : Nat)) ≤ Vv ∧ (Vv + 8) ≤ (2 ^ (47 : Nat))))
    (h9 : ((2 ^ (40 : Nat)) ≤ (spv - (PSK_c_scr C)) ∧ spv ≤ (2 ^ (47 : Nat))))
    (h10 : (Pv % 8) = 0)
    (h11 : (spv % 16) = 0)
    (h12 : (spv ≤ Pv ∧ (spv ≤ Ev ∧ spv ≤ Vv)))
    (h13 : (((Pv + 272) ≤ Ev ∨ (Ev + 16) ≤ Pv) ∧ (((Pv + 272) ≤ Vv ∨ (Vv + 8) ≤ Pv) ∧ ((Ev + 16) ≤ Vv ∨ (Vv + 8) ≤ Ev))))
    (h14 : (elenZ E (ELit (PSK_c_scr C))) = (PSK_c_scr C))
    (h15 : (estart E (SA spe (-(PSK_c_scr C)))) = (spv - (PSK_c_scr C))) :
    Pv = (Pv + 0) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmSmall/SmallCall.v (replace)
example (sp0 : Int) (SCR : Int) (csp : Int) (scr : Int) (k : Int) :
    ((sp0 - SCR) + (((SCR + csp) - scr) + k)) = (((sp0 + csp) - scr) + k) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmTop/ChunkBase.v (replace)
example
    {T1 T2 : Type}
    (IS : Int)
    (rep : T1)
    (g' : Int)
    (PML_srep_data : Int → T1 → Int)
    (length : T2 → Nat)
    (PML_srep_chars : T1 → T2)
    (h1 : (0 ≤ IS ∧ IS < (2 ^ (60 : Nat))))
    (h2 : ((PML_srep_data (IS + 80) rep) ≤ g' ∧ g' ≤ ((PML_srep_data (IS + 80) rep) + (((length (PML_srep_chars rep)) : Nat) : Int)))) :
    IS = (IS + 0) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmTop/ChunkStretch.v (assert)
example
    (k0 : Int)
    (bofb : Int)
    (h1 : k0 = 0)
    (h2 : ((1 ≤ k0 ∧ k0 ≤ 16383) ∧ bofb = 0))
    (h3 : ((1 ≤ k0 ∧ k0 ≤ 16383) ∧ bofb = 1)) :
    (k0 = 16384 ∧ bofb = 0) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmTop/TopKitX.v (replace)
example (u : Int) :
    (u * (256 * 2)) = (512 * u) := by
  lia

-- jsoncons/fuzz_json_encoder: lib/PmTopW/DetectKW.v (assert)
example
    {T1 T2 : Type}
    (Bof : T1 → Nat → Int)
    (s : T1)
    (w64 : T2 → Int)
    (c : T2)
    (h1 : (0 ≤ (w64 c) ∧ (w64 c) < (2 ^ (64 : Nat))))
    (h2 : (Bof s 3) = 0)
    (h3 : (Bof s 2) = 0)
    (h4 : (Bof s 1) = 254)
    (h5 : (Bof s 0) = 255)
    (h6 : (Bof s 3) = 255) :
    (Bof s 2) = 254 := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/Mh_0041.v (replace)
example
    {list_Segment T2 T3 T4 : Type}
    (segs : list_Segment)
    (g : Nat)
    (f : Nat)
    (a : T2)
    (bv_unsigned : T2 → Int)
    (base : Int)
    (off : Nat)
    (forallb : T3 → list_Segment → Bool)
    (fseg : Nat → Nat → T3)
    (chunk : T4)
    (fpos : Int → T4 → Nat → Bool)
    (fposB : Int → T4 → Nat → Bool)
    (h1 : (forallb (fseg g f) segs) = true)
    (h2 : ((off : Nat) : Int) = ((bv_unsigned a) - base))
    (h3 : (fpos base chunk off) = true)
    (h4 : (((bv_unsigned a) - base) % 2) = 0)
    (h5 : (fposB base chunk off) = true) :
    (bv_unsigned a) = (base + ((off : Nat) : Int)) := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/Mh_0077.v (assert)
example
    {word list___Z_Z acs env T5 T6 T7 : Type}
    (sp : word)
    (BUDGET : Int)
    (LENMAX : Int)
    (KMAX : Int)
    (EXTRA : list___Z_Z)
    (cs : acs)
    (E : env)
    (i : Int)
    (k : Int)
    (as0_chk : acs → Bool)
    (drv_chk : acs → Bool)
    (a_eager : acs → Int)
    (a_abytes : acs → Int)
    (A_bytes : list___Z_Z → Int)
    (AsanInitK_LIMIT : Int)
    (AsanCeil_bottomup_floor : Int)
    (a_totsz : acs → Int)
    (length : T5 → Nat)
    (segments_reserved : T6 → T5)
    (Asan_M_loaded_segments : T6)
    (a_maps : acs → T5)
    (AsanCeil_alloc_ceiling : Int)
    (stk_chk : acs → Bool)
    (SIMGx : T5)
    (bv_unsigned : word → Int)
    (Z_to_bv : Int → Int → word)
    (uE : env → T7 → Int)
    (KE_AUX : T7)
    (argc : Int)
    (envp : T5)
    (h1 : (0 ≤ BUDGET ∧ (0 ≤ KMAX ∧ (0 ≤ LENMAX ∧ LENMAX < (2 ^ (62 : Nat))))))
    (h2 : (as0_chk cs) = true)
    (h3 : (drv_chk cs) = true)
    (h4 : ((((a_eager cs) + (a_abytes cs)) + (A_bytes EXTRA)) + BUDGET) ≤ AsanInitK_LIMIT)
    (h5 : (((AsanCeil_bottomup_floor + LENMAX) + ((a_totsz cs) + BUDGET)) + ((((((length (segments_reserved Asan_M_loaded_segments)) + (length (a_maps cs))) : Nat) : Int) + KMAX) * (LENMAX + 4095))) ≤ AsanCeil_alloc_ceiling)
    (h6 : (stk_chk cs) = true)
    (h7 : (0 ≤ i ∧ i < (((length SIMGx) : Nat) : Int)))
    (h8 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + i))) = ((bv_unsigned sp) + i))
    (h9 : (uE E KE_AUX) = (((bv_unsigned sp) + (8 * argc)) + (8 * (((length envp) : Nat) : Int))))
    (h10 : (i - ((8 * argc) + (8 * (((length envp) : Nat) : Int)))) = ((8 * k) + ((i - ((8 * argc) + (8 * (((length envp) : Nat) : Int)))) % 8)))
    (h11 : (3 ≤ k ∧ k < 23)) :
    (k = 3 ∨ (k = 4 ∨ (k = 5 ∨ (k = 6 ∨ (k = 7 ∨ (k = 8 ∨ (k = 9 ∨ (k = 10 ∨ (k = 11 ∨ (k = 12 ∨ (k = 13 ∨ (k = 14 ∨ (k = 15 ∨ (k = 16 ∨ (k = 17 ∨ (k = 18 ∨ (k = 19 ∨ (k = 20 ∨ (k = 21 ∨ k = 22))))))))))))))))))) := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/Mh_0142.v (replace)
example
    {list_Z : Type}
    (dst : Int)
    (src : Int)
    (n : Int)
    (bs : list_Z)
    (i : Nat)
    (j : Int)
    (length : list_Z → Nat)
    (h1 : 1 ≤ n)
    (h2 : 0 ≤ dst)
    (h3 : (dst + n) < (2 ^ (63 : Nat)))
    (h4 : 0 ≤ src)
    (h5 : (src + n) < (2 ^ (63 : Nat)))
    (h6 : ((dst + n) ≤ src ∨ (src + n) ≤ dst))
    (h7 : (((length bs) : Nat) : Int) = n) :
    (src + (((i : Nat) : Int) + j)) = ((src + ((i : Nat) : Int)) + j) := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/Mh_0142.v (replace)
example
    {list_Z : Type}
    (dst : Int)
    (src : Int)
    (n : Int)
    (bs : list_Z)
    (i : Nat)
    (j : Int)
    (length : list_Z → Nat)
    (h1 : 1 ≤ n)
    (h2 : 0 ≤ dst)
    (h3 : (dst + n) < (2 ^ (63 : Nat)))
    (h4 : 0 ≤ src)
    (h5 : (src + n) < (2 ^ (63 : Nat)))
    (h6 : ((dst + n) ≤ src ∨ (src + n) ≤ dst))
    (h7 : (((length bs) : Nat) : Int) = n) :
    (dst + (((i : Nat) : Int) + j)) = ((dst + ((i : Nat) : Int)) + j) := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/Mh_0145.v (assert)
example (sz : Int) (q : Int) (h1 : sz = (16 * q)) (h2 : 0 < q) :
    0 < sz := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/Mh_0282.v (assert)
example (i : Nat) (h1 : (i = 0 ∨ (i = 1 ∨ (i = 2 ∨ i = 3)))) :
    (i = 0 ∨ (i = 1 ∨ (i = 2 ∨ i = 3))) := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/Mh_0288.v (assert)
example
    (F : Int)
    (ff_bytes : Int → Int)
    (fb : Int)
    (h1 : (((fb + 32) + 2008) ≤ F ∨ (F + (ff_bytes 4)) ≤ (fb + 32)))
    (h2 : 0 ≤ (F / 8))
    (h3 : ((F / 8) + ((ff_bytes 4) / 8)) ≤ 17592186044416) :
    (((F / 8) * 8) + (((ff_bytes 4) / 8) * 8)) ≤ (2 ^ (47 : Nat)) := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/PnAHarness7.v (assert)
example (i : Nat) (h1 : i = 0) :
    i = 0 := by
  lia

-- jsoncons/fuzz_msgpack_encoder: lib/PnARiT8.v (replace)
example
    (F : Int)
    (cls : Int)
    (w : Int)
    (h1 : (0 ≤ cls ∧ cls ≤ 16))
    (h2 : (7036928 ≤ F ∧ F ≤ 140737488354304))
    (h3 : 0 ≤ (F / 8))
    (h4 : (F / 8) ≤ 17592186044288)
    (h5 : ((F / 8) * 8) = F)
    (h6 : (0 ≤ w ∧ w < (2 ^ (64 : Nat))))
    (h7 : (0 ≤ w ∧ w ≤ 18446744073709551615)) :
    ((F / 8) + 2147450936) = (((F / 8) + 2147450880) + 56) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/Ea0DrvStdio.v (assert)
example
    {asan_run word : Type}
    (ar : asan_run)
    (sp0 : word)
    (x : Int)
    (bv_unsigned : word → Int)
    (ar_stack_top : asan_run → Int)
    (ahl_ceil : asan_run → Int)
    (h1 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ (2 ^ (47 : Nat))))
    (h2 : ((bv_unsigned sp0) % 16) = 0)
    (h3 : (((((bv_unsigned sp0) - 8388608) / 8) + 2147450880) ≤ x ∧ x ≤ ((((bv_unsigned sp0) - 1) / 8) + 2147450880)))
    (h4 : (ahl_ceil ar) = ((bv_unsigned sp0) - 8388608)) :
    (bv_unsigned sp0) ≤ (max (bv_unsigned sp0) (ar_stack_top ar)) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/Ea0FakeStackGCC.v (assert)
example
    {T1 T2 T3 : Type}
    (t : Int)
    (fs : Int)
    (c : Int)
    (nfr : Int)
    (nlog : Int)
    (frsz : Int)
    (flb : Int)
    (sparg : Int)
    (bot : Int)
    (Zpow : Int → Int → Int)
    (gc_shz_hi : Int → Int)
    (gc_shz_lo : Int → Int)
    (store_ok : T1 → T2 → T3 → Nat → Bool)
    (ASEGS : T1)
    (mem0 : T2)
    (Z_to_bv : Nat → Int → T3)
    (h1 : (0 ≤ c ∧ c ≤ 10))
    (h2 : nlog = (14 - c))
    (h3 : nfr = (Zpow 2 nlog))
    (h4 : frsz = (Zpow 2 (6 + c)))
    (h5 : flb = (((fs + 4096) + 32768) - (2 * nfr)))
    (h6 : (16777216 ≤ (t - 160) ∧ t < (2 ^ (64 : Nat))))
    (h7 : (6914048 ≤ fs ∧ ((((fs + 4096) + 32768) + (11 * (2 ^ (20 : Nat)))) < (2 ^ (47 : Nat)) ∧ ((((fs + 4096) + 32768) + (11 * (2 ^ (20 : Nat)))) ≤ (t - 160) ∨ t ≤ fs))))
    (h8 : ((((fs + 4096) + 32768) + (11 * (2 ^ (20 : Nat)))) ≤ 2147446784 ∨ 17594333495296 ≤ fs))
    (h9 : ((gc_shz_hi fs) ≤ (t - 160) ∨ t ≤ (gc_shz_lo fs)))
    (h10 : ((0 ≤ sparg ∧ sparg < (2 ^ (64 : Nat))) ∧ (0 ≤ bot ∧ bot < (2 ^ (64 : Nat)))))
    (h11 : (store_ok ASEGS mem0 (Z_to_bv 64 fs) (Int.toNat ((4096 + 32768) + (11 * (2 ^ (20 : Nat)))))) = true)
    (h12 : (16 ≤ nfr ∧ nfr ≤ 16384)) :
    (0 ≤ nlog ∧ nlog ≤ 14) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/Eb0DiagOpenPre.v (assert)
example
    {list_byte : Type}
    (p : Int)
    (bs : list_byte)
    (length : list_byte → Nat)
    (h1 : (((length bs) : Nat) : Int) ≤ 131071)
    (h2 : (140735332552704 ≤ p ∧ p ≤ 140737488355311)) :
    (0 ≤ (((length bs) : Nat) : Int) ∧ (((length bs) : Nat) : Int) ≤ 131071) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/Eb0DrvEntryK.v (assert)
example
    {word EntryDraw list_list_byte list___Z_Z acs env T7 T8 T9 : Type}
    (sp : word)
    (rdraw : EntryDraw)
    (argv : list_list_byte)
    (envp : list_list_byte)
    (uid : word)
    (hw : word)
    (BUDGET : Int)
    (LENMAX : Int)
    (KMAX : Int)
    (EXTRA : list___Z_Z)
    (cs : acs)
    (E : env)
    (i : Int)
    (k : Int)
    (as0_chk : acs → Bool)
    (drv_chk : acs → Bool)
    (a_eager : acs → Int)
    (a_abytes : acs → Int)
    (A_bytes : list___Z_Z → Int)
    (AsanInitK_LIMIT : Int)
    (AsanCeil_bottomup_floor : Int)
    (a_totsz : acs → Int)
    (length : list_list_byte → Nat)
    (segments_reserved : T7 → list_list_byte)
    (ASEGS0 : T7)
    (a_maps : acs → list_list_byte)
    (AsanCeil_alloc_ceiling : Int)
    (stk_chk : acs → Bool)
    (entry_stack_image : T8 → word → list_list_byte → list_list_byte → word → word → EntryDraw → list_list_byte)
    (APH0 : T8)
    (bv_unsigned : word → Int)
    (Z_to_bv : Int → Int → word)
    (uE : env → T9 → Int)
    (KE_AUX : T9)
    (h1 : (0 ≤ BUDGET ∧ (0 ≤ KMAX ∧ (0 ≤ LENMAX ∧ LENMAX < (2 ^ (62 : Nat))))))
    (h2 : (as0_chk cs) = true)
    (h3 : (drv_chk cs) = true)
    (h4 : ((((a_eager cs) + (a_abytes cs)) + (A_bytes EXTRA)) + BUDGET) ≤ AsanInitK_LIMIT)
    (h5 : (((AsanCeil_bottomup_floor + LENMAX) + ((a_totsz cs) + BUDGET)) + ((((((length (segments_reserved ASEGS0)) + (length (a_maps cs))) : Nat) : Int) + KMAX) * (LENMAX + 4095))) ≤ AsanCeil_alloc_ceiling)
    (h6 : (stk_chk cs) = true)
    (h7 : (0 ≤ i ∧ i < (((length (entry_stack_image APH0 sp argv envp uid hw rdraw)) : Nat) : Int)))
    (h8 : (((length argv) : Nat) : Int) = 2)
    (h9 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + i))) = ((bv_unsigned sp) + i))
    (h10 : (uE E KE_AUX) = (((bv_unsigned sp) + 16) + (8 * (((length envp) : Nat) : Int))))
    (h11 : (i - (16 + (8 * (((length envp) : Nat) : Int)))) = ((8 * k) + ((i - (16 + (8 * (((length envp) : Nat) : Int)))) % 8)))
    (h12 : (3 ≤ k ∧ k < 23)) :
    (k = 3 ∨ (k = 4 ∨ (k = 5 ∨ (k = 6 ∨ (k = 7 ∨ (k = 8 ∨ (k = 9 ∨ (k = 10 ∨ (k = 11 ∨ (k = 12 ∨ (k = 13 ∨ (k = 14 ∨ (k = 15 ∨ (k = 16 ∨ (k = 17 ∨ (k = 18 ∨ (k = 19 ∨ (k = 20 ∨ (k = 21 ∨ k = 22))))))))))))))))))) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/Eb0UsageEntryK.v (assert)
example
    {list___Z_Z acs env T4 T5 T6 T7 : Type}
    (BUDGET : Int)
    (LENMAX : Int)
    (KMAX : Int)
    (EXTRA : list___Z_Z)
    (cs : acs)
    (E : env)
    (i : Int)
    (k : Int)
    (as0_chk : acs → Bool)
    (drv_chk : acs → Bool)
    (a_eager : acs → Int)
    (a_abytes : acs → Int)
    (A_bytes : list___Z_Z → Int)
    (AsanInitK_LIMIT : Int)
    (AsanCeil_bottomup_floor : Int)
    (a_totsz : acs → Int)
    (length : T4 → Nat)
    (segments_reserved : T5 → T4)
    (ASEGS0 : T5)
    (a_maps : acs → T4)
    (AsanCeil_alloc_ceiling : Int)
    (stk_chk : acs → Bool)
    (SIMGx : T4)
    (bv_unsigned : T6 → Int)
    (Z_to_bv : Int → Int → T6)
    (usp : Int)
    (uE : env → T7 → Int)
    (KE_AUX : T7)
    (argc : Int)
    (envc : Int)
    (h1 : (0 ≤ BUDGET ∧ (0 ≤ KMAX ∧ (0 ≤ LENMAX ∧ LENMAX < (2 ^ (62 : Nat))))))
    (h2 : (as0_chk cs) = true)
    (h3 : (drv_chk cs) = true)
    (h4 : ((((a_eager cs) + (a_abytes cs)) + (A_bytes EXTRA)) + BUDGET) ≤ AsanInitK_LIMIT)
    (h5 : (((AsanCeil_bottomup_floor + LENMAX) + ((a_totsz cs) + BUDGET)) + ((((((length (segments_reserved ASEGS0)) + (length (a_maps cs))) : Nat) : Int) + KMAX) * (LENMAX + 4095))) ≤ AsanCeil_alloc_ceiling)
    (h6 : (stk_chk cs) = true)
    (h7 : (0 ≤ i ∧ i < (((length SIMGx) : Nat) : Int)))
    (h8 : (bv_unsigned (Z_to_bv 64 (usp + i))) = (usp + i))
    (h9 : (uE E KE_AUX) = ((usp + (8 * argc)) + (8 * envc)))
    (h10 : (i - ((8 * argc) + (8 * envc))) = ((8 * k) + ((i - ((8 * argc) + (8 * envc))) % 8)))
    (h11 : (3 ≤ k ∧ k < 23)) :
    (k = 3 ∨ (k = 4 ∨ (k = 5 ∨ (k = 6 ∨ (k = 7 ∨ (k = 8 ∨ (k = 9 ∨ (k = 10 ∨ (k = 11 ∨ (k = 12 ∨ (k = 13 ∨ (k = 14 ∨ (k = 15 ∨ (k = 16 ∨ (k = 17 ∨ (k = 18 ∨ (k = 19 ∨ (k = 20 ∨ (k = 21 ∨ k = 22))))))))))))))))))) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/Eu0MainEntry.v (replace)
example
    {word list_list_byte T3 : Type}
    (sp0 : word)
    (envv : list_list_byte)
    (tid : word)
    (bv_unsigned : word → Int)
    (auxv_off : T3 → list_list_byte → Nat)
    (av : T3)
    (i : Int)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat)))) :
    ((((bv_unsigned sp0) + (((auxv_off av envv) : Nat) : Int)) + (8 * ((7 : Nat) : Int))) + i) = ((((bv_unsigned sp0) + (((auxv_off av envv) : Nat) : Int)) + 56) + i) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/PeCBegArrU.v (replace)
example
    {list_Z st T T4 : Type}
    (sp : Int)
    (p : list_Z)
    (X : st)
    (a : T)
    (Y : T4)
    (s_bad : T4 → Bool)
    (r_begin : list_Z → Bool → st → T4)
    (F : T → list_Z → T4 → T4)
    (h1 : (s_bad (r_begin p false X)) = false)
    (h2 : (s_bad (F a p Y)) = false) :
    (sp + ((-7) * 16)) = (sp - 112) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/PeCBegObjU.v (replace)
example
    {list_Z st T T4 : Type}
    (sp : Int)
    (p : list_Z)
    (X : st)
    (a : T)
    (Y : T4)
    (s_bad : T4 → Bool)
    (r_begin : list_Z → Bool → st → T4)
    (F : T → list_Z → T4 → T4)
    (h1 : (s_bad (r_begin p true X)) = false)
    (h2 : (s_bad (F a p Y)) = false) :
    (sp + ((-7) * 16)) = (sp - 112) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/PeCRdValS.v (replace)
example
    {list_Z st T T4 : Type}
    (t : Int)
    (sp : Int)
    (p : list_Z)
    (X : st)
    (h_1 : Int)
    (a : T)
    (Y : T4)
    (s_bad : T4 → Bool)
    (r_value : list_Z → Int → st → T4)
    (F : T → list_Z → T4 → T4)
    (PMSP_pm_scr : Int → Int)
    (h1 : (0 ≤ t ∧ t < 256))
    (h2 : (s_bad (r_value p t X)) = false)
    (h3 : (0 ≤ h_1 ∧ h_1 ≤ 7))
    (h4 : (s_bad (F a p Y)) = false)
    (h5 : (12288 ≤ (PMSP_pm_scr h_1) ∧ (PMSP_pm_scr h_1) ≤ 26624)) :
    (sp + ((-5) * 16)) = (sp - 80) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/seg/SegBridgeE.v (replace)
example
    (lo : Int)
    (n : Int)
    (x : Int)
    (lit_ok : Int → Int → Bool)
    (h1 : (lit_ok lo n) = true)
    (h2 : (lo ≤ x ∧ x < (lo + n))) :
    x = (lo + (x - lo)) := by
  lia

-- jsoncons/fuzz_ubjson_encoder: lib/seg/SegBridgeE.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (x : Int)
    (lo : Int)
    (bv_unsigned : T1 → Int)
    (adenot : T2 → T3 → T1)
    (E : T2)
    (SA : T4 → Int → T3)
    (ELit : Int → T4)
    (w : Nat)
    (h1 : ((bv_unsigned (adenot E (SA (ELit 0) lo))) + ((w : Nat) : Int)) ≤ (2 ^ (64 : Nat))) :
    x = (lo + (x - lo)) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/AsanNodesExtraK.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (bv_unsigned : T1 → Int)
    (a : T1)
    (sz : T1)
    (n : Int)
    (estart : T2 → T3 → Int)
    (E : T2)
    (SA : T4 → Int → T3)
    (b : T4)
    (off : Int)
    (edenot : T2 → T4 → T1)
    (h1 : (bv_unsigned sz) = n)
    (h2 : (estart E (SA b off)) = ((bv_unsigned (edenot E b)) + off))
    (h3 : (bv_unsigned a) = (estart E (SA b off)))
    (h4 : (((bv_unsigned a) + (bv_unsigned sz)) ≤ 2147446784 ∨ (17594333495296 ≤ (bv_unsigned a) ∧ ((bv_unsigned a) + (bv_unsigned sz)) ≤ (2 ^ (47 : Nat))))) :
    ((((bv_unsigned a) + (bv_unsigned sz)) - 8) + (1 * (2 ^ (64 : Nat)))) = (((bv_unsigned a) + n) + ((2 ^ (64 : Nat)) - 8)) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/AsanPopFree.v (replace)
example :
    (0 : Nat) = (Int.toNat (4 * 0)) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/AsanPopFree.v (replace)
example (c : Int) (k : Int) (q : Int) (j : Int) :
    ((c + ((k - 1) * (q * 16))) + ((-(j * q)) * 16)) = (c + (((k - 1) - j) * (q * 16))) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/CJ/Ref/RF_ntf_D.v (replace)
example
    {T1 : Type}
    (u : Int)
    (Z_land : T1 → Int → Int)
    (w : T1)
    (Z_lxor : T1 → Int → Int)
    (h1 : (0 ≤ (Z_lxor w 18446744073709551615) ∧ (Z_lxor w 18446744073709551615) < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ (Z_land w 31) ∧ (Z_land w 31) < 32)) :
    ((u - ((Z_land w 31) + 1)) + (1 * (2 ^ (64 : Nat)))) = (u + (18446744073709551615 - (Z_land w 31))) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/CJ/Ref/RF_ntf_H.v (replace)
example
    {T1 T2 T3 : Type}
    (m_last_idx : T1 → Int)
    (get_meta_rec : T2 → T3 → T1)
    (st : T2)
    (g : T3)
    (m_freeable : T1 → Int)
    (m_sizeclass : T1 → Int) :
    ((((m_last_idx (get_meta_rec st g)) + (32 * (m_freeable (get_meta_rec st g)))) * (2 ^ (52 : Nat))) + ((m_sizeclass (get_meta_rec st g)) * (2 ^ (58 : Nat)))) = ((((m_last_idx (get_meta_rec st g)) + (32 * (m_freeable (get_meta_rec st g)))) + (64 * (m_sizeclass (get_meta_rec st g)))) * (2 ^ (52 : Nat))) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/FxCarry.v (replace)
example {T1 : Type} (C : Int) (xt_const : T1 → Int) (pos' : T1) (neg' : T1) :
    (C + (((xt_const pos') - (xt_const neg')) - C)) = ((xt_const pos') - (xt_const neg')) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/Ja0DrvEntryK.v (assert)
example
    {T1 T2 T3 T4 : Type}
    (k : Int)
    (length : T1 → Nat)
    (argv : T1)
    (bv_unsigned : T2 → Int)
    (Z_to_bv : Int → Int → T2)
    (sp : T2)
    (i : Int)
    (E : T3)
    (uE : T3 → T4 → Int)
    (KE_AUX : T4)
    (envp : T1)
    (h1 : (((length argv) : Nat) : Int) = 2)
    (h2 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + i))) = ((bv_unsigned sp) + i))
    (h3 : (uE E KE_AUX) = (((bv_unsigned sp) + 16) + (8 * (((length envp) : Nat) : Int))))
    (h4 : (i - (16 + (8 * (((length envp) : Nat) : Int)))) = ((8 * k) + ((i - (16 + (8 * (((length envp) : Nat) : Int)))) % 8)))
    (h5 : (3 ≤ k ∧ k < 23)) :
    (k = 3 ∨ (k = 4 ∨ (k = 5 ∨ (k = 6 ∨ (k = 7 ∨ (k = 8 ∨ (k = 9 ∨ (k = 10 ∨ (k = 11 ∨ (k = 12 ∨ (k = 13 ∨ (k = 14 ∨ (k = 15 ∨ (k = 16 ∨ (k = 17 ∨ (k = 18 ∨ (k = 19 ∨ (k = 20 ∨ (k = 21 ∨ k = 22))))))))))))))))))) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/Ja0FakeStackGC.v (assert)
example (c : Int) :
    ((14 - c) + (6 + c)) = 20 := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/JatAllocate3A16.v (replace)
example
    (qs : Int)
    (c : Int)
    (w : Int)
    (qz : Int)
    (ab : Int)
    (spb : Int)
    (shb : Int)
    (km : Int)
    (n : Int)
    (q16 : Int)
    (rs : Int)
    (rz : Int)
    (h1 : ab = ((spb + (c * (2 ^ (32 : Nat)))) + (w * 16)))
    (h2 : shb = ((2147450880 + (8192 * qs)) + (c * (2 ^ (29 : Nat)))))
    (h3 : 0 ≤ km)
    (h4 : (262144 * km) ≤ 3758096384)
    (h5 : ((n + 15) / 16) = q16)
    (h6 : rs = ((((max n 8) + 15) / 16) * 16))
    (h7 : (((rs + 16) + rz) % 8) = 0)
    (h8 : (ab % 16) = 0)
    (h9 : (rz % 16) = 0)
    (h10 : (ab / 8) = (((8192 * qs) + (c * (2 ^ (29 : Nat)))) + (2 * w)))
    (h11 : ((ab + rz) / 8) = ((((8192 * qs) + (c * (2 ^ (29 : Nat)))) + (2 * w)) + (2 * qz))) :
    (((((8192 * qs) + (c * (2 ^ (29 : Nat)))) + (2 * w)) + (2 * qz)) * 8) = ((((65536 * qs) + (c * (2 ^ (32 : Nat)))) + (w * 16)) + (16 * qz)) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/JatWrapAligned16.v (replace)
example {T1 : Type} (rn_spb : T1 → Int) (rn : T1) (c : Int) (v : Int) :
    (((rn_spb rn) + (c * (2 ^ (32 : Nat)))) + (8 * (2 * v))) = (((rn_spb rn) + (c * (2 ^ (32 : Nat)))) + (16 * v)) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/Jb0DiagStrK.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp0 : T1)
    (pz : Int)
    (h1 : ((((bv_unsigned sp0) - 8388608) / 8) + 1048576) ≤ (pz / 8)) :
    ((bv_unsigned sp0) + ((-1048576) * 8)) = ((bv_unsigned sp0) - 8388608) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/Jb0DrvStdio.v (assert)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp0 : T1)
    (ar_stack_top : T2 → Int)
    (ar : T2)
    (ahl_ceil : T2 → Int)
    (h1 : (ahl_ceil ar) = ((bv_unsigned sp0) - 8388608)) :
    (bv_unsigned sp0) ≤ (max (bv_unsigned sp0) (ar_stack_top ar)) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/JbtAllocA16.v (replace)
example (q16 : Int) (rs : Int) (h1 : ((rs + 16) % 8) = 0) :
    (((2 * q16) + 2) * 8) = ((16 * q16) + 16) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/JbtFree1.v (replace)
example (x0 : Int) (x1 : Int) (x2 : Int) (w : Int) (h1 : (w % 256) = (x0 % 256)) :
    (x0 + ((x1 + (256 * x2)) * 256)) = ((x0 + (256 * x1)) + (65536 * x2)) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/JbtPopulate3.v (replace)
example
    (E : Int)
    (i : Int)
    (sz : Int)
    (new : Int)
    (au : Int)
    (h1 : (0 ≤ (i * sz) ∧ (i * sz) ≤ (new * sz)))
    (h2 : (0 ≤ ((au + (i * sz)) / 16) ∧ ((au + (i * sz)) / 16) < (2 ^ (28 : Nat)))) :
    ((E - (4 * (i + 1))) + (4 * (2 ^ (64 : Nat)))) = (E + ((((2 ^ (64 : Nat)) - 1) - i) * (2 ^ (2 : Nat)))) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/Js0DrvG.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (A : Int)
    (len : Int)
    (i : Int)
    (want : Int)
    (CAPk : T1 → Int)
    (k : T1)
    (length : T2 → Nat)
    (bs : T2)
    (LEN : Int)
    (M1 : T3)
    (RSEGS : T4)
    (Z_to_bv : Int → Int → T5)
    (vals1 : T2)
    (nb : Int)
    (store_ok : T4 → T3 → T5 → Nat → Bool)
    (h1 : ((1 ≤ want ∧ want ≤ 65536) ∧ want ≤ ((CAPk k) - len)))
    (h2 : (((length bs) : Nat) : Int) = (min want (LEN - len)))
    (h3 : len = LEN)
    (h4 : (length vals1) = 73)
    (h5 : (length bs) = (Int.toNat nb))
    (h6 : (store_ok RSEGS M1 (Z_to_bv 64 (A + len)) (length bs)) = true) :
    (A + (len + i)) = ((A + len) + i) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmAOpnew.v (replace)
example
    {T1 T2 : Type}
    (sp : Int)
    (bv_unsigned : T1 → Int)
    (getr : T2 → Int → T1)
    (R1 : T2)
    (h1 : ((0 ≤ sp ∧ sp < (2 ^ (64 : Nat))) ∧ (140735332487184 ≤ sp ∧ sp ≤ 140737488355328)))
    (h2 : (bv_unsigned (getr R1 2)) = (sp - 16)) :
    (sp + ((-1) * 16)) = (sp - 16) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmARzKit.v (replace)
example
    {T1 : Type}
    (pd : Int)
    (a : Int)
    (m : Int)
    (ar : T1)
    (q : Int)
    (A0 : Int)
    (ar_fs : T1 → Int)
    (sp : Int)
    (h1 : (q / 8) ≤ (pd / 8))
    (h2 : (((pd + m) - 1) / 8) ≤ (((q + A0) - 1) / 8))
    (h3 : ((ar_fs ar) / 8) ≤ (pd / 8))
    (h4 : (((pd + m) - 1) / 8) ≤ ((((ar_fs ar) + 11571200) - 1) / 8))
    (h5 : ((2147450880 + (((pd + m) - 1) / 8)) + 8) ≤ (sp - 2560))
    (h6 : (((pd + m) - 1) / 8) < (2 ^ (44 : Nat))) :
    (pd + (a - pd)) = a := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmASrcFillTb.v (replace)
example
    {T1 T2 : Type}
    (ois : Int)
    (p' : Int)
    (p : Int)
    (sp : Int)
    (PMSPA_o_p : T1 → T2 → Int)
    (PMA_AD : T1)
    (fb : T2)
    (g : Int)
    (eg : Int)
    (h1 : p' = p)
    (h2 : ((sp - 18432) % 8) = 0)
    (h3 : (((sp - 48) - 16384) % 8) = 0)
    (h4 : ((p + 16384) ≤ g ∨ eg ≤ p))
    (h5 : ((PMSPA_o_p PMA_AD fb) % 8) = 0) :
    (ois + 156) = ((ois + 120) + 36) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmBBo3.v (assert)
example
    (NE : Int)
    (h1 : (4096 ≤ (NE - 32) ∧ (NE - 32) ≤ 140737488355296))
    (h2 : ((NE - 32) % 8) = 0) :
    (0 ≤ (NE - 32) ∧ (NE - 32) < (2 ^ (64 : Nat))) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmBBo5.v (replace)
example
    {T1 : Type}
    (F : Int)
    (i : Int)
    (len : Int)
    (PM_p_b : T1 → Int)
    (s2 : T1)
    (nn : Int)
    (PM_p_k : T1 → Int)
    (Zpow : Int → Int → Int)
    (s4 : T1)
    (h1 : (0 ≤ len ∧ len ≤ 16777216))
    (h2 : (0 ≤ ((PM_p_b s2) + (32 * nn)) ∧ ((PM_p_b s2) + (32 * nn)) ≤ 140737488355328))
    (h3 : (0 ≤ ((PM_p_b s2) + (32 * nn)) ∧ ((PM_p_b s2) + (32 * nn)) < (2 ^ (64 : Nat))))
    (h4 : (0 ≤ ((PM_p_b s2) + (32 * (Zpow 2 (PM_p_k s2)))) ∧ ((PM_p_b s2) + (32 * (Zpow 2 (PM_p_k s2)))) ≤ 140737488355328))
    (h5 : (0 ≤ ((PM_p_b s2) + (32 * (Zpow 2 (PM_p_k s2)))) ∧ ((PM_p_b s2) + (32 * (Zpow 2 (PM_p_k s2)))) < (2 ^ (64 : Nat))))
    (h6 : (F % 32) = 0)
    (h7 : ((F + 32) % 8) = 0)
    (h8 : (PM_p_b s4) = (PM_p_b s2)) :
    (F + (32 + i)) = ((F + 32) + i) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmBRdKit.v (replace)
example
    {T1 : Type}
    (o : Int)
    (d : Int)
    (a : Int)
    (sz : Int)
    (ahl_ceil : T1 → Int)
    (ar : T1)
    (h1 : (0 ≤ o ∧ (o + sz) ≤ (ahl_ceil ar))) :
    ((o + d) + (a - (o + d))) = a := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmBReaderRead.v (replace)
example
    (sp : Int)
    (fb : Int)
    (oec : Int)
    (op : Int)
    (ois : Int)
    (ov : Int)
    (h1 : oec = (fb + 992))
    (h2 : op = (fb + 464))
    (h3 : ois = (fb + 96))
    (h4 : ov = (fb + 432)) :
    (sp + ((-2176) * 16)) = (sp - 34816) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmBSrcKit.v (replace)
example (fb : Int) :
    (((128 * (fb / 1024)) + 12) * 8) = ((1024 * (fb / 1024)) + 96) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmBSrcPeek.v (replace)
example
    {T1 T2 T3 : Type}
    (sp : Int)
    (bv_unsigned : T1 → Int)
    (getr : T2 → T3 → T1)
    (R : T2)
    (reg : Int → T3)
    (os : Int)
    (op : Int)
    (h1 : (bv_unsigned (getr R (reg 10))) = os)
    (h2 : os = (op + 24))
    (h3 : ((sp - 20480) % 8) = 0)
    (h4 : (((sp - 48) - 18432) % 8) = 0) :
    (sp + ((-1155) * 16)) = ((sp - 48) - 18432) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmSEnd.v (replace)
example
    {T1 : Type}
    (vb : Int)
    (length : T1 → Nat)
    (stk : T1)
    (h1 : (0 : Int) ≤ 14336)
    (h2 : ((32 * (((length stk) : Nat) : Int)) % 32) = 0)
    (h3 : 1 ≤ (length stk)) :
    ((vb + (32 * (((length stk) : Nat) : Int))) - 32) = ((vb + (32 * (((length stk) : Nat) : Int))) - 32) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmSParse3.v (replace)
example
    {T1 T2 : Type}
    (vb2 : Int)
    (length : T1 → Nat)
    (pre : T1)
    (L : T2)
    (fb : Int)
    (hl_k_per_malloc : T2 → Int)
    (hl_b_overhead : T2 → Int)
    (vb1 : Int)
    (T : Int)
    (tl : Int)
    (ti : Int)
    (vk1 : Int)
    (Zpow : Int → Int → Int)
    (T2 : Int)
    (vk2 : Int)
    (h1 : (0 : Int) ≤ 32768)
    (h2 : ((fb + 40) % 8) = 0)
    (h3 : ((fb + 8) % 8) = 0)
    (h4 : ((fb + 432) % 8) = 0)
    (h5 : 0 ≤ (hl_k_per_malloc L))
    (h6 : 0 ≤ (hl_b_overhead L))
    (h7 : 0 < (Zpow 2 vk1))
    (h8 : (0 ≤ T ∧ (T + 32) ≤ (vb1 + (32 * (Zpow 2 vk1)))))
    (h9 : (T % 16) = 0)
    (h10 : ti = tl)
    (h11 : (0 ≤ tl ∧ tl ≤ (2 ^ (24 : Nat))))
    (h12 : (0 ≤ ti ∧ (ti < tl ∧ tl ≤ (2 ^ (24 : Nat)))))
    (h13 : 0 < (Zpow 2 vk2))
    (h14 : (0 ≤ T2 ∧ (T2 + 32) ≤ (vb2 + (32 * (Zpow 2 vk2)))))
    (h15 : (T2 % 16) = 0) :
    (vb2 + (((((length pre) : Nat) : Int) * 2) * 16)) = (vb2 + (32 * (((length pre) : Nat) : Int))) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmSParse3.v (replace)
example
    {T1 T2 : Type}
    (vb2 : Int)
    (length : T1 → Nat)
    (pre : T1)
    (L : T2)
    (fb : Int)
    (hl_k_per_malloc : T2 → Int)
    (hl_b_overhead : T2 → Int)
    (vb1 : Int)
    (T : Int)
    (tl : Int)
    (ti : Int)
    (vk1 : Int)
    (Zpow : Int → Int → Int)
    (T2 : Int)
    (vk2 : Int)
    (h1 : (0 : Int) ≤ 32768)
    (h2 : ((fb + 40) % 8) = 0)
    (h3 : ((fb + 8) % 8) = 0)
    (h4 : ((fb + 432) % 8) = 0)
    (h5 : 0 ≤ (hl_k_per_malloc L))
    (h6 : 0 ≤ (hl_b_overhead L))
    (h7 : 0 < (Zpow 2 vk1))
    (h8 : (0 ≤ T ∧ (T + 32) ≤ (vb1 + (32 * (Zpow 2 vk1)))))
    (h9 : (T % 16) = 0)
    (h10 : ti = tl)
    (h11 : (0 ≤ tl ∧ tl ≤ (2 ^ (24 : Nat))))
    (h12 : (0 ≤ ti ∧ (ti < tl ∧ tl ≤ (2 ^ (24 : Nat)))))
    (h13 : 0 < (Zpow 2 vk2))
    (h14 : (0 ≤ T2 ∧ (T2 + 32) ≤ (vb2 + (32 * (Zpow 2 vk2)))))
    (h15 : (T2 % 16) = 0) :
    (vb2 + (32 * ((((length pre) : Nat) : Int) + 1))) = ((vb2 + (32 * (((length pre) : Nat) : Int))) + 32) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmSrcSFillTb.v (replace)
example
    {heap_layout : Type}
    (L : heap_layout)
    (fb : Int)
    (p' : Int)
    (p : Int)
    (hl_sptop : heap_layout → Int)
    (g : Int)
    (eg : Int)
    (h1 : (0 : Int) ≤ 18432)
    (h2 : (((fb + 40) + 24) % 8) = 0)
    (h3 : ((fb + 440) % 8) = 0)
    (h4 : p' = p)
    (h5 : (hl_sptop L) ≤ (2 ^ (47 : Nat)))
    (h6 : ((p + 16384) ≤ g ∨ eg ≤ p))
    (h7 : (0 : Int) ≤ 16384) :
    (((fb + 440) + 120) + 32) = ((fb + 440) + 152) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PmSrcUFill.v (replace)
example
    {heap_layout : Type}
    (L : heap_layout)
    (fb : Int)
    (qc : Int)
    (hl_sptop : heap_layout → Int)
    (g : Int)
    (eg : Int)
    (p0 : Int)
    (h1 : (0 : Int) ≤ 18432)
    (h2 : (((fb + 40) + 24) % 8) = 0)
    (h3 : ((fb + 440) % 8) = 0)
    (h4 : (hl_sptop L) ≤ (2 ^ (47 : Nat)))
    (h5 : ((qc + 16384) ≤ g ∨ eg ≤ qc))
    (h6 : qc ≠ p0)
    (h7 : (0 : Int) ≤ 16384) :
    (((fb + 440) + 120) + 32) = ((fb + 440) + 152) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/PropExec.v (replace)
example
    {T1 : Type}
    (bv_wrap : T1 → Int → Int)
    (n : T1)
    (x : Int)
    (bv_half_modulus : T1 → Int)
    (y : Int) :
    ((bv_wrap n (x + (bv_half_modulus n))) + (y - (bv_half_modulus n))) = (((bv_wrap n (x + (bv_half_modulus n))) - (bv_half_modulus n)) + y) := by
  lia

-- jsoncons/fuzz_ubjson_parser_max: lib/asan/L5StepARB0.v (replace)
example (a : Int) (b : Int) :
    (a + ((max a b) - a)) = (b + ((max a b) - b)) := by
  lia

-- leptonica/bilateral_fuzzer: lib/Common/Musl/PFCoreLit.v (replace)
example
    (p : Int)
    (n : Int)
    (c : Int)
    (i : Int)
    (IMG_LO : Int)
    (IMG_TOP : Int)
    (byt : Int → Int)
    (h1 : 1 ≤ n)
    (h2 : (IMG_LO ≤ p ∧ (p + n) < IMG_TOP))
    (h3 : (byt (p + n)) = c)
    (h4 : i = (n - 1)) :
    (p + n) = ((p + i) + 1) := by
  lia

-- leptonica/bilateral_fuzzer: lib/Common/Musl/PFCoreLit.v (replace)
example
    (p : Int)
    (n : Int)
    (c : Int)
    (x : Nat)
    (N10 : Int)
    (i : Int)
    (IMG_LO : Int)
    (IMG_TOP : Int)
    (byt : Int → Int)
    (h1 : 1 ≤ n)
    (h2 : (IMG_LO ≤ p ∧ (p + n) < IMG_TOP))
    (h3 : (byt (p + n)) = c)
    (h4 : ((x : Nat) : Int) = ((n - 1) - N10))
    (h5 : (0 ≤ N10 ∧ N10 < n))
    (h6 : i = (n - 1)) :
    (p + n) = ((p + i) + 1) := by
  lia

-- leptonica/bilateral_fuzzer: lib/Common/Musl/PFCoreLit.v (replace)
example
    (p : Int)
    (n : Int)
    (c : Int)
    (x : Nat)
    (N10 : Int)
    (i : Int)
    (IMG_LO : Int)
    (IMG_TOP : Int)
    (byt : Int → Int)
    (h1 : 1 ≤ n)
    (h2 : (IMG_LO ≤ p ∧ (p + n) < IMG_TOP))
    (h3 : (byt (p + n)) = c)
    (h4 : ((x : Nat) : Int) = ((n - 1) - N10))
    (h5 : (0 ≤ N10 ∧ N10 < n))
    (h6 : i = (n - 1)) :
    ((p + i) + 1) = (p + (i + 1)) := by
  lia

-- leptonica/bilateral_fuzzer: lib/Common/Musl/StdioWrite_run2.v (replace)
example
    (su : Int)
    (f : Int)
    (dA_2f848 : Int)
    (rl_data_lo : Int)
    (h1 : (4294967296 + 112) ≤ su)
    (h2 : su ≤ 140737488355328)
    (h3 : rl_data_lo ≤ f)
    (h4 : (f + 232) ≤ (194632 + dA_2f848)) :
    su = (su - 0) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Leptonica/LeptArith2.v (replace)
example (z : Int) (k : Int) :
    ((z + (2 ^ (31 : Nat))) + (k * (2 ^ (32 : Nat)))) = ((z + ((2 ^ (32 : Nat)) * k)) + (2 ^ (31 : Nat))) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Leptonica/VL/LeptCmapValid.v (replace)
example
    {T1 T2 pixv word T5 : Type}
    (C : T1)
    (m : T2)
    (s : Int)
    (pix : Int)
    (cm : Int)
    (v : pixv)
    (Z_to_bv : Nat → Int → word)
    (c_top : T1 → Int)
    (LSTK : Int)
    (p_cmap : pixv → Int)
    (store_ok : T5 → T2 → word → Nat → Bool)
    (SEGS : T5)
    (h1 : (s % 16) = 0)
    (h2 : (((c_top C) - LSTK) + 96) ≤ s)
    (h3 : s ≤ (c_top C))
    (h4 : (p_cmap v) = 0)
    (h5 : (pix % 8) = 0)
    (h6 : ((pix + 64) ≤ cm ∨ (cm + 24) ≤ pix))
    (h7 : (store_ok SEGS m (Z_to_bv 64 pix) 64) = true) :
    (s + (-36)) = (s - 36) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Mallocng/MallocInv_ameta2.v (assert)
example
    {T1 : Type}
    (m : Int)
    (x : Int)
    (caddr : T1 → Int)
    (KAmc : T1)
    (KAm : T1)
    (h1 : ((m ≤ x ∧ x < (m + 16)) ∨ (((caddr KAmc) ≤ x ∧ x < ((caddr KAmc) + 8)) ∨ ((caddr KAm) ≤ x ∧ x < ((caddr KAm) + 8))))) :
    ((m ≤ x ∧ x < (m + 16)) ∨ (((caddr KAmc) ≤ x ∧ x < ((caddr KAmc) + 8)) ∨ (((caddr KAm) ≤ x ∧ x < ((caddr KAm) + 8)) ∨ ((¬ (m ≤ x ∧ x < (m + 16))) ∧ ((¬ ((caddr KAmc) ≤ x ∧ x < ((caddr KAmc) + 8))) ∧ (¬ ((caddr KAm) ≤ x ∧ x < ((caddr KAm) + 8)))))))) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Mallocng/MallocInv_ameta2.v (assert)
example
    {word T2 : Type}
    (m : Int)
    (bv_unsigned : word → Int)
    (a : word)
    (caddr : T2 → Int)
    (KAmc : T2)
    (KAm : T2)
    (x : Int)
    (h1 : ((m ≤ x ∧ x < (m + 16)) ∨ (((caddr KAmc) ≤ x ∧ x < ((caddr KAmc) + 8)) ∨ ((caddr KAm) ≤ x ∧ x < ((caddr KAm) + 8)))))
    (h2 : ((m ≤ x ∧ x < (m + 16)) ∨ (((caddr KAmc) ≤ x ∧ x < ((caddr KAmc) + 8)) ∨ (((caddr KAm) ≤ x ∧ x < ((caddr KAm) + 8)) ∨ ((¬ (m ≤ x ∧ x < (m + 16))) ∧ ((¬ ((caddr KAmc) ≤ x ∧ x < ((caddr KAmc) + 8))) ∧ (¬ ((caddr KAm) ≤ x ∧ x < ((caddr KAm) + 8))))))))) :
    ((m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16)) ∨ (((caddr KAmc) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < ((caddr KAmc) + 8)) ∨ (((caddr KAm) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < ((caddr KAm) + 8)) ∨ ((¬ (m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16))) ∧ ((¬ ((caddr KAmc) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < ((caddr KAmc) + 8))) ∧ (¬ ((caddr KAm) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < ((caddr KAm) + 8)))))))) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Mallocng/MallocInv_ameta2.v (assert)
example (m : Int) (x : Int) (C_FMH : Int) (xn : Int) (xp : Int) (h1 : 0 ≤ xn) (h2 : 0 ≤ xp) :
    ((m ≤ x ∧ x < (m + 16)) ∨ ((C_FMH ≤ x ∧ x < (C_FMH + 8)) ∨ ((¬ (m ≤ x ∧ x < (m + 16))) ∧ (¬ (C_FMH ≤ x ∧ x < (C_FMH + 8)))))) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Mallocng/MallocInv_ameta2.v (assert)
example
    {T1 : Type}
    (m : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (C_FMH : Int)
    (xn : Int)
    (xp : Int)
    (x : Int)
    (h1 : 0 ≤ xn)
    (h2 : 0 ≤ xp)
    (h3 : ((m ≤ x ∧ x < (m + 16)) ∨ ((C_FMH ≤ x ∧ x < (C_FMH + 8)) ∨ ((¬ (m ≤ x ∧ x < (m + 16))) ∧ (¬ (C_FMH ≤ x ∧ x < (C_FMH + 8))))))) :
    ((m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16)) ∨ ((C_FMH ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (C_FMH + 8)) ∨ ((¬ (m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16))) ∧ (¬ (C_FMH ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (C_FMH + 8)))))) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Mallocng/MallocInv_ameta2.v (assert)
example
    {T1 : Type}
    (m : Int)
    (x : Int)
    (C_FMH : Int)
    (xn : Int)
    (xp : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (h1 : 0 ≤ xn)
    (h2 : 0 ≤ xp)
    (h3 : ((m ≤ x ∧ x < (m + 16)) ∨ ((C_FMH ≤ x ∧ x < (C_FMH + 8)) ∨ ((¬ (m ≤ x ∧ x < (m + 16))) ∧ (¬ (C_FMH ≤ x ∧ x < (C_FMH + 8)))))))
    (h4 : ((m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16)) ∨ ((C_FMH ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (C_FMH + 8)) ∨ ((¬ (m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16))) ∧ (¬ (C_FMH ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (C_FMH + 8)))))))
    (h5 : (xn = xp ∨ ((xn + 40) ≤ xp ∨ (xp + 40) ≤ xn))) :
    ((m ≤ x ∧ x < (m + 16)) ∨ ((C_FMH ≤ x ∧ x < (C_FMH + 8)) ∨ ((xn ≤ x ∧ x < (xn + 8)) ∨ (((xp + 8) ≤ x ∧ x < (xp + 16)) ∨ ((¬ (m ≤ x ∧ x < (m + 16))) ∧ ((¬ (C_FMH ≤ x ∧ x < (C_FMH + 8))) ∧ ((¬ (xn ≤ x ∧ x < (xn + 8))) ∧ (¬ ((xp + 8) ≤ x ∧ x < (xp + 16)))))))))) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Mallocng/MallocInv_ameta2.v (assert)
example
    {T1 : Type}
    (m : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (C_FMH : Int)
    (xn : Int)
    (xp : Int)
    (x : Int)
    (h1 : 0 ≤ xn)
    (h2 : 0 ≤ xp)
    (h3 : ((m ≤ x ∧ x < (m + 16)) ∨ ((C_FMH ≤ x ∧ x < (C_FMH + 8)) ∨ ((¬ (m ≤ x ∧ x < (m + 16))) ∧ (¬ (C_FMH ≤ x ∧ x < (C_FMH + 8)))))))
    (h4 : ((m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16)) ∨ ((C_FMH ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (C_FMH + 8)) ∨ ((¬ (m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16))) ∧ (¬ (C_FMH ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (C_FMH + 8)))))))
    (h5 : (xn = xp ∨ ((xn + 40) ≤ xp ∨ (xp + 40) ≤ xn)))
    (h6 : ((m ≤ x ∧ x < (m + 16)) ∨ ((C_FMH ≤ x ∧ x < (C_FMH + 8)) ∨ ((xn ≤ x ∧ x < (xn + 8)) ∨ (((xp + 8) ≤ x ∧ x < (xp + 16)) ∨ ((¬ (m ≤ x ∧ x < (m + 16))) ∧ ((¬ (C_FMH ≤ x ∧ x < (C_FMH + 8))) ∧ ((¬ (xn ≤ x ∧ x < (xn + 8))) ∧ (¬ ((xp + 8) ≤ x ∧ x < (xp + 16))))))))))) :
    ((m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16)) ∨ ((C_FMH ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (C_FMH + 8)) ∨ ((xn ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (xn + 8)) ∨ (((xp + 8) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (xp + 16)) ∨ ((¬ (m ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (m + 16))) ∧ ((¬ (C_FMH ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (C_FMH + 8))) ∧ ((¬ (xn ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (xn + 8))) ∧ (¬ ((xp + 8) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (xp + 16)))))))))) := by
  lia

-- leptonica/colorfill_fuzzer: lib/Common/Mallocng/MallocInv_ntg.v (replace)
example
    (U : Int)
    (W : Int)
    (h1 : (0 ≤ U ∧ U < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ W ∧ W < (2 ^ (64 : Nat))))
    (h3 : ((W % 32) + 1) ≤ U) :
    ((U - ((W % 32) + 1)) + (1 * (2 ^ (64 : Nat)))) = (U + (((2 ^ (64 : Nat)) - 32) + (31 - (W % 32)))) := by
  lia

-- leptonica/colorfill_fuzzer: lib/K5/A08/F_printf_core_dloop.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (X1 : Int)
    (N1 : Int)
    (X2 : Int)
    (N2 : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (j : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (SHADOW_LO : Int)
    (SHADOW_HI : Int)
    (x : Int)
    (dec_digits : Int → list_Z)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 819200)
    (h5 : ((852432 ≤ Fp ∧ (Fp + 232) ≤ 864896) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6459280 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 6467584)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : ((AP + 8) ≤ X1 ∧ ((X1 + N1) ≤ VA ∧ 0 ≤ N1)))
    (h8 : (6467584 ≤ X2 ∧ ((X2 + N2) ≤ lo ∧ (0 ≤ N2 ∧ ((X2 + N2) ≤ SHADOW_LO ∨ SHADOW_HI ≤ X2)))))
    (h9 : q ≤ AP)
    (h10 : (AP + 8) ≤ VA)
    (h11 : 0 ≤ A)
    (h12 : 0 ≤ BS)
    (h13 : (x / 10) < 1844674407370955162)
    (h14 : 2 ≤ (zlength (dec_digits x))) :
    ((q + (-392)) + (j - 1)) = (((q + (-392)) + j) + (-1)) := by
  lia

-- leptonica/colorfill_fuzzer: lib/K5/Spec/StrFun.v (replace)
example {T1 : Type} (length : T1 → Nat) (str : T1) (n : Int) :
    0 = ((Int.toNat (min (((length str) : Nat) : Int) n)) - (length str)) := by
  lia

-- leptonica/edge_fuzzer: lib/Common/Leptonica/LeptNumaW.v (replace)
example (n : Int) (h1 : (0 ≤ n ∧ n ≤ 100000000)) :
    ((18446744073609551615 + n) + ((-1) * (2 ^ (64 : Nat)))) = (((n - 100000001) + (2 ^ (31 : Nat))) - (2 ^ (31 : Nat))) := by
  lia

-- leptonica/edge_fuzzer: lib/Common/Leptonica/LeptScan.v (assert)
example
    {T1 : Type}
    (x : Int)
    (Zpow : Int → Int → Int)
    (Z_lxor : Int → Int → Int)
    (Z_testbit : Int → T1 → Bool)
    (n : T1)
    (Z_log2 : Int → Int)
    (h1 : (0 ≤ x ∧ x < (2 ^ (31 : Nat))))
    (h2 : (Z_lxor x ((2 ^ (64 : Nat)) - 1)) = (((2 ^ (64 : Nat)) - 1) - x))
    (h3 : (Z_testbit x n) = false)
    (h4 : (Z_log2 x) < 64)
    (h5 : 0 < (Zpow 2 (31 - (x % 32)))) :
    1 ≤ (Zpow 2 (31 - (x % 32))) := by
  lia

-- leptonica/edge_fuzzer: lib/Common/Leptonica/VL/MaxIndex.v (replace)
example
    {T1 T2 T3 : Type}
    (pix : Int)
    (pmax : Int)
    (w : Int)
    (h_1 : Int)
    (d : Int)
    (wpl : Int)
    (data : Int)
    (sp : Int)
    (i : Int)
    (SEGS : T1)
    (M : T2)
    (Z_to_bv : Nat → Int → T3)
    (store_ok : T1 → T2 → T3 → Nat → Bool)
    (h1 : (1 ≤ pix ∧ (pix + 64) ≤ (2 ^ (64 : Nat))))
    (h2 : (pix % 8) = 0)
    (h3 : (1 ≤ pmax ∧ (pmax + 4) ≤ (2 ^ (64 : Nat))))
    (h4 : (pmax % 4) = 0)
    (h5 : (0 ≤ w ∧ w < (2 ^ (32 : Nat))))
    (h6 : (0 ≤ h_1 ∧ h_1 < (2 ^ (32 : Nat))))
    (h7 : (0 ≤ d ∧ d < (2 ^ (32 : Nat))))
    (h8 : (0 ≤ wpl ∧ wpl < (2 ^ (32 : Nat))))
    (h9 : (1 ≤ w ∧ w ≤ 20000))
    (h10 : (1 ≤ h_1 ∧ h_1 ≤ 20000))
    (h11 : (d = 1 ∨ (d = 2 ∨ (d = 4 ∨ d = 8))))
    (h12 : wpl = (((w * d) + 31) / 32))
    (h13 : (4 ≤ data ∧ data < (2 ^ (64 : Nat))))
    (h14 : (data % 4) = 0)
    (h15 : (128 ≤ sp ∧ sp < (2 ^ (64 : Nat))))
    (h16 : (sp % 16) = 0)
    (h17 : (data + (4 * (wpl * h_1))) ≤ ((2 ^ (64 : Nat)) - 1))
    (h18 : (store_ok SEGS M (Z_to_bv 64 pmax) 4) = true)
    (h19 : ((pmax + 4) ≤ pix ∨ (pix + 64) ≤ pmax))
    (h20 : ((pmax + 4) ≤ (sp - 128) ∨ sp ≤ pmax))
    (h21 : ((pix + 64) ≤ (sp - 128) ∨ sp ≤ pix)) :
    (data + ((wpl * i) * 4)) = (data + ((4 * wpl) * i)) := by
  lia

-- leptonica/edge_fuzzer: lib/Common/Mallocng/MallocInv_agnest.v (replace)
example
    {astate meta_rec T3 : Type}
    (A1 : astate)
    (sc : Int)
    (j : Int)
    (gj : Int)
    (mt : meta_rec)
    (idx : Int)
    (cnt1 : Int)
    (ab : Int)
    (av1 : Int)
    (fr : Int)
    (av2 : Int)
    (p0 : Int)
    (a_ctx : astate → T3 → Int)
    (KActive : Int → T3)
    (mt_sc : meta_rec → Int)
    (mt_last : meta_rec → Int)
    (mt_stride : meta_rec → Int)
    (size_class : Int → Int)
    (Zpow : Int → Int → Int)
    (ifr : Int → Int → Int)
    (iav : Int → Int → Int)
    (t : Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ j ∧ j < 48))
    (h3 : (a_ctx A1 (KActive j)) = gj)
    (h4 : (mt_sc mt) = j)
    (h5 : (0 ≤ idx ∧ idx ≤ (mt_last mt)))
    (h6 : (mt_stride mt) = (16 * (size_class j)))
    (h7 : (2 ≤ cnt1 ∧ cnt1 ≤ 32))
    (h8 : (((16 * (size_class sc)) * cnt1) + 16) ≤ (16 * (size_class j)))
    (h9 : (((16 * (size_class sc)) * cnt1) + 16) ≤ 2048)
    (h10 : (0 ≤ ab ∧ ab < 256))
    (h11 : (Int.fmod av1 (2 ^ (32 : Nat))) = ((Zpow 2 ((cnt1 - 1) + 1)) - 1))
    (h12 : (Int.fmod fr (2 ^ (32 : Nat))) = (ifr cnt1 (cnt1 - 1)))
    (h13 : (Int.fmod av2 (2 ^ (32 : Nat))) = (iav cnt1 (cnt1 - 1)))
    (h14 : 0 ≤ av1)
    (h15 : 0 ≤ fr)
    (h16 : 0 ≤ av2)
    (h17 : 0 ≤ (t * (16 * (size_class sc))))
    (h18 : (t * (16 * (size_class sc))) ≤ (cnt1 * (16 * (size_class sc)))) :
    1 = ((p0 - 1) - (p0 - 2)) := by
  lia

-- leptonica/edge_fuzzer: lib/K5/A9/RT_stackmalloc.v (assert)
example (NF : Int → Int) (k : Nat) (h1 : (NF ((k : Nat) : Int)) ≤ 16384) :
    (NF ((k : Nat) : Int)) ≤ 16384 := by
  lia

-- leptonica/edge_fuzzer: lib/K5/AS/AsanInit.v (assert)
example
    {list_list_byte : Type}
    (argv : list_list_byte)
    (total_arg_bytes_nat : list_list_byte → Nat) :
    0 ≤ (((total_arg_bytes_nat argv) : Nat) : Int) := by
  lia

-- leptonica/edge_fuzzer: lib/K5/AS/AsanInit.v (replace)
example
    (len : Int)
    (h1 : (0 ≤ ((8 - (len % 8)) % 8) ∧ ((8 - (len % 8)) % 8) < 8))
    (h2 : ((len + ((8 - (len % 8)) % 8)) % 8) = 0) :
    8 = ((len % 8) + (8 - (len % 8))) := by
  lia

-- leptonica/edge_fuzzer: lib/K5/B9/Ed_fp.v (replace)
example (k : Int) (h1 : ((-1) ≤ k ∧ k < 0)) :
    (-1) = k := by
  lia

-- leptonica/edge_fuzzer: lib/K5/B9/F_printf_core_scan.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (X1 : Int)
    (N1 : Int)
    (X2 : Int)
    (N2 : Int)
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
    (SHADOW_LO : Int)
    (SHADOW_HI : Int)
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 1867776)
    (h5 : ((1915408 ≤ Fp ∧ (Fp + 232) ≤ 1973376) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((7569152 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 7577600)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : ((AP + 8) ≤ X1 ∧ ((X1 + N1) ≤ VA ∧ 0 ≤ N1)))
    (h8 : (7577600 ≤ X2 ∧ ((X2 + N2) ≤ lo ∧ (0 ≤ N2 ∧ ((X2 + N2) ≤ SHADOW_LO ∨ SHADOW_HI ≤ X2)))))
    (h9 : q ≤ AP)
    (h10 : (AP + 8) ≤ VA)
    (h11 : 0 ≤ A)
    (h12 : 0 ≤ BS)
    (h13 : (znth fmt i) ≠ 0) :
    n = (((A + i) + n) - (A + i)) := by
  lia

-- leptonica/edge_fuzzer: lib/K5/B9/LeptL_gmax_loop.v (replace)
example
    {list_byte : Type}
    (k : Nat)
    (j : Int)
    (data : Int)
    (n : Int)
    (line : Int)
    (w : Int)
    (c : Int)
    (p : Int)
    (bs : list_byte)
    (length : list_byte → Nat)
    (h1 : ((k : Nat) : Int) = (w - j))
    (h2 : c = (w - j))
    (h3 : p = (line + j))
    (h4 : 0 ≤ j)
    (h5 : 1 ≤ k)
    (h6 : w ≤ (2 ^ (20 : Nat)))
    (h7 : data ≤ line)
    (h8 : (line % 4) = 0)
    (h9 : (line + (4 * ((w + 3) / 4))) ≤ (data + n))
    (h10 : 0 < data)
    (h11 : (data % 8) = 0)
    (h12 : (data + n) ≤ (2 ^ (47 : Nat)))
    (h13 : ((data + n) ≤ 2147446784 ∨ 17594333495296 ≤ data))
    (h14 : (((length bs) : Nat) : Int) = n) :
    (w - (j + 1)) = ((w - j) + (-1)) := by
  lia

-- leptonica/edge_fuzzer: lib/K5/B9/LeptL_gmax_loop.v (replace)
example
    {list_byte : Type}
    (k : Nat)
    (j : Int)
    (data : Int)
    (n : Int)
    (line : Int)
    (w : Int)
    (c : Int)
    (p : Int)
    (bs : list_byte)
    (length : list_byte → Nat)
    (h1 : ((k : Nat) : Int) = (w - j))
    (h2 : c = (w - j))
    (h3 : p = (line + j))
    (h4 : 0 ≤ j)
    (h5 : 1 ≤ k)
    (h6 : w ≤ (2 ^ (20 : Nat)))
    (h7 : data ≤ line)
    (h8 : (line % 4) = 0)
    (h9 : (line + (4 * ((w + 3) / 4))) ≤ (data + n))
    (h10 : 0 < data)
    (h11 : (data % 8) = 0)
    (h12 : (data + n) ≤ (2 ^ (47 : Nat)))
    (h13 : ((data + n) ≤ 2147446784 ∨ 17594333495296 ≤ data))
    (h14 : (((length bs) : Nat) : Int) = n) :
    (line + (j + 1)) = ((line + j) + 1) := by
  lia

-- leptonica/edge_fuzzer: lib/K5/B9/LeptL_gmax_loop.v (replace)
example
    {list_byte : Type}
    (k : Nat)
    (j : Int)
    (data : Int)
    (n : Int)
    (line : Int)
    (w : Int)
    (c : Int)
    (p : Int)
    (bs : list_byte)
    (Z_lxor : Int → Int → Int)
    (length : list_byte → Nat)
    (h1 : ((k : Nat) : Int) = (w - j))
    (h2 : c = (w - j))
    (h3 : p = (line + j))
    (h4 : 0 ≤ j)
    (h5 : 1 ≤ k)
    (h6 : w ≤ (2 ^ (20 : Nat)))
    (h7 : data ≤ line)
    (h8 : (line % 4) = 0)
    (h9 : (line + (4 * ((w + 3) / 4))) ≤ (data + n))
    (h10 : 0 < data)
    (h11 : (data % 8) = 0)
    (h12 : (data + n) ≤ (2 ^ (47 : Nat)))
    (h13 : ((data + n) ≤ 2147446784 ∨ 17594333495296 ≤ data))
    (h14 : (((length bs) : Nat) : Int) = n)
    (h15 : (j + 1) = w) :
    (Z_lxor (line + j) 3) = (data + ((Z_lxor (line + j) 3) - data)) := by
  lia

-- leptonica/edge_fuzzer: lib/K5/B9/Px_getpixel_c0.v (assert)
example
    {T1 : Type}
    (x : Int)
    (p_w : T1 → Int)
    (v : T1)
    (y : Int)
    (p_h : T1 → Int)
    (usp : Int)
    (lo : Int)
    (pval : Int)
    (pix : Int)
    (p_data : T1 → Int)
    (rsize : T1 → Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : (pval + 4) ≤ lo)
    (h3 : ((pval + 4) ≤ pix ∨ (pix + 64) ≤ pval))
    (h4 : ((pval + 4) ≤ (p_data v) ∨ ((p_data v) + (rsize v)) ≤ pval)) :
    (((0 ≤ x ∧ x < (p_w v)) ∧ (0 ≤ y ∧ y < (p_h v))) ∨ (¬ ((0 ≤ x ∧ x < (p_w v)) ∧ (0 ≤ y ∧ y < (p_h v))))) := by
  lia

-- leptonica/edge_fuzzer: lib/O9/O9LeptNfe.v (replace)
example (i : Int) :
    (i - 1) = ((i + 1) - 2) := by
  lia

-- leptonica/edge_fuzzer: lib/V9/V9LeptEdgeSegs2.v (replace)
example (nv : Int) :
    0 = (((nv - nv)).natAbs : Int) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/Common/CatExec.v (lemma)
example (n : Nat) (m : Nat) (h1 : n ≤ m) :
    n ≤ m := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/Common/Mallocng/MallocInv_mal2.v (replace)
example
    {mstate T2 meta_rec T4 : Type}
    (s1 : mstate)
    (m : Int)
    (p : Int)
    (L : Int)
    (nn : Int)
    (region_free : T2 → meta_rec → meta_rec → Bool)
    (vm_noaccess : T4 → T2)
    (ms_vm : mstate → T4)
    (Z_to_bv : Int → Int → meta_rec)
    (h1 : (L % 4096) = 0)
    (h2 : (region_free (vm_noaccess (ms_vm s1)) (Z_to_bv 64 p) (Z_to_bv 64 L)) = true)
    (h3 : (0 ≤ nn ∧ ((nn + 20) ≤ L ∧ L ≤ ((nn + 20) + 4095)))) :
    (m + 0) = m := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/K5/A10/Fh_low0_loop.v (replace)
example
    (rs : Int)
    (q0 : Int)
    (i : Int)
    (wpl : Int)
    (h_1 : Int)
    (h1 : (0 ≤ (i * wpl) ∧ (i * wpl) ≤ ((h_1 - 1) * wpl)))
    (h2 : ((h_1 - 1) * wpl) ≤ (2 ^ (40 : Nat)))
    (h3 : (i + 1) = h_1) :
    (rs + (4 * ((q0 + ((i + 1) * wpl)) - (1 * wpl)))) = ((rs + (4 * ((q0 + (i * wpl)) - (1 * wpl)))) + (wpl * 4)) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/K5/AS/AsanPlanSoundSums.v (replace)
example
    {word : Type}
    (s : word)
    (n : Int)
    (i : Int)
    (bv_unsigned : word → Int)
    (h1 : ((bv_unsigned s) + n) ≤ (2 ^ (64 : Nat)))
    (h2 : (0 ≤ i ∧ i < n)) :
    (((Int.toNat i) : Nat) : Int) = i := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/K5/B10/Fh_brick.v (replace)
example
    {T1 : Type}
    (sx : Int)
    (usp : Int)
    (sel : Int)
    (arr : Int)
    (sy : Int)
    (length : T1 → Nat)
    (ws : T1)
    (Z_b2z : Bool → Int)
    (row : Int)
    (Z_land : Int → Int → Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : ((sel + 32) ≤ arr ∨ (arr + (8 * sy)) ≤ sel))
    (h3 : (((length ws) : Nat) : Int) = sy)
    (h4 : (Z_b2z (decide (0 < arr))) = 1)
    (h5 : (Z_b2z (decide (0 < row))) = 1)
    (h6 : (Z_land (Z_b2z (decide ((Z_land row 3) < 1))) (Z_b2z (decide (0 < row)))) = 1) :
    sx = (sx - 0) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/K5/B10/Fh_brick.v (replace)
example
    {T1 : Type}
    (row : Int)
    (usp : Int)
    (sel : Int)
    (arr : Int)
    (sy : Int)
    (length : T1 → Nat)
    (ws : T1)
    (Z_b2z : Bool → Int)
    (Z_land : Int → Int → Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : ((sel + 32) ≤ arr ∨ (arr + (8 * sy)) ≤ sel))
    (h3 : (((length ws) : Nat) : Int) = sy)
    (h4 : (Z_b2z (decide (0 < arr))) = 1)
    (h5 : (Z_b2z (decide (0 < row))) = 1)
    (h6 : (Z_land (Z_b2z (decide ((Z_land row 3) < 1))) (Z_b2z (decide (0 < row)))) = 1) :
    row = (row + (4 * 0)) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/K5/B10/GmB_roplow_loop.v (replace)
example
    (datad : Int)
    (doff : Int)
    (i : Int)
    (dwpl : Int)
    (nfw : Int)
    (dh : Int)
    (swpl : Int)
    (h1 : (0 ≤ nfw ∧ nfw < (2 ^ (26 : Nat))))
    (h2 : (0 ≤ (i * dwpl) ∧ (i * dwpl) ≤ ((dh - 1) * dwpl)))
    (h3 : (0 ≤ (i * swpl) ∧ (i * swpl) ≤ ((dh - 1) * swpl)))
    (h4 : ((dh - 1) * dwpl) ≤ 100020000)
    (h5 : ((dh - 1) * swpl) ≤ 100020000)
    (h6 : (i + 1) = dh)
    (h7 : nfw = 0) :
    (datad + (4 * ((doff + (i * dwpl)) + nfw))) = (((i * dwpl) * 4) + (datad + (4 * doff))) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/K5/B10/GmB_roplow_loop.v (replace)
example
    (datas : Int)
    (soff : Int)
    (i : Int)
    (swpl : Int)
    (dwpl : Int)
    (dh : Int)
    (h1 : (0 ≤ (i * dwpl) ∧ (i * dwpl) ≤ ((dh - 1) * dwpl)))
    (h2 : (0 ≤ (i * swpl) ∧ (i * swpl) ≤ ((dh - 1) * swpl)))
    (h3 : ((dh - 1) * dwpl) ≤ 100020000)
    (h4 : ((dh - 1) * swpl) ≤ 100020000)
    (h5 : (i + 1) = dh) :
    (datas + (4 * (soff + (i * swpl)))) = ((datas + (4 * soff)) + ((i * swpl) * 4)) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/O10/O10LeptDwa.v (lemma)
example
    {T1 T2 T3 : Type}
    (datad : Int)
    (s : Int)
    (SLO : Int)
    (SHI : Int)
    (DN : Int)
    (store_ok : T1 → T2 → T3 → Nat → Bool)
    (SEGS : T1)
    (M0 : T2)
    (Z_to_bv : Nat → Int → T3)
    (h1 : ((2 ^ (18 : Nat)) ≤ s ∧ s ≤ (2 ^ (63 : Nat))))
    (h2 : (4096 ≤ SLO ∧ SHI ≤ (2 ^ (62 : Nat))))
    (h3 : (4096 ≤ datad ∧ (datad + DN) ≤ (2 ^ (62 : Nat))))
    (h4 : (store_ok SEGS M0 (Z_to_bv 64 SLO) (Int.toNat (SHI - SLO))) = true)
    (h5 : (store_ok SEGS M0 (Z_to_bv 64 datad) (Int.toNat DN)) = true) :
    (4096 ≤ (s - 160) ∧ ((s - 160) + 160) ≤ (2 ^ (63 : Nat))) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/O10/O10LeptDwa.v (assert)
example
    {T1 T2 T3 : Type}
    (datad : Int)
    (s : Int)
    (index : Int)
    (SLO : Int)
    (SHI : Int)
    (DN : Int)
    (store_ok : T1 → T2 → T3 → Nat → Bool)
    (SEGS : T1)
    (M0 : T2)
    (Z_to_bv : Nat → Int → T3)
    (h1 : ((2 ^ (18 : Nat)) ≤ s ∧ s ≤ (2 ^ (63 : Nat))))
    (h2 : (0 ≤ index ∧ index ≤ 9))
    (h3 : (4096 ≤ SLO ∧ SHI ≤ (2 ^ (62 : Nat))))
    (h4 : (4096 ≤ datad ∧ (datad + DN) ≤ (2 ^ (62 : Nat))))
    (h5 : (store_ok SEGS M0 (Z_to_bv 64 SLO) (Int.toNat (SHI - SLO))) = true)
    (h6 : (store_ok SEGS M0 (Z_to_bv 64 datad) (Int.toNat DN)) = true) :
    (index = 0 ∨ (index = 1 ∨ (index = 2 ∨ (index = 3 ∨ (index = 4 ∨ (index = 5 ∨ (index = 6 ∨ (index = 7 ∨ (index = 8 ∨ index = 9))))))))) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/O10/O10LeptHmtW.v (replace)
example
    {lctx T2 : Type}
    (C : lctx)
    (s : Int)
    (w : Int)
    (h_1 : Int)
    (kR : Int)
    (bR : Int)
    (p2 : Int)
    (k2 : Int)
    (b2 : Int)
    (c_top : lctx → Int)
    (LSTK : Int)
    (HMT_STACK : Int)
    (RK10_hmt : Int → Int)
    (RB10_hmt : Int → Int → Int → Int)
    (RK_pixcopy : Int)
    (RB10_pixcopy : T2 → Int)
    (rast : Int → Int → Int → T2)
    (h1 : (s % 16) = 0)
    (h2 : (((c_top C) - LSTK) + HMT_STACK) ≤ s)
    (h3 : s ≤ (c_top C))
    (h4 : 1 ≤ w)
    (h5 : 1 ≤ h_1)
    (h6 : (RK10_hmt 1) ≤ kR)
    (h7 : (RB10_hmt 1 w h_1) ≤ bR)
    (h8 : ((kR - (RK10_hmt 1)) + RK_pixcopy) ≤ k2)
    (h9 : ((bR - (RB10_hmt 1 w h_1)) + (RB10_pixcopy (rast w h_1 1))) ≤ b2)
    (h10 : 0 ≤ (RB10_pixcopy (rast w h_1 1)))
    (h11 : 64 ≤ s)
    (h12 : s < (2 ^ (64 : Nat)))
    (h13 : p2 ≠ 0) :
    w = (((w + 64) - 32) - 32) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/O10/O10LeptHmtW.v (replace)
example
    {lctx T2 : Type}
    (C : lctx)
    (s : Int)
    (w : Int)
    (h_1 : Int)
    (kR : Int)
    (bR : Int)
    (p2 : Int)
    (k2 : Int)
    (b2 : Int)
    (c_top : lctx → Int)
    (LSTK : Int)
    (HMT_STACK : Int)
    (RK10_hmt : Int → Int)
    (RB10_hmt : Int → Int → Int → Int)
    (RK_pixcopy : Int)
    (RB10_pixcopy : T2 → Int)
    (rast : Int → Int → Int → T2)
    (h1 : (s % 16) = 0)
    (h2 : (((c_top C) - LSTK) + HMT_STACK) ≤ s)
    (h3 : s ≤ (c_top C))
    (h4 : 1 ≤ w)
    (h5 : 1 ≤ h_1)
    (h6 : (RK10_hmt 1) ≤ kR)
    (h7 : (RB10_hmt 1 w h_1) ≤ bR)
    (h8 : ((kR - (RK10_hmt 1)) + RK_pixcopy) ≤ k2)
    (h9 : ((bR - (RB10_hmt 1 w h_1)) + (RB10_pixcopy (rast w h_1 1))) ≤ b2)
    (h10 : 0 ≤ (RB10_pixcopy (rast w h_1 1)))
    (h11 : 64 ≤ s)
    (h12 : s < (2 ^ (64 : Nat)))
    (h13 : p2 ≠ 0) :
    h_1 = (((h_1 + 64) - 32) - 32) := by
  lia

-- leptonica/fhmtgen_fuzzer: lib/O10/O10LeptPixT.v (assert)
example
    {T1 : Type}
    (C : T1)
    (s : Int)
    (w : Int)
    (h_1 : Int)
    (d : Int)
    (wpl_of : Int → Int → Int)
    (c_top : T1 → Int)
    (LSTK : Int)
    (LSF : Int)
    (h1 : (s % 16) = 0)
    (h2 : ((((c_top C) - LSTK) + 48) + LSF) ≤ s)
    (h3 : s ≤ (c_top C))
    (h4 : (1 ≤ w ∧ w ≤ 1000000))
    (h5 : (1 ≤ h_1 ∧ h_1 ≤ 1000000))
    (h6 : (4 * ((wpl_of w d) * h_1)) < (2 ^ (31 : Nat)))
    (h7 : (0 ≤ d ∧ d < (2 ^ (64 : Nat)))) :
    (4 * ((wpl_of w d) * h_1)) < (2 ^ (64 : Nat)) := by
  lia

-- leptonica/graymorph_fuzzer: lib/Common/Leptonica/OL/LeptPixDestroy.v (replace)
example
    {T1 T2 pixv T4 word T6 : Type}
    (C : T1)
    (m : T2)
    (s : Int)
    (pp : Int)
    (pix : Int)
    (cm : Int)
    (v : pixv)
    (u : T4 → Int)
    (x : T4)
    (Z_to_bv : Nat → Int → word)
    (c_top : T1 → Int)
    (LSTK : Int)
    (ALLOC_STACK : Int)
    (SEGS : T6)
    (p_rc : pixv → Int)
    (p_text : pixv → Int)
    (p_cmap : pixv → Int)
    (store_ok : T6 → T2 → word → Nat → Bool)
    (h1 : (s % 16) = 0)
    (h2 : ((((c_top C) - LSTK) + 64) + ALLOC_STACK) ≤ s)
    (h3 : s ≤ pp)
    (h4 : (pp + 8) ≤ (c_top C))
    (h5 : (p_rc v) = 1)
    (h6 : (p_text v) = 0)
    (h7 : (p_cmap v) = cm)
    (h8 : (store_ok SEGS m (Z_to_bv 64 pix) 64) = true)
    (h9 : cm ≠ 0) :
    (u x) = (cm + ((u x) - cm)) := by
  lia

-- leptonica/graymorph_fuzzer: lib/Common/Mallocng/MallocInv_ameta6x.v (assert)
example
    {astate T2 word : Type}
    (A0 : astate)
    (A : astate)
    (caddr : T2 → Int)
    (KAac : T2)
    (bv_unsigned : word → Int)
    (x : word)
    (KShift : T2)
    (KAareas : T2)
    (a_ctx : astate → T2 → Int)
    (KBrk : T2)
    (Z_to_bv : Int → Int → word)
    (L : Int)
    (page_round_up_Z : Int → Int)
    (Zpow : Int → Int → Int)
    (sh : Int)
    (h1 : (a_ctx A KBrk) = ((2 ^ (64 : Nat)) - 1))
    (h2 : (bv_unsigned (Z_to_bv 64 L)) = L)
    (h3 : (page_round_up_Z L) = L)
    (h4 : L = (Zpow 2 ((a_ctx A0 KShift) + 13)))
    (h5 : sh = 0)
    (h6 : (a_ctx A KShift) = sh) :
    (((caddr KAac) ≤ (bv_unsigned x) ∧ (bv_unsigned x) < ((caddr KAac) + 8)) ∨ (((caddr KShift) ≤ (bv_unsigned x) ∧ (bv_unsigned x) < ((caddr KShift) + 8)) ∨ (((caddr KAareas) ≤ (bv_unsigned x) ∧ (bv_unsigned x) < ((caddr KAareas) + 8)) ∨ ((¬ ((caddr KAac) ≤ (bv_unsigned x) ∧ (bv_unsigned x) < ((caddr KAac) + 8))) ∧ ((¬ ((caddr KShift) ≤ (bv_unsigned x) ∧ (bv_unsigned x) < ((caddr KShift) + 8))) ∧ (¬ ((caddr KAareas) ≤ (bv_unsigned x) ∧ (bv_unsigned x) < ((caddr KAareas) + 8)))))))) := by
  lia

-- leptonica/graymorph_fuzzer: lib/Common/Mallocng/MallocInv_ameta6x.v (assert)
example {T1 : Type} (B : Int) (bv_unsigned : T1 → Int) (a : T1) :
    ((B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 4096)) ∨ (¬ (B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 4096)))) := by
  lia

-- leptonica/graymorph_fuzzer: lib/Common/Mallocng/MallocInv_ameta6x.v (assert)
example
    {word T2 T3 T4 T5 : Type}
    (B : Int)
    (bv_unsigned : word → Int)
    (a : word)
    (vm_start_brk : T2 → word)
    (ms_vm : T3 → T2)
    (s : T3)
    (A1 : T4)
    (a_ctx : T4 → T5 → Int)
    (KBrk : T5)
    (h2 : T2)
    (vm_brk : T2 → word)
    (n4 : word)
    (h1 : (bv_unsigned (vm_start_brk (ms_vm s))) = B)
    (h2_1 : (a_ctx A1 KBrk) = B)
    (h3 : (bv_unsigned (vm_brk h2)) = (B + 8192))
    (h4 : (bv_unsigned n4) = 4096) :
    ((B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 4096)) ∨ (¬ (B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 4096)))) := by
  lia

-- leptonica/graymorph_fuzzer: lib/Common/Mallocng/MallocInv_ameta6x.v (assert)
example
    {word T2 T3 T4 T5 : Type}
    (B : Int)
    (bv_unsigned : word → Int)
    (a : word)
    (vm_start_brk : T2 → word)
    (ms_vm : T3 → T2)
    (s : T3)
    (A1 : T4)
    (a_ctx : T4 → T5 → Int)
    (KBrk : T5)
    (h2 : T2)
    (vm_brk : T2 → word)
    (n4 : word)
    (h1 : (bv_unsigned (vm_start_brk (ms_vm s))) = B)
    (h2_1 : (a_ctx A1 KBrk) = B)
    (h3 : (bv_unsigned (vm_brk h2)) = (B + 8192))
    (h4 : (bv_unsigned n4) = 4096)
    (h5 : ((B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 4096)) ∨ (¬ (B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 4096)))))
    (h6 : (((B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 4096)) ∨ ((B + 4096) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 8192))) ∨ (¬ (B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 8192))))) :
    ((B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 8192)) ∨ (¬ (B ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (B + 8192)))) := by
  lia

-- leptonica/graymorph_fuzzer: lib/K5/A14/F_printf_core_xloop.v (replace)
example
    {list_Z T2 : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (X1 : Int)
    (N1 : Int)
    (X2 : Int)
    (N2 : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (j : Int)
    (zlength : list_Z → Int)
    (hex_digits : T2 → Int → list_Z)
    (l : T2)
    (x : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (SHADOW_LO : Int)
    (SHADOW_HI : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 909312)
    (h5 : ((943088 ≤ Fp ∧ (Fp + 232) ≤ 959104) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6556176 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 6565888)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : ((AP + 8) ≤ X1 ∧ ((X1 + N1) ≤ VA ∧ 0 ≤ N1)))
    (h8 : (6565888 ≤ X2 ∧ ((X2 + N2) ≤ lo ∧ (0 ≤ N2 ∧ ((X2 + N2) ≤ SHADOW_LO ∨ SHADOW_HI ≤ X2)))))
    (h9 : q ≤ AP)
    (h10 : (AP + 8) ≤ VA)
    (h11 : 0 ≤ A)
    (h12 : 0 ≤ BS)
    (h13 : (x / 16) < 1152921504606846976)
    (h14 : 1 ≤ (zlength (hex_digits l x)))
    (h15 : (zlength (hex_digits l x)) = ((zlength (hex_digits l (x / 16))) + 1)) :
    (Int.toNat (j - ((zlength (hex_digits l (x / 16))) + 1))) = (Int.toNat ((j - 1) - (zlength (hex_digits l (x / 16))))) := by
  lia

-- leptonica/graymorph_fuzzer: lib/K5/A14/GmL_sbv_loop.v (replace)
example
    (data : Int)
    (i : Int)
    (wpl : Int)
    (ld : Int)
    (h1 : ((i * wpl) + wpl) ≤ ld)
    (h2 : 0 ≤ (i * wpl)) :
    ((data + (4 * (i * wpl))) + 0) = (data + (4 * (i * wpl))) := by
  lia

-- leptonica/graymorph_fuzzer: lib/K5/B14/R_fs0.v (replace)
example (FSB : Int) (F8 : Int) (h1 : FSB = (8 * F8)) :
    FSB = (FSB + (8 * 0)) := by
  lia

-- leptonica/graymorph_fuzzer: lib/O14/O14LeptGrayA.v (replace)
example
    {T1 T2 pixv T4 word T6 : Type}
    (C : T1)
    (m : T2)
    (s : Int)
    (pp : Int)
    (pix : Int)
    (R : Int)
    (v : pixv)
    (u : T4 → Int)
    (x : T4)
    (Z_to_bv : Nat → Int → word)
    (c_top : T1 → Int)
    (LSTK : Int)
    (ALLOC_STACK : Int)
    (SEGS : T6)
    (p_rc : pixv → Int)
    (p_text : pixv → Int)
    (p_cmap : pixv → Int)
    (p_data : pixv → Int)
    (store_ok : T6 → T2 → word → Nat → Bool)
    (h1 : (s % 16) = 0)
    (h2 : ((((c_top C) - LSTK) + 64) + ALLOC_STACK) ≤ s)
    (h3 : s ≤ pp)
    (h4 : (pp + 8) ≤ (c_top C))
    (h5 : (p_rc v) = 1)
    (h6 : (p_text v) = 0)
    (h7 : (p_cmap v) = 0)
    (h8 : 0 < R)
    (h9 : (p_data v) ≠ pix)
    (h10 : (store_ok SEGS m (Z_to_bv 64 pix) 64) = true) :
    (u x) = (pix + ((u x) - pix)) := by
  lia

-- leptonica/graymorph_fuzzer: lib/O14/O14LeptRopUni.v (assert)
example
    {lctx : Type}
    (C : lctx)
    (s : Int)
    (datad : Int)
    (nd : Int)
    (nfw : Int)
    (k : Int)
    (DW : Int)
    (dh : Int)
    (dwpl : Int)
    (c_top : lctx → Int)
    (LSTK : Int)
    (ROPUNI_STACK : Int)
    (i : Int)
    (h1 : (((c_top C) - LSTK) + ROPUNI_STACK) ≤ s)
    (h2 : s ≤ (c_top C))
    (h3 : (0 ≤ datad ∧ datad < (2 ^ (64 : Nat))))
    (h4 : 0 < nd)
    (h5 : (1 ≤ DW ∧ DW < (2 ^ (31 : Nat))))
    (h6 : DW = ((32 * nfw) + k))
    (h7 : (0 ≤ k ∧ k < 32))
    (h8 : (0 ≤ nfw ∧ nfw < (2 ^ (26 : Nat))))
    (h9 : (1 ≤ dh ∧ dh ≤ 20000))
    (h10 : (1 ≤ dwpl ∧ dwpl < (2 ^ (24 : Nat))))
    (h11 : (dh * dwpl) ≤ (2 ^ (24 : Nat)))
    (h12 : (0 ≤ (i * dwpl) ∧ ((i * dwpl) + dwpl) ≤ (2 ^ (24 : Nat))))
    (h13 : k = DW) :
    k ≠ 0 := by
  lia

-- leptonica/graymorph_fuzzer: lib/O14/O14MemsetFill.v (replace)
example
    {T1 T2 T3 : Type}
    (d : Int)
    (n : Int)
    (k : Int)
    (store_ok : T1 → T2 → T3 → Nat → Bool)
    (SEGS : T1)
    (M : T2)
    (Z_to_bv : Nat → Int → T3)
    (h1 : 0 ≤ d)
    (h2 : 1 ≤ n)
    (h3 : n < (2 ^ (64 : Nat)))
    (h4 : (d + n) ≤ (2 ^ (64 : Nat)))
    (h5 : (store_ok SEGS M (Z_to_bv 64 d) (Int.toNat n)) = true)
    (h6 : ((-d) % 4) = k) :
    0 = (d + (-d)) := by
  lia

-- leptonica/graymorph_fuzzer: lib/V14/V14LeptGrayA.v (replace)
example
    {T1 T2 pixv T4 word T6 : Type}
    (C : T1)
    (m : T2)
    (s : Int)
    (pp : Int)
    (pix : Int)
    (R : Int)
    (v : pixv)
    (u : T4 → Int)
    (x : T4)
    (Z_to_bv : Nat → Int → word)
    (c_top : T1 → Int)
    (LSTK : Int)
    (ALLOC_STACK : Int)
    (SEGS : T6)
    (p_rc : pixv → Int)
    (p_text : pixv → Int)
    (p_cmap : pixv → Int)
    (p_data : pixv → Int)
    (store_ok : T6 → T2 → word → Nat → Bool)
    (h1 : (s % 16) = 0)
    (h2 : ((((c_top C) - LSTK) + 64) + ALLOC_STACK) ≤ s)
    (h3 : s ≤ pp)
    (h4 : (pp + 8) ≤ (c_top C))
    (h5 : (pp % 8) = 0)
    (h6 : (p_rc v) = 1)
    (h7 : (p_text v) = 0)
    (h8 : (p_cmap v) = 0)
    (h9 : 0 < R)
    (h10 : (p_data v) ≠ pix)
    (h11 : (store_ok SEGS m (Z_to_bv 64 pix) 64) = true) :
    (u x) = (pix + ((u x) - pix)) := by
  lia

-- leptonica/graymorph_fuzzer: lib/V14/V14LeptPixSure.v (replace)
example
    {T1 T2 : Type}
    (C : T1)
    (s : Int)
    (w : Int)
    (h_1 : Int)
    (d : Int)
    (kR : Int)
    (bR : Int)
    (u : T2 → Int)
    (x : T2)
    (pix : Int)
    (c_top : T1 → Int)
    (LSTK : Int)
    (LSF : Int)
    (RK_pix : Int)
    (RB_pix14 : Int)
    (h1 : (s % 16) = 0)
    (h2 : ((((c_top C) - LSTK) + 96) + LSF) ≤ s)
    (h3 : s ≤ (c_top C))
    (h4 : (1 ≤ w ∧ w ≤ 1000000))
    (h5 : (1 ≤ h_1 ∧ h_1 ≤ 1000000))
    (h6 : (w * h_1) ≤ 400000000)
    (h7 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h8 : RK_pix ≤ kR)
    (h9 : RB_pix14 ≤ bR)
    (h10 : (pix % 8) = 0) :
    (u x) = (pix + ((u x) - pix)) := by
  lia

-- leptonica/graymorph_fuzzer: lib/V14/V14Tail.v (replace)
example
    {lctx : Type}
    (C : lctx)
    (s : Int)
    (w : Int)
    (h_1 : Int)
    (kR : Int)
    (bR : Int)
    (RB_graymorph : Int)
    (RB_pixcopy14 : Int)
    (RB_gm4 : Int)
    (RB_gm3 : Int)
    (c_top : lctx → Int)
    (RK_graymorph : Int)
    (h1 : (s % 16) = 0)
    (h2 : (c_top C) = s)
    (h3 : 1 ≤ w)
    (h4 : 1 ≤ h_1)
    (h5 : RK_graymorph ≤ kR)
    (h6 : RB_graymorph ≤ bR) :
    (((bR - RB_graymorph) + (RB_pixcopy14 + RB_gm4)) + (RB_pixcopy14 + RB_gm3)) = ((((((bR - RB_graymorph) + (RB_pixcopy14 + RB_gm4)) + (RB_pixcopy14 + RB_gm3)) + (RB_pixcopy14 + RB_gm3)) - RB_pixcopy14) - RB_gm3) := by
  lia

-- leptonica/grayquant_fuzzer: lib/Common/Leptonica/LeptExecT.v (replace)
example
    (c : Int)
    (arr : Int)
    (d : Int)
    (nalloc : Int)
    (n : Int)
    (pad : Int)
    (i : Int)
    (h1 : (0 ≤ c ∧ c < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ arr ∧ arr < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ d ∧ d < (2 ^ (31 : Nat))))
    (h4 : (0 ≤ nalloc ∧ nalloc < (2 ^ (31 : Nat))))
    (h5 : (0 ≤ n ∧ n < (2 ^ (31 : Nat))))
    (h6 : (0 ≤ pad ∧ pad < (2 ^ (31 : Nat)))) :
    (c + (8 + i)) = ((c + 8) + i) := by
  lia

-- leptonica/grayquant_fuzzer: lib/Common/Leptonica/LeptExecT.v (replace)
example
    (c : Int)
    (arr : Int)
    (d : Int)
    (nalloc : Int)
    (n : Int)
    (pad : Int)
    (h1 : (0 ≤ c ∧ c < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ arr ∧ arr < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ d ∧ d < (2 ^ (31 : Nat))))
    (h4 : (0 ≤ nalloc ∧ nalloc < (2 ^ (31 : Nat))))
    (h5 : (0 ≤ n ∧ n < (2 ^ (31 : Nat))))
    (h6 : (0 ≤ pad ∧ pad < (2 ^ (31 : Nat)))) :
    (c + 12) = ((c + 8) + 4) := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/A15/Gq_rmc_rows.v (assert)
example
    (i : Int)
    (h_1 : Int)
    (w : Int)
    (wpl : Int)
    (h1 : (w ≤ (4 * wpl) ∧ ((4 * wpl) ≤ (w + 3) ∧ (0 < wpl ∧ wpl ≤ 5000))))
    (h2 : (0 ≤ i ∧ i < h_1))
    (h3 : ((i * wpl) + wpl) ≤ (wpl * h_1))
    (h4 : 0 ≤ (i * wpl))
    (h5 : (((Int.toNat (w / 4)) : Nat) : Int) = ((w / 4) - 0))
    (h6 : 1 ≤ (Int.toNat (w / 4)))
    (h7 : w ≤ (4 * (w / 4)))
    (h8 : (4 * (w / 4)) < w)
    (h9 : (((Int.toNat (w - (4 * (w / 4)))) : Nat) : Int) = (w - (4 * (w / 4))))
    (h10 : 1 ≤ (Int.toNat (w - (4 * (w / 4))))) :
    (i + 1) = h_1 := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/A15/Gq_rmc_rows.v (assert)
example
    (i : Int)
    (h_1 : Int)
    (w : Int)
    (wpl : Int)
    (h1 : (w ≤ (4 * wpl) ∧ ((4 * wpl) ≤ (w + 3) ∧ (0 < wpl ∧ wpl ≤ 5000))))
    (h2 : (0 ≤ i ∧ i < h_1))
    (h3 : ((i * wpl) + wpl) ≤ (wpl * h_1))
    (h4 : 0 ≤ (i * wpl))
    (h5 : (((Int.toNat (w / 4)) : Nat) : Int) = ((w / 4) - 0))
    (h6 : 1 ≤ (Int.toNat (w / 4)))
    (h7 : w ≤ (4 * (w / 4)))
    (h8 : (4 * (w / 4)) < w)
    (h9 : (((Int.toNat (w - (4 * (w / 4)))) : Nat) : Int) = (w - (4 * (w / 4))))
    (h10 : 1 ≤ (Int.toNat (w - (4 * (w / 4)))))
    (h11 : (i + 1) = h_1) :
    (i + 1) < h_1 := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/A15/R_fs_gen.v (replace)
example (c : Int) (c' : Int) (h1 : 0 ≤ c) (h2 : c < c') (h3 : c' ≤ 10) :
    c' = ((c + 1) + (((Int.toNat (c' - (c + 1))) : Nat) : Int)) := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/A15/R_fs_gen.v (lemma)
example (k : Nat) (h1 : k ≤ 10) :
    (0 ≤ ((k : Nat) : Int) ∧ ((k : Nat) : Int) ≤ 10) := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/A15/R_popfree_T.v (replace)
example
    (X : Int)
    (i : Int)
    (Z_lnot : Int → Int)
    (h1 : (0 ≤ i ∧ i < (2 ^ (62 : Nat))))
    (h2 : (Int.fmod (Z_lnot i) (2 ^ (64 : Nat))) = (((2 ^ (64 : Nat)) - i) - 1)) :
    (((X - 4) - (4 * i)) + (4 * (2 ^ (64 : Nat)))) = (X + ((((2 ^ (64 : Nat)) - i) - 1) * (2 ^ (2 : Nat)))) := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/B15/Gm_copycmap.v (assert)
example
    (cms : Int)
    (usp : Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : ((usp % 32) = 0 ∨ (usp % 32) = 16))
    (h3 : cms ≠ 0) :
    cms ≠ 0 := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/B15/Gq_band32_loop.v (replace)
example
    (datas : Int)
    (i : Int)
    (wpls : Int)
    (j : Int)
    (h_1 : Int)
    (wpld : Int)
    (h1 : ((i * wpls) + wpls) ≤ (wpls * h_1))
    (h2 : 0 ≤ (i * wpls))
    (h3 : ((i * wpld) + wpld) ≤ (wpld * h_1))
    (h4 : 0 ≤ (i * wpld))
    (h5 : (0 ≤ (j / 32) ∧ (j / 32) < wpld)) :
    (datas + (4 * ((i * wpls) + (j + 1)))) = ((datas + (4 * ((i * wpls) + j))) + 4) := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/B15/Gq_cmaplin.v (replace)
example
    (carr : Int)
    (usp : Int)
    (cmap : Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : ((cmap + 24) ≤ carr ∨ (carr + 16) ≤ cmap)) :
    carr = (carr + (4 * 0)) := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/B15/Gq_dither2_l0.v (replace)
example
    (r : Int)
    (v : Int)
    (h1 : (0 ≤ r ∧ r ≤ 65535))
    (h2 : (v ≤ 65535 ∨ ((2 ^ (64 : Nat)) - 65536) ≤ v))
    (h3 : (0 ≤ v ∧ v < (2 ^ (64 : Nat)))) :
    ((((r + v) - 18446744073709551616) + 2147483648) + (4294967296 * 4294967296)) = ((((r + v) - 18446744073709551616) + (1 * 18446744073709551616)) + 2147483648) := by
  lia

-- leptonica/grayquant_fuzzer: lib/K5/B15/Gq_qtab_c0.v (replace)
example
    (usp : Int)
    (lo : Int)
    (ptab : Int)
    (pcmap : Int)
    (SEGTOP_A : Int)
    (fr : Int)
    (cmap : Int)
    (carr : Int)
    (tab : Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : 0 < ptab)
    (h3 : ((ptab + 8) ≤ 2147446784 ∨ 17594333495296 ≤ ptab))
    (h4 : ((ptab + 8) ≤ 65536 ∨ SEGTOP_A ≤ ptab))
    (h5 : (ptab + 8) ≤ (2 ^ (47 : Nat)))
    (h6 : (pcmap + 8) ≤ lo)
    (h7 : (pcmap + 8) ≤ (usp - 208))
    (h8 : ((ptab + 8) ≤ pcmap ∨ (pcmap + 8) ≤ ptab))
    (h9 : (fr + 64) ≤ ptab)
    (h10 : ((ptab + 8) ≤ cmap ∨ (cmap + 24) ≤ ptab))
    (h11 : ((ptab + 8) ≤ carr ∨ (carr + 1024) ≤ ptab))
    (h12 : ((pcmap + 8) ≤ cmap ∨ (cmap + 24) ≤ pcmap))
    (h13 : ((pcmap + 8) ≤ carr ∨ (carr + 1024) ≤ pcmap))
    (h14 : (cmap + 24) ≤ (usp - 208))
    (h15 : (carr + 1024) ≤ (usp - 208))
    (h16 : ((ptab + 8) ≤ tab ∨ (tab + 1024) ≤ ptab))
    (h17 : ((pcmap + 8) ≤ tab ∨ (tab + 1024) ≤ pcmap))
    (h18 : (tab % 16) = 0)
    (h19 : 0 < tab)
    (h20 : (tab + 1024) < (2 ^ (47 : Nat)))
    (h21 : (tab + 1024) ≤ (usp - 208)) :
    ((usp + (-192)) + 56) = (usp + (-136)) := by
  lia

-- leptonica/grayquant_fuzzer: lib/O15/O15CL10a.v (replace)
example
    {T1 T2 : Type}
    (C : T1)
    (s : Int)
    (w : Int)
    (h_1 : Int)
    (d : Int)
    (kR : Int)
    (bR : Int)
    (u : T2 → Int)
    (x : T2)
    (pix : Int)
    (c_top : T1 → Int)
    (LSTK : Int)
    (LSF : Int)
    (RK_pix : Int)
    (RB_pix14 : Int)
    (h1 : (s % 16) = 0)
    (h2 : ((((c_top C) - LSTK) + 96) + LSF) ≤ s)
    (h3 : s ≤ (c_top C))
    (h4 : 1 ≤ w)
    (h5 : 1 ≤ h_1)
    (h6 : RK_pix ≤ kR)
    (h7 : RB_pix14 ≤ bR)
    (h8 : (1 ≤ w ∧ w ≤ 1000000))
    (h9 : (1 ≤ h_1 ∧ h_1 ≤ 1000000))
    (h10 : (w * h_1) ≤ 400000000)
    (h11 : (0 ≤ d ∧ d < (2 ^ (64 : Nat)))) :
    (u x) = (pix + ((u x) - pix)) := by
  lia

-- leptonica/grayquant_fuzzer: lib/O15/O15Tail.v (assert)
example
    {T1 : Type}
    (s : Int)
    (c_top : T1 → Int)
    (C : T1)
    (LSTK : Int)
    (pixs : Int)
    (OFF2 : Int)
    (OFF3 : Int)
    (h1 : (((c_top C) - LSTK) + 48) ≤ s)
    (h2 : ((c_top C) - LSTK) ≤ (s - 48))
    (h3 : ((s - 48) + (((Int.toNat 48) : Nat) : Int)) ≤ (c_top C))
    (h4 : (0 ≤ s ∧ s < (2 ^ (64 : Nat))))
    (h5 : 48 ≤ s)
    (h6 : (0 ≤ pixs ∧ pixs < (2 ^ (64 : Nat))))
    (h7 : (s % 8) = 0)
    (h8 : (s + OFF2) ≤ (s + (-40)))
    (h9 : ((s + (-40)) + 8) ≤ (c_top C))
    (h10 : (s + OFF3) ≤ (s + (-48))) :
    ((s + (-48)) + 8) ≤ (c_top C) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Leptonica/VL/LeptPixCreate.v (replace)
example
    {T1 T2 : Type}
    (C : T1)
    (s : Int)
    (w : Int)
    (h_1 : Int)
    (d : Int)
    (u : T2 → Int)
    (x : T2)
    (pix : Int)
    (c_top : T1 → Int)
    (LSTK : Int)
    (LSF : Int)
    (h1 : (s % 16) = 0)
    (h2 : ((((c_top C) - LSTK) + 96) + LSF) ≤ s)
    (h3 : s ≤ (c_top C))
    (h4 : (1 ≤ w ∧ w ≤ 1000000))
    (h5 : (1 ≤ h_1 ∧ h_1 ≤ 1000000))
    (h6 : (w * h_1) ≤ 400000000)
    (h7 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h8 : (pix % 8) = 0) :
    (u x) = (pix + ((u x) - pix)) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Mallocng/MallocInv_agnest2.v (replace)
example
    {word T2 T3 T4 T5 T6 T7 T8 T9 T10 : Type}
    (m : Int)
    (bv_unsigned : word → Int)
    (a : word)
    (mt_mem : T2 → Int)
    (mt : T2)
    (idx : Int)
    (mt_stride : T2 → Int)
    (p0 : T2 → Int → Int)
    (ne : T2 → Int → Int)
    (nA3 : T3 → T4 → T5 → T2 → T6 → T7 → Int → T8)
    (A1 : T3)
    (j : T4)
    (gj : T5)
    (aib : T6)
    (slots : T7)
    (sc : T9)
    (cnt1 : Int)
    (a_ctx : T8 → T10 → Int)
    (KActive : T9 → T10)
    (KUsage : T9 → T10)
    (h1 : (((mt_mem mt) + 16) + (idx * (mt_stride mt))) = (p0 mt idx))
    (h2 : (((p0 mt idx) + (mt_stride mt)) - 4) = (ne mt idx))
    (h3 : (a_ctx (nA3 A1 j gj mt aib slots idx) (KActive sc)) = 0)
    (h4 : ((a_ctx (nA3 A1 j gj mt aib slots idx) (KUsage sc)) + cnt1) < (2 ^ (63 : Nat))) :
    (m + ((bv_unsigned a) - m)) = (bv_unsigned a) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Mallocng/MallocInv_env.v (replace)
example (a : Int) (LOCKA : Int) (h1 : (0 ≤ (a - LOCKA) ∧ (a - LOCKA) < 8)) :
    a = (LOCKA + (a - LOCKA)) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Mallocng/MallocInv_heap.v (replace)
example
    (a : Int)
    (n : Nat)
    (k : Int)
    (h1 : 0 ≤ a)
    (h2 : (a + ((n : Nat) : Int)) ≤ (2 ^ (64 : Nat))) :
    (a + (k + 1)) = ((a + 1) + k) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Mallocng/MallocInv_heap.v (replace)
example
    {T1 : Type}
    (x : Int)
    (n : Nat)
    (bv_unsigned : T1 → Int)
    (y : T1)
    (h1 : (0 ≤ x ∧ x < (2 ^ (64 : Nat))))
    (h2 : (x + ((n : Nat) : Int)) ≤ (2 ^ (64 : Nat))) :
    (x + ((bv_unsigned y) - x)) = (bv_unsigned y) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Mallocng/MallocInv_heap.v (replace)
example
    (a : Int)
    (n : Nat)
    (k : Int)
    (h1 : 0 ≤ a)
    (h2 : (a + ((n : Nat) : Int)) ≤ (2 ^ (64 : Nat)))
    (h3 : (0 ≤ k ∧ k < ((n : Nat) : Int))) :
    k = ((a + k) - a) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Mallocng/MallocInv_tav4.v (replace)
example
    (aib : Int)
    (Zpow : Int → Int → Int)
    (h1 : (0 ≤ aib ∧ aib < (2 ^ (64 : Nat))))
    (h2 : (0 < (Zpow 2 ((aib % 32) + 1)) ∧ (Zpow 2 ((aib % 32) + 1)) ≤ (2 ^ (32 : Nat)))) :
    ((Zpow 2 ((aib % 32) + 1)) - 1) = ((Zpow 2 ((aib % 32) + 1)) + (-1)) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Musl/PFLept.v (assert)
example (q : Int) (h1 : (0 ≤ q ∧ q < 7)) :
    (q = 0 ∨ (q = 1 ∨ (q = 2 ∨ (q = 3 ∨ (q = 4 ∨ (q = 5 ∨ q = 6)))))) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/Common/Musl/PFLept.v (replace)
example (sp0 : Int) :
    (sp0 - 48) = ((sp0 - 56) + (8 * 1)) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/K5/A16/F_printf_core_flags.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (X1 : Int)
    (N1 : Int)
    (X2 : Int)
    (N2 : Int)
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
    (SHADOW_LO : Int)
    (SHADOW_HI : Int)
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 806912)
    (h5 : ((838672 ≤ Fp ∧ (Fp + 232) ≤ 848640) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6442640 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 6451200)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : ((AP + 8) ≤ X1 ∧ ((X1 + N1) ≤ VA ∧ 0 ≤ N1)))
    (h8 : (6451200 ≤ X2 ∧ ((X2 + N2) ≤ lo ∧ (0 ≤ N2 ∧ ((X2 + N2) ≤ SHADOW_LO ∨ SHADOW_HI ≤ X2)))))
    (h9 : q ≤ AP)
    (h10 : (AP + 8) ≤ VA)
    (h11 : 0 ≤ A)
    (h12 : 0 ≤ BS)
    (h13 : (p + k) < (zlength fmt))
    (h14 : (32 ≤ (znth fmt (p + k)) ∧ (znth fmt (p + k)) < 64)) :
    ((p + k) + 1) = (p + (k + 1)) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/K5/A16/HandoffImage.v (replace)
example
    {acs Model word T4 : Type}
    (ch : acs)
    (model : Model)
    (a : Int)
    (bv_unsigned : word → Int)
    (vm_init_sp : T4 → word)
    (m_vmmaps : Model → T4)
    (hs_stk_ok : acs → Bool)
    (h1 : (hs_stk_ok ch) = true) :
    a = ((bv_unsigned (vm_init_sp (m_vmmaps model))) + (a - (bv_unsigned (vm_init_sp (m_vmmaps model))))) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/K5/B16/LeptC_deser2.v (replace)
example
    {T1 : Type}
    (fr : Int)
    (lo : Int)
    (data : Int)
    (rs : Int)
    (nc : Int)
    (length : T1 → Nat)
    (sbs : T1)
    (dp : Int)
    (h1 : (fr + 128) ≤ 140737488355328)
    (h2 : (nc ≠ 0 → 0 < nc))
    (h3 : (((length sbs) : Nat) : Int) = rs)
    (h4 : rs ≤ 67108864)
    (h5 : (0 ≤ data ∧ data ≤ (2 ^ (47 : Nat))))
    (h6 : (0 ≤ ((dp + (4 * nc)) + 28) ∧ ((dp + (4 * nc)) + 28) ≤ (2 ^ (47 : Nat))))
    (h7 : ((data + rs) ≤ ((dp + (4 * nc)) + 28) ∨ (((dp + (4 * nc)) + 28) + rs) ≤ data))
    (h8 : (((dp + (4 * nc)) + 28) + rs) ≤ lo) :
    (fr + 36) = ((fr + 32) + 4) := by
  lia

-- leptonica/jpegiostub_fuzzer: lib/K5/G3/LeptModel.v (replace)
example
    (i : Int)
    (h1 : (Int.fmod i (2 ^ (64 : Nat))) = (i + (2 ^ (64 : Nat))))
    (h2 : (Int.fmod (-(i + (2 ^ (64 : Nat)))) (2 ^ (64 : Nat))) = (-i)) :
    ((-i) + ((-1) * (2 ^ (64 : Nat)))) = (-(i + (2 ^ (64 : Nat)))) := by
  lia

-- leptonica/kernel_fuzzer: lib/Common/Mallocng/MallocInv_ameta5x.v (assert)
example
    {T1 : Type}
    (p : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (n : T1)
    (h1 : (bv_unsigned n) = 4096)
    (h2 : ((p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 4096)) ∨ (¬ (p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 4096))))) :
    ((p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 4096)) ∨ (¬ (p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 4096)))) := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/A17/F_memchr.v (replace)
example
    {word : Type}
    (a2 : word)
    (j : Nat)
    (b : Int)
    (bv_unsigned : word → Int)
    (i : Int)
    (h1 : (Int.toNat ((bv_unsigned a2) - b)) = j) :
    ((bv_unsigned a2) - (i + 8)) = (((bv_unsigned a2) - i) + (-8)) := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/A17/Km_create.v (replace)
example
    (h_1 : Int)
    (mcost : Int → Int)
    (km_cost : Int → Int → Int)
    (w : Int)
    (h1 : (0 ≤ (mcost (8 * h_1)) ∧ (mcost (8 * h_1)) ≤ (km_cost h_1 w)))
    (h2 : 0 ≤ (mcost (4 * w))) :
    (8 * h_1) = (h_1 * 8) := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/A17/Km_getpixel.v (assert)
example
    {T1 T2 : Type}
    (X : Int)
    (pv : Int)
    (lo : Int)
    (pix : Int)
    (p_data : T1 → Int)
    (v : T1)
    (rsize : T1 → Int)
    (usp : Int)
    (p_wpl : T1 → Int)
    (y : Int)
    (p_h : T1 → Int)
    (p_w : T1 → Int)
    (shb11 : T2)
    (bv_unsigned : T2 → Int)
    (h1 : ((pv + 4) ≤ lo ∧ (((pv + 4) ≤ pix ∨ (pix + 64) ≤ pv) ∧ ((pv + 4) ≤ (p_data v) ∨ ((p_data v) + (rsize v)) ≤ pv))))
    (h2 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h3 : ((usp % 32) = 0 ∨ (usp % 32) = 16))
    (h4 : ((pv + 4) ≤ pix ∨ (pix + 64) ≤ pv))
    (h5 : (0 < (p_wpl v) ∧ (p_wpl v) ≤ 20000))
    (h6 : (0 ≤ ((p_wpl v) * y) ∧ (((p_wpl v) * y) + (p_wpl v)) ≤ ((p_wpl v) * (p_h v))))
    (h7 : (p_w v) ≤ (4 * (p_wpl v)))
    (h8 : (p_data v) ≤ X)
    (h9 : (X + 1) ≤ ((p_data v) + (4 * ((p_wpl v) * (p_h v)))))
    (h10 : ((X - (X % 4)) + 4) ≤ ((p_data v) + (4 * ((p_wpl v) * (p_h v)))))
    (h11 : 0 ≤ X)
    (h12 : (0 ≤ (bv_unsigned shb11) ∧ (bv_unsigned shb11) < 8))
    (h13 : 0 ≤ ((4 * (X / 4)) + (3 - (X % 4))))
    (h14 : (((4 * (X / 4)) + (3 - (X % 4))) % 8) < (bv_unsigned shb11))
    (h15 : ((p_data v) ≤ ((4 * (X / 4)) + (3 - (X % 4))) ∧ (((4 * (X / 4)) + (3 - (X % 4))) + 1) ≤ ((p_data v) + (4 * ((p_wpl v) * (p_h v)))))) :
    0 ≤ X := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/A17/LeptL_gmax_loop.v (replace)
example
    {list_byte : Type}
    (k : Nat)
    (j : Int)
    (data : Int)
    (n : Int)
    (line : Int)
    (w : Int)
    (c : Int)
    (bs : list_byte)
    (length : list_byte → Nat)
    (h1 : ((k : Nat) : Int) = (w - j))
    (h2 : c = (w - j))
    (h3 : 0 ≤ j)
    (h4 : 1 ≤ k)
    (h5 : data ≤ line)
    (h6 : (line % 4) = 0)
    (h7 : (line + (4 * ((w + 3) / 4))) ≤ (data + n))
    (h8 : 0 < data)
    (h9 : (data % 8) = 0)
    (h10 : (data + n) ≤ (2 ^ (47 : Nat)))
    (h11 : ((data + n) ≤ 2147446784 ∨ 17594333495296 ≤ data))
    (h12 : (((length bs) : Nat) : Int) = n) :
    (w - (j + 1)) = ((w - j) + (-1)) := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/A17/LeptL_gmax_loop.v (replace)
example
    {list_byte : Type}
    (k : Nat)
    (j : Int)
    (data : Int)
    (n : Int)
    (line : Int)
    (w : Int)
    (c : Int)
    (bs : list_byte)
    (length : list_byte → Nat)
    (h1 : ((k : Nat) : Int) = (w - j))
    (h2 : c = (w - j))
    (h3 : 0 ≤ j)
    (h4 : 1 ≤ k)
    (h5 : data ≤ line)
    (h6 : (line % 4) = 0)
    (h7 : (line + (4 * ((w + 3) / 4))) ≤ (data + n))
    (h8 : 0 < data)
    (h9 : (data % 8) = 0)
    (h10 : (data + n) ≤ (2 ^ (47 : Nat)))
    (h11 : ((data + n) ≤ 2147446784 ∨ 17594333495296 ≤ data))
    (h12 : (((length bs) : Nat) : Int) = n) :
    (line + (j + 1)) = ((line + j) + 1) := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/A17/LeptL_gmax_loop.v (replace)
example
    {list_byte : Type}
    (k : Nat)
    (j : Int)
    (data : Int)
    (n : Int)
    (line : Int)
    (w : Int)
    (bs : list_byte)
    (length : list_byte → Nat)
    (h1 : ((k : Nat) : Int) = (w - j))
    (h2 : 0 ≤ j)
    (h3 : 1 ≤ k)
    (h4 : w ≤ (2 ^ (20 : Nat)))
    (h5 : data ≤ line)
    (h6 : (line % 4) = 0)
    (h7 : (line + (4 * ((w + 15) / 16))) ≤ (data + n))
    (h8 : 0 < data)
    (h9 : (data % 8) = 0)
    (h10 : (data + n) ≤ (2 ^ (47 : Nat)))
    (h11 : ((data + n) ≤ 2147446784 ∨ 17594333495296 ≤ data))
    (h12 : (((length bs) : Nat) : Int) = n)
    (h13 : (j + 1) = w) :
    (line + (4 * (j / 16))) = (data + ((line + (4 * (j / 16))) - data)) := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/B17/F_printf_core_dloop.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (X1 : Int)
    (N1 : Int)
    (X2 : Int)
    (N2 : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (j : Int)
    (zlength : list_Z → Int)
    (W' : list_Z)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (SHADOW_LO : Int)
    (SHADOW_HI : Int)
    (x : Int)
    (dec_digits : Int → list_Z)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 815104)
    (h5 : ((847696 ≤ Fp ∧ (Fp + 232) ≤ 856704) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6453328 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 6463488)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : ((AP + 8) ≤ X1 ∧ ((X1 + N1) ≤ VA ∧ 0 ≤ N1)))
    (h8 : (6463488 ≤ X2 ∧ ((X2 + N2) ≤ lo ∧ (0 ≤ N2 ∧ ((X2 + N2) ≤ SHADOW_LO ∨ SHADOW_HI ≤ X2)))))
    (h9 : q ≤ AP)
    (h10 : (AP + 8) ≤ VA)
    (h11 : 0 ≤ A)
    (h12 : 0 ≤ BS)
    (h13 : (x / 10) < 1844674407370955162)
    (h14 : 2 ≤ (zlength (dec_digits x))) :
    (Int.toNat (j - ((zlength W') + 1))) = (Int.toNat ((j - 1) - (zlength W'))) := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/B17/FrmRun.v (replace)
example
    {T1 word T3 : Type}
    (segs : T1)
    (a : word)
    (seg : T3)
    (j : Int)
    (rom_frm_ok : T1 → Bool)
    (seg_executable : T3 → Bool)
    (seg_base : T3 → Nat)
    (bv_unsigned : word → Int)
    (seg_size : T3 → Nat)
    (h1 : (rom_frm_ok segs) = true)
    (h2 : (seg_executable seg) = true)
    (h3 : ((((seg_base seg) : Nat) : Int) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < ((((seg_base seg) : Nat) : Int) + (((seg_size seg) : Nat) : Int))))
    (h4 : ((bv_unsigned a) % 2) = 0)
    (h5 : (bv_unsigned a) = ((((seg_base seg) : Nat) : Int) + (2 * j)))
    (h6 : 0 ≤ j) :
    (((Int.toNat j) : Nat) : Int) = j := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/B17/Km_frompix.v (assert)
example
    {T1 : Type}
    (lo : Int)
    (usp : Int)
    (p_d : T1 → Int)
    (v : T1)
    (p_w : T1 → Int)
    (p_h : T1 → Int)
    (p_wpl : T1 → Int)
    (kel : Int)
    (pix : Int)
    (p_data : T1 → Int)
    (data : Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : ((usp % 32) = 0 ∨ (usp % 32) = 16))
    (h3 : (1 ≤ (p_d v) ∧ (p_d v) ≤ 32))
    (h4 : ((p_w v) * (p_h v)) ≤ (2 ^ (26 : Nat)))
    (h5 : (p_w v) ≤ (4 * (p_wpl v)))
    (h6 : 0 ≤ ((p_w v) * (p_h v)))
    (h7 : ((kel + 24) ≤ pix ∨ (pix + 64) ≤ kel))
    (h8 : ((kel + 24) ≤ (p_data v) ∨ ((p_data v) + (4 * ((p_wpl v) * (p_h v)))) ≤ kel))
    (h9 : ((kel + 24) ≤ data ∨ (data + (8 * (p_h v))) ≤ kel))
    (h10 : 0 ≤ lo) :
    0 ≤ lo := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/B17/Km_getpixel.v (assert)
example
    {T1 T2 : Type}
    (X : Int)
    (pv : Int)
    (lo : Int)
    (pix : Int)
    (p_data : T1 → Int)
    (v : T1)
    (rsize : T1 → Int)
    (usp : Int)
    (p_wpl : T1 → Int)
    (y : Int)
    (p_h : T1 → Int)
    (p_w : T1 → Int)
    (shb11 : T2)
    (bv_unsigned : T2 → Int)
    (h1 : ((pv + 4) ≤ lo ∧ (((pv + 4) ≤ pix ∨ (pix + 64) ≤ pv) ∧ ((pv + 4) ≤ (p_data v) ∨ ((p_data v) + (rsize v)) ≤ pv))))
    (h2 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h3 : ((usp % 32) = 0 ∨ (usp % 32) = 16))
    (h4 : ((pv + 4) ≤ pix ∨ (pix + 64) ≤ pv))
    (h5 : (0 < (p_wpl v) ∧ (p_wpl v) ≤ 20000))
    (h6 : (0 ≤ ((p_wpl v) * y) ∧ (((p_wpl v) * y) + (p_wpl v)) ≤ ((p_wpl v) * (p_h v))))
    (h7 : (0 ≤ (y * (p_wpl v)) ∧ (y * (p_wpl v)) < (2 ^ (24 : Nat))))
    (h8 : (p_w v) ≤ (4 * (p_wpl v)))
    (h9 : (p_data v) ≤ X)
    (h10 : (X + 1) ≤ ((p_data v) + (4 * ((p_wpl v) * (p_h v)))))
    (h11 : ((X - (X % 4)) + 4) ≤ ((p_data v) + (4 * ((p_wpl v) * (p_h v)))))
    (h12 : 0 ≤ X)
    (h13 : (0 ≤ (bv_unsigned shb11) ∧ (bv_unsigned shb11) < 8))
    (h14 : 0 ≤ ((4 * (X / 4)) + (3 - (X % 4))))
    (h15 : (((4 * (X / 4)) + (3 - (X % 4))) % 8) < (bv_unsigned shb11))
    (h16 : ((p_data v) ≤ ((4 * (X / 4)) + (3 - (X % 4))) ∧ (((4 * (X / 4)) + (3 - (X % 4))) + 1) ≤ ((p_data v) + (4 * ((p_wpl v) * (p_h v)))))) :
    0 ≤ X := by
  lia

-- leptonica/kernel_fuzzer: lib/K5/B17/Lept_create.v (replace)
example
    (usp : Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : ((usp % 32) = 16 ∨ (usp % 32) = 0)) :
    (usp + (-48)) = ((usp + (-32)) + (-16)) := by
  lia

-- leptonica/kernel_fuzzer: lib/O17/O17LeptDeser.v (replace)
example
    {T1 T2 : Type}
    (C : T1)
    (s : Int)
    (kR : Int)
    (bR : Int)
    (dp : Int)
    (pl : T2)
    (nc : Int)
    (w : Int)
    (h_1 : Int)
    (d : Int)
    (cm : Int)
    (RK_deser : Int)
    (RB_deser : Int)
    (c_top : T1 → Int)
    (LSTK : Int)
    (LSF : Int)
    (wpl_of : Int → Int → Int)
    (length : T2 → Nat)
    (n : Int)
    (bs : T2)
    (h1 : RK_deser ≤ kR)
    (h2 : RB_deser ≤ bR)
    (h3 : (s % 16) = 0)
    (h4 : ((((c_top C) - LSTK) + 256) + LSF) ≤ s)
    (h5 : s ≤ (c_top C))
    (h6 : (0 ≤ nc ∧ nc ≤ 256))
    (h7 : (((4 * nc) + 28) + (4 * ((wpl_of w d) * h_1))) = (((length pl) : Nat) : Int))
    (h8 : 1 ≤ w)
    (h9 : 1 ≤ h_1)
    (h10 : (nc = 0 ↔ cm = 0))
    (h11 : n = (4 * ((wpl_of w d) * h_1)))
    (h12 : (length bs) = (Int.toNat n)) :
    (dp + (((Int.toNat ((4 * nc) + 28)) : Nat) : Int)) = ((dp + (4 * nc)) + 28) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Leptonica/OL/MaxIndex.v (replace)
example
    {T1 T2 T3 : Type}
    (pix : Int)
    (pmax : Int)
    (w : Int)
    (h_1 : Int)
    (d : Int)
    (wpl : Int)
    (data : Int)
    (sp : Int)
    (i : Int)
    (SEGS : T1)
    (M : T2)
    (Z_to_bv : Nat → Int → T3)
    (store_ok : T1 → T2 → T3 → Nat → Bool)
    (h1 : (1 ≤ pix ∧ (pix + 64) ≤ (2 ^ (64 : Nat))))
    (h2 : (1 ≤ pmax ∧ (pmax + 4) ≤ (2 ^ (64 : Nat))))
    (h3 : (0 ≤ w ∧ w < (2 ^ (32 : Nat))))
    (h4 : (0 ≤ h_1 ∧ h_1 < (2 ^ (32 : Nat))))
    (h5 : (0 ≤ d ∧ d < (2 ^ (32 : Nat))))
    (h6 : (0 ≤ wpl ∧ wpl < (2 ^ (32 : Nat))))
    (h7 : (1 ≤ w ∧ w ≤ 20000))
    (h8 : (1 ≤ h_1 ∧ h_1 ≤ 20000))
    (h9 : (d = 1 ∨ (d = 2 ∨ (d = 4 ∨ d = 8))))
    (h10 : wpl = (((w * d) + 31) / 32))
    (h11 : (4 ≤ data ∧ data < (2 ^ (64 : Nat))))
    (h12 : (data % 4) = 0)
    (h13 : (144 ≤ sp ∧ sp < (2 ^ (64 : Nat))))
    (h14 : (data + (4 * (wpl * h_1))) ≤ (2 ^ (64 : Nat)))
    (h15 : (store_ok SEGS M (Z_to_bv 64 pmax) 4) = true)
    (h16 : ((pmax + 4) ≤ pix ∨ (pix + 64) ≤ pmax))
    (h17 : ((pmax + 4) ≤ (sp - 144) ∨ sp ≤ pmax))
    (h18 : ((pix + 64) ≤ (sp - 144) ∨ sp ≤ pix)) :
    (data + ((wpl * i) * 4)) = (data + ((4 * wpl) * i)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Mallocng/MallocInv_agroot.v (replace)
example
    {mstate meta_rec T3 T4 T5 : Type}
    (s1 : mstate)
    (sc : Int)
    (req : Int)
    (m : Int)
    (md : meta_rec)
    (p : Int)
    (L : Int)
    (cnt : Int)
    (aidx : Int)
    (mt_f : meta_rec → T3 → Int)
    (FW32 : T3)
    (region_free : T4 → meta_rec → meta_rec → Bool)
    (vm_noaccess : T5 → T4)
    (ms_vm : mstate → T5)
    (Z_to_bv : Int → Int → meta_rec)
    (size_class : Int → Int)
    (h1 : (mt_f md FW32) = L)
    (h2 : (0 ≤ sc ∧ sc < 48))
    (h3 : 0 < L)
    (h4 : (L % 4096) = 0)
    (h5 : (region_free (vm_noaccess (ms_vm s1)) (Z_to_bv 64 p) (Z_to_bv 64 L)) = true)
    (h6 : (1 ≤ cnt ∧ cnt ≤ 32))
    (h7 : ((16 * (size_class sc)) * cnt) < (2 ^ (20 : Nat)))
    (h8 : (1 < cnt → (((16 * (size_class sc)) * cnt) + 16) ≤ L))
    (h9 : (cnt = 1 → (req + 20) ≤ L))
    (h10 : 0 ≤ req)
    (h11 : (0 ≤ aidx ∧ aidx ≤ (cnt - 1)))
    (h12 : (cnt = 1 → (256 ≤ (size_class sc) ∨ (L - 16) ≤ (16 * (size_class sc)))))
    (h13 : (cnt = 1 → L < ((2 ^ (20 : Nat)) + 16)))
    (h14 : (aidx < (cnt - 1) → 7 ≤ sc)) :
    (m + (p - m)) = p := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Mallocng/MallocInv_agroot.v (replace)
example
    {mstate meta_rec T3 T4 T5 : Type}
    (s1 : mstate)
    (sc : Int)
    (req : Int)
    (m : Int)
    (md : meta_rec)
    (p : Int)
    (L : Int)
    (cnt : Int)
    (aidx : Int)
    (mt_f : meta_rec → T3 → Int)
    (FW32 : T3)
    (region_free : T4 → meta_rec → meta_rec → Bool)
    (vm_noaccess : T5 → T4)
    (ms_vm : mstate → T5)
    (Z_to_bv : Int → Int → meta_rec)
    (size_class : Int → Int)
    (h1 : (mt_f md FW32) = L)
    (h2 : (0 ≤ sc ∧ sc < 48))
    (h3 : 0 < L)
    (h4 : (L % 4096) = 0)
    (h5 : (region_free (vm_noaccess (ms_vm s1)) (Z_to_bv 64 p) (Z_to_bv 64 L)) = true)
    (h6 : (1 ≤ cnt ∧ cnt ≤ 32))
    (h7 : ((16 * (size_class sc)) * cnt) < (2 ^ (20 : Nat)))
    (h8 : (1 < cnt → (((16 * (size_class sc)) * cnt) + 16) ≤ L))
    (h9 : (cnt = 1 → (req + 20) ≤ L))
    (h10 : 0 ≤ req)
    (h11 : (0 ≤ aidx ∧ aidx ≤ (cnt - 1)))
    (h12 : (cnt = 1 → (256 ≤ (size_class sc) ∨ (L - 16) ≤ (16 * (size_class sc)))))
    (h13 : (cnt = 1 → L < ((2 ^ (20 : Nat)) + 16)))
    (h14 : (aidx < (cnt - 1) → 7 ≤ sc)) :
    (m + 0) = m := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Musl/PFCoreTop.v (replace)
example
    {list_Z T2 : Type}
    (fa : Int)
    (fbs : list_Z)
    (length : list_Z → Nat)
    (bs : list_Z)
    (IMG_LO : Int)
    (IMG_TOP : Int)
    (nth : Nat → list_Z → Int → Int)
    (n : Int)
    (rem : T2 → Int)
    (rest : T2)
    (p : Int)
    (fbyte : Int → Int)
    (flat : T2 → list_Z)
    (h1 : (IMG_LO ≤ fa ∧ (fa + (((length fbs) : Nat) : Int)) ≤ IMG_TOP))
    (h2 : 1 ≤ n)
    (h3 : 0 ≤ (rem rest))
    (h4 : (fbyte (p + n)) = (nth 0 (flat rest) 0))
    (h5 : ((nth 0 (flat rest) 0) = 0 ∨ ((nth 0 (flat rest) 0) = 37 ∧ (((p + n) + 1) < (fa + (((length fbs) : Nat) : Int)) ∧ (fbyte ((p + n) + 1)) ≠ 37)))) :
    1 = (((length bs) + 1) - (length bs)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Musl/PFCoreTop.v (replace)
example
    {list_Z T2 T3 : Type}
    (fa : Int)
    (fbs : list_Z)
    (p : Int)
    (IMG_LO : Int)
    (length : list_Z → Nat)
    (IMG_TOP : Int)
    (nth : Nat → list_Z → Int → Int)
    (n : Int)
    (rem : T2 → Int)
    (rest : T2)
    (fbyte : Int → Int)
    (flat : T2 → list_Z)
    (conv_len : T3 → Int)
    (c' : T3)
    (c : T3)
    (h1 : (IMG_LO ≤ fa ∧ (fa + (((length fbs) : Nat) : Int)) ≤ IMG_TOP))
    (h2 : 1 ≤ n)
    (h3 : 0 ≤ (rem rest))
    (h4 : (fbyte (p + n)) = (nth 0 (flat rest) 0))
    (h5 : ((nth 0 (flat rest) 0) = 0 ∨ ((nth 0 (flat rest) 0) = 37 ∧ (((p + n) + 1) < (fa + (((length fbs) : Nat) : Int)) ∧ (fbyte ((p + n) + 1)) ≠ 37))))
    (h6 : 2 ≤ (conv_len c'))
    (h7 : (2 ≤ (conv_len c) ∧ (conv_len c) ≤ 3))
    (h8 : (IMG_LO ≤ p ∧ (p + (conv_len c)) < IMG_TOP)) :
    (p + 1) = (p + ((1 : Nat) : Int)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Musl/PFSnw.v (replace)
example
    {T1 : Type}
    (sp0 : Int)
    (sp : Int)
    (u : Int)
    (j : Int)
    (s : Int)
    (l : Int)
    (k : Int)
    (FR : Int)
    (length : T1 → Nat)
    (bs1 : T1)
    (h1 : (((sp0 - FR) + 64) ≤ sp ∧ sp ≤ (sp0 - 2768)))
    (h2 : (0 ≤ u ∧ u ≤ 80))
    (h3 : (0 ≤ l ∧ l < (2 ^ (32 : Nat))))
    (h4 : (0 ≤ s ∧ ((s + l) ≤ (sp0 - FR) ∨ (sp ≤ s ∧ (s + l) ≤ (sp0 - 2768)))))
    (h5 : ((0 ≤ k ∧ k ≤ u) ∧ k ≤ (1999 - j)))
    (h6 : (length bs1) = (Int.toNat k)) :
    (((sp0 - 2080) + j) + k) = ((sp0 - 2080) + (j + k)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Musl/PFSnw.v (replace)
example
    {T1 : Type}
    (sp0 : Int)
    (sp : Int)
    (u : Int)
    (j : Int)
    (s : Int)
    (l : Int)
    (k : Int)
    (FR : Int)
    (length : T1 → Nat)
    (bs1 : T1)
    (h1 : (((sp0 - FR) + 64) ≤ sp ∧ sp ≤ (sp0 - 2768)))
    (h2 : (0 ≤ u ∧ u ≤ 80))
    (h3 : (0 ≤ l ∧ l < (2 ^ (32 : Nat))))
    (h4 : (0 ≤ s ∧ ((s + l) ≤ (sp0 - FR) ∨ (sp ≤ s ∧ (s + l) ≤ (sp0 - 2768)))))
    (h5 : ((0 ≤ k ∧ k ≤ u) ∧ k ≤ (1999 - j)))
    (h6 : (length bs1) = (Int.toNat k)) :
    ((1999 - j) - k) = (1999 - (j + k)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Musl/PFSnw.v (replace)
example
    {list_byte : Type}
    (sp0 : Int)
    (sp : Int)
    (u : Int)
    (s : Int)
    (l : Int)
    (j1 : Int)
    (k2 : Int)
    (FR : Int)
    (length : list_byte → Nat)
    (bs2 : list_byte)
    (h1 : (((sp0 - FR) + 64) ≤ sp ∧ sp ≤ (sp0 - 2768)))
    (h2 : (0 ≤ u ∧ u ≤ 80))
    (h3 : (0 ≤ l ∧ l < (2 ^ (32 : Nat))))
    (h4 : (0 ≤ s ∧ ((s + l) ≤ (sp0 - FR) ∨ (sp ≤ s ∧ (s + l) ≤ (sp0 - 2768)))))
    (h5 : ((0 ≤ k2 ∧ k2 ≤ l) ∧ k2 ≤ (1999 - j1)))
    (h6 : (length bs2) = (Int.toNat k2)) :
    (((sp0 - 2080) + j1) + k2) = ((sp0 - 2080) + (j1 + k2)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/Common/Musl/PFSnw.v (replace)
example
    {list_byte : Type}
    (sp0 : Int)
    (sp : Int)
    (u : Int)
    (s : Int)
    (l : Int)
    (j1 : Int)
    (k2 : Int)
    (FR : Int)
    (length : list_byte → Nat)
    (bs2 : list_byte)
    (h1 : (((sp0 - FR) + 64) ≤ sp ∧ sp ≤ (sp0 - 2768)))
    (h2 : (0 ≤ u ∧ u ≤ 80))
    (h3 : (0 ≤ l ∧ l < (2 ^ (32 : Nat))))
    (h4 : (0 ≤ s ∧ ((s + l) ≤ (sp0 - FR) ∨ (sp ≤ s ∧ (s + l) ≤ (sp0 - 2768)))))
    (h5 : ((0 ≤ k2 ∧ k2 ≤ l) ∧ k2 ≤ (1999 - j1)))
    (h6 : (length bs2) = (Int.toNat k2)) :
    ((1999 - j1) - k2) = (1999 - (j1 + k2)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/K5/A21/F_vfprintf_sn2.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) (CK : Int) (h1 : (bv_unsigned sp) ≤ CK) :
    ((bv_unsigned sp) + (-360)) = (((bv_unsigned sp) + (-368)) + ((8 : Nat) : Int)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/K5/A21/Pm_cmapvalid_stk.v (assert)
example
    (fr : Int)
    (pv : Int)
    (h1 : 0 < pv)
    (h2 : (pv % 8) ≤ 4)
    (h3 : 17594333495296 ≤ pv)
    (h4 : (fr + 64) ≤ pv)
    (h5 : (((fr / 8) + 2147450880) + 8) ≤ pv) :
    (fr + 64) ≤ pv := by
  lia

-- leptonica/paintcmap_fuzzer: lib/K5/A21/RT_release.v (replace)
example
    (fs_size : Nat → Int)
    (k : Nat)
    (shad : Int → Int)
    (f : Int)
    (SHB : Int)
    (fa : Int)
    (n : Int)
    (c : Nat)
    (fsz : Int → Int)
    (h1 : (((k : Nat) : Int) = 0 ∨ (((k : Nat) : Int) = 1 ∨ (((k : Nat) : Int) = 6 ∨ ((k : Nat) : Int) = 2))))
    (h2 : SHB ≤ (shad fa))
    (h3 : ((shad fa) + (n / 8)) ≤ ((2 ^ (44 : Nat)) + SHB))
    (h4 : (((fa / 8) * 8) + ((n / 8) * 8)) ≤ (fa + n))
    (h5 : ((fa / 8) + (n / 8)) ≤ (2 ^ (44 : Nat)))
    (h6 : (((fa / 8) + (n / 8)) * 8) ≤ (2 ^ (47 : Nat)))
    (h7 : (((c : Nat) : Int) = 0 ∨ (((c : Nat) : Int) = 1 ∨ (((c : Nat) : Int) = 6 ∨ ((c : Nat) : Int) = 2))))
    (h8 : ((c : Nat) : Int) ≠ ((k : Nat) : Int))
    (h9 : (fsz ((k : Nat) : Int)) = (fs_size k))
    (h10 : 0 < (fs_size k))
    (h11 : 0 ≤ ((fs_size k) / 8)) :
    ((fs_size k) / 8) = (((shad f) + ((fs_size k) / 8)) - (shad f)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/K5/B21/RT_malsec_art.v (assert)
example (c : Int) (h1 : ((c * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (2 ^ (37 : Nat))) :
    ((c * (2 ^ (32 : Nat))) + (2 ^ (32 : Nat))) ≤ (2 ^ (37 : Nat)) := by
  lia

-- leptonica/paintcmap_fuzzer: lib/V21/V21LeptSelLoop.v (replace)
example
    {list_byte : Type}
    (datas : Int)
    (w : Int)
    (h_1 : Int)
    (d : Int)
    (wpl : Int)
    (s : Int)
    (x1 : Int)
    (y1 : Int)
    (ibs : list_byte)
    (i : Int)
    (length : list_byte → Nat)
    (h1 : (1 ≤ w ∧ w ≤ 20000))
    (h2 : (1 ≤ h_1 ∧ h_1 ≤ 20000))
    (h3 : (d = 1 ∨ (d = 2 ∨ (d = 4 ∨ d = 8))))
    (h4 : wpl = (((w * d) + 31) / 32))
    (h5 : 4096 ≤ datas)
    (h6 : (datas % 4) = 0)
    (h7 : (144 ≤ s ∧ s < (2 ^ (64 : Nat))))
    (h8 : (datas + (4 * (wpl * h_1))) ≤ (s - 144))
    (h9 : (0 ≤ x1 ∧ x1 < ((2 ^ (31 : Nat)) - 1)))
    (h10 : (0 ≤ y1 ∧ y1 < ((2 ^ (31 : Nat)) - 1)))
    (h11 : (length ibs) = 4) :
    (datas + ((wpl * i) * 4)) = (datas + ((4 * wpl) * i)) := by
  lia

-- leptonica/pix1_fuzzer: lib/Common/Mallocng/MallocInv_ameta3.v (assert)
example
    {T1 T2 T3 : Type}
    (p : Int)
    (x : Int)
    (LOCKA : Int)
    (tl : Int)
    (a_ctx : T1 → T2 → Int)
    (A : T1)
    (KAtail : T2)
    (bv_unsigned : T3 → Int)
    (a : T3)
    (h1 : (a_ctx A KAtail) < (2 ^ (64 : Nat)))
    (h2 : ((p ≤ x ∧ x < (p + 40)) ∨ (((LOCKA + 32) ≤ x ∧ x < (LOCKA + 56)) ∨ (((LOCKA + 64) ≤ x ∧ x < (LOCKA + 88)) ∨ ((¬ (p ≤ x ∧ x < (p + 40))) ∧ ((¬ ((LOCKA + 32) ≤ x ∧ x < (LOCKA + 56))) ∧ (¬ ((LOCKA + 64) ≤ x ∧ x < (LOCKA + 88)))))))))
    (h3 : ((p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 40)) ∨ (((LOCKA + 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 56)) ∨ (((LOCKA + 64) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 88)) ∨ ((¬ (p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 40))) ∧ ((¬ ((LOCKA + 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 56))) ∧ (¬ ((LOCKA + 64) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 88))))))))) :
    ((p ≤ x ∧ x < (p + 40)) ∨ (((LOCKA + 32) ≤ x ∧ x < (LOCKA + 56)) ∨ (((LOCKA + 72) ≤ x ∧ x < (LOCKA + 88)) ∨ (((tl + 8) ≤ x ∧ x < (tl + 16)) ∨ ((¬ (p ≤ x ∧ x < (p + 40))) ∧ ((¬ ((LOCKA + 32) ≤ x ∧ x < (LOCKA + 56))) ∧ ((¬ ((LOCKA + 72) ≤ x ∧ x < (LOCKA + 88))) ∧ (¬ ((tl + 8) ≤ x ∧ x < (tl + 16)))))))))) := by
  lia

-- leptonica/pix1_fuzzer: lib/Common/Mallocng/MallocInv_ameta3.v (assert)
example
    {T1 T2 T3 : Type}
    (p : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (LOCKA : Int)
    (tl : Int)
    (a_ctx : T2 → T3 → Int)
    (A : T2)
    (KAtail : T3)
    (x : Int)
    (h1 : (a_ctx A KAtail) < (2 ^ (64 : Nat)))
    (h2 : ((p ≤ x ∧ x < (p + 40)) ∨ (((LOCKA + 32) ≤ x ∧ x < (LOCKA + 56)) ∨ (((LOCKA + 64) ≤ x ∧ x < (LOCKA + 88)) ∨ ((¬ (p ≤ x ∧ x < (p + 40))) ∧ ((¬ ((LOCKA + 32) ≤ x ∧ x < (LOCKA + 56))) ∧ (¬ ((LOCKA + 64) ≤ x ∧ x < (LOCKA + 88)))))))))
    (h3 : ((p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 40)) ∨ (((LOCKA + 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 56)) ∨ (((LOCKA + 64) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 88)) ∨ ((¬ (p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 40))) ∧ ((¬ ((LOCKA + 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 56))) ∧ (¬ ((LOCKA + 64) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 88)))))))))
    (h4 : ((p ≤ x ∧ x < (p + 40)) ∨ (((LOCKA + 32) ≤ x ∧ x < (LOCKA + 56)) ∨ (((LOCKA + 72) ≤ x ∧ x < (LOCKA + 88)) ∨ (((tl + 8) ≤ x ∧ x < (tl + 16)) ∨ ((¬ (p ≤ x ∧ x < (p + 40))) ∧ ((¬ ((LOCKA + 32) ≤ x ∧ x < (LOCKA + 56))) ∧ ((¬ ((LOCKA + 72) ≤ x ∧ x < (LOCKA + 88))) ∧ (¬ ((tl + 8) ≤ x ∧ x < (tl + 16))))))))))) :
    ((p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 40)) ∨ (((LOCKA + 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 56)) ∨ (((LOCKA + 72) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 88)) ∨ (((tl + 8) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (tl + 16)) ∨ ((¬ (p ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (p + 40))) ∧ ((¬ ((LOCKA + 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 56))) ∧ ((¬ ((LOCKA + 72) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (LOCKA + 88))) ∧ (¬ ((tl + 8) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (tl + 16)))))))))) := by
  lia

-- leptonica/pix1_fuzzer: lib/Common/Mallocng/MallocInv_tav1.v (assert)
example
    (h_1 : Int)
    (x : Int)
    (PM : Int)
    (xn : Int)
    (xp : Int)
    (h1 : (0 ≤ xn ∧ xn < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ xp ∧ xp < (2 ^ (64 : Nat)))) :
    ((h_1 ≤ x ∧ x < (h_1 + 16)) ∨ ((PM ≤ x ∧ x < (PM + 8)) ∨ ((¬ (h_1 ≤ x ∧ x < (h_1 + 16))) ∧ (¬ (PM ≤ x ∧ x < (PM + 8)))))) := by
  lia

-- leptonica/pix1_fuzzer: lib/Common/Mallocng/MallocInv_tav1.v (assert)
example
    {T1 : Type}
    (h_1 : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (PM : Int)
    (xn : Int)
    (xp : Int)
    (x : Int)
    (h1 : (0 ≤ xn ∧ xn < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ xp ∧ xp < (2 ^ (64 : Nat))))
    (h3 : ((h_1 ≤ x ∧ x < (h_1 + 16)) ∨ ((PM ≤ x ∧ x < (PM + 8)) ∨ ((¬ (h_1 ≤ x ∧ x < (h_1 + 16))) ∧ (¬ (PM ≤ x ∧ x < (PM + 8))))))) :
    ((h_1 ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (h_1 + 16)) ∨ ((PM ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (PM + 8)) ∨ ((¬ (h_1 ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (h_1 + 16))) ∧ (¬ (PM ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (PM + 8)))))) := by
  lia

-- leptonica/pix1_fuzzer: lib/Common/Mallocng/MallocInv_tav1.v (assert)
example
    {T1 : Type}
    (h_1 : Int)
    (x : Int)
    (PM : Int)
    (xn : Int)
    (xp : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (h1 : (0 ≤ xn ∧ xn < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ xp ∧ xp < (2 ^ (64 : Nat))))
    (h3 : ((h_1 ≤ x ∧ x < (h_1 + 16)) ∨ ((PM ≤ x ∧ x < (PM + 8)) ∨ ((¬ (h_1 ≤ x ∧ x < (h_1 + 16))) ∧ (¬ (PM ≤ x ∧ x < (PM + 8)))))))
    (h4 : ((h_1 ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (h_1 + 16)) ∨ ((PM ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (PM + 8)) ∨ ((¬ (h_1 ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (h_1 + 16))) ∧ (¬ (PM ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (PM + 8)))))))
    (h5 : (xn = xp ∨ ((xn + 40) ≤ xp ∨ (xp + 40) ≤ xn))) :
    ((h_1 ≤ x ∧ x < (h_1 + 16)) ∨ ((PM ≤ x ∧ x < (PM + 8)) ∨ ((xn ≤ x ∧ x < (xn + 8)) ∨ (((xp + 8) ≤ x ∧ x < (xp + 16)) ∨ ((¬ (h_1 ≤ x ∧ x < (h_1 + 16))) ∧ ((¬ (PM ≤ x ∧ x < (PM + 8))) ∧ ((¬ (xn ≤ x ∧ x < (xn + 8))) ∧ (¬ ((xp + 8) ≤ x ∧ x < (xp + 16)))))))))) := by
  lia

-- leptonica/pix1_fuzzer: lib/Common/Mallocng/MallocInv_tav1.v (assert)
example
    {T1 : Type}
    (h_1 : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (PM : Int)
    (xn : Int)
    (xp : Int)
    (x : Int)
    (h1 : (0 ≤ xn ∧ xn < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ xp ∧ xp < (2 ^ (64 : Nat))))
    (h3 : ((h_1 ≤ x ∧ x < (h_1 + 16)) ∨ ((PM ≤ x ∧ x < (PM + 8)) ∨ ((¬ (h_1 ≤ x ∧ x < (h_1 + 16))) ∧ (¬ (PM ≤ x ∧ x < (PM + 8)))))))
    (h4 : ((h_1 ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (h_1 + 16)) ∨ ((PM ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (PM + 8)) ∨ ((¬ (h_1 ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (h_1 + 16))) ∧ (¬ (PM ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (PM + 8)))))))
    (h5 : (xn = xp ∨ ((xn + 40) ≤ xp ∨ (xp + 40) ≤ xn)))
    (h6 : ((h_1 ≤ x ∧ x < (h_1 + 16)) ∨ ((PM ≤ x ∧ x < (PM + 8)) ∨ ((xn ≤ x ∧ x < (xn + 8)) ∨ (((xp + 8) ≤ x ∧ x < (xp + 16)) ∨ ((¬ (h_1 ≤ x ∧ x < (h_1 + 16))) ∧ ((¬ (PM ≤ x ∧ x < (PM + 8))) ∧ ((¬ (xn ≤ x ∧ x < (xn + 8))) ∧ (¬ ((xp + 8) ≤ x ∧ x < (xp + 16))))))))))) :
    ((h_1 ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (h_1 + 16)) ∨ ((PM ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (PM + 8)) ∨ ((xn ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (xn + 8)) ∨ (((xp + 8) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (xp + 16)) ∨ ((¬ (h_1 ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (h_1 + 16))) ∧ ((¬ (PM ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (PM + 8))) ∧ ((¬ (xn ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (xn + 8))) ∧ (¬ ((xp + 8) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (xp + 16)))))))))) := by
  lia

-- leptonica/pix1_fuzzer: lib/K5/B22/RT_init_mem.v (replace)
example {T1 T2 T3 : Type} (uE : T1 → T2 → Int) (E : T1) (eDNB : T3 → T2) (ch : T3) :
    ((uE E (eDNB ch)) + 32) = ((uE E (eDNB ch)) + (16 * (((1 : Nat) : Int) + 1))) := by
  lia

-- leptonica/pix1_fuzzer: lib/K5/B22/RT_release.v (replace)
example
    (fs_size : Nat → Int)
    (k : Nat)
    (shad : Int → Int)
    (f : Int)
    (SHB : Int)
    (fa : Int)
    (n : Int)
    (c : Nat)
    (fsz : Int → Int)
    (h1 : (((k : Nat) : Int) = 0 ∨ (((k : Nat) : Int) = 1 ∨ ((k : Nat) : Int) = 6)))
    (h2 : SHB ≤ (shad fa))
    (h3 : ((shad fa) + (n / 8)) ≤ ((2 ^ (44 : Nat)) + SHB))
    (h4 : (((fa / 8) * 8) + ((n / 8) * 8)) ≤ (fa + n))
    (h5 : ((fa / 8) + (n / 8)) ≤ (2 ^ (44 : Nat)))
    (h6 : (((fa / 8) + (n / 8)) * 8) ≤ (2 ^ (47 : Nat)))
    (h7 : (((c : Nat) : Int) = 0 ∨ (((c : Nat) : Int) = 1 ∨ ((c : Nat) : Int) = 6)))
    (h8 : ((c : Nat) : Int) ≠ ((k : Nat) : Int))
    (h9 : (fsz ((k : Nat) : Int)) = (fs_size k))
    (h10 : 0 < (fs_size k))
    (h11 : 0 ≤ ((fs_size k) / 8)) :
    ((fs_size k) / 8) = (((shad f) + ((fs_size k) / 8)) - (shad f)) := by
  lia

-- leptonica/pix1_fuzzer: lib/O22/O22Tail.v (replace)
example
    {word T2 T3 T4 T5 : Type}
    (u : word → Int)
    (x : word)
    (pix : Int)
    (Z_to_bv : Nat → Int → T2)
    (s : Int)
    (dp : Int)
    (c_top : T3 → Int)
    (C : T3)
    (m' : T4)
    (store_ok : T5 → T4 → T2 → Nat → Bool)
    (SEGS : T5)
    (h1 : (c_top C) = s)
    (h2 : (1 ≤ dp ∧ dp < (2 ^ (64 : Nat))))
    (h3 : (store_ok SEGS m' (Z_to_bv 64 pix) 64) = true) :
    (u x) = (pix + ((u x) - pix)) := by
  lia

-- leptonica/pix1_fuzzer: lib/V22/V22Drv1.v (assert)
example
    {word list_byte : Type}
    (tid : word)
    (data : list_byte)
    (cap : Int)
    (len : Int)
    (vals : list_byte)
    (want : Int)
    (bv_unsigned : word → Int)
    (L : Int)
    (length : list_byte → Nat)
    (firstn : Nat → list_byte → list_byte)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h2 : (length vals) = 42)
    (h3 : want = (min (cap - len) 65536))
    (h4 : (0 ≤ len ∧ len < cap))
    (h5 : len ≤ L)
    (h6 : L = (((length data) : Nat) : Int))
    (h7 : (((length (firstn (Int.toNat len) data)) : Nat) : Int) = len) :
    (1 ≤ want ∧ want ≤ 65536) := by
  lia

-- leptonica/pix1_fuzzer: lib/V22/V22Drv1.v (assert)
example
    {word list_byte T3 : Type}
    (tid : word)
    (data : list_byte)
    (cap : Int)
    (len : Int)
    (vals : list_byte)
    (R : T3)
    (want : Int)
    (n : Int)
    (L : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (firstn : Nat → list_byte → list_byte)
    (getr : T3 → Int → word)
    (Rc : T3)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h2 : (length vals) = 42)
    (h3 : want = (min (cap - len) 65536))
    (h4 : (0 ≤ len ∧ len < cap))
    (h5 : len ≤ L)
    (h6 : L = (((length data) : Nat) : Int))
    (h7 : (((length (firstn (Int.toNat len) data)) : Nat) : Int) = len)
    (h8 : (1 ≤ want ∧ want ≤ 65536))
    (h9 : (bv_unsigned (getr R 17)) = 63)
    (h10 : n = (min want (L - len)))
    (h11 : len = L)
    (h12 : (bv_unsigned (getr Rc 17)) = 57)
    (h13 : (1 ≤ n ∧ n ≤ want)) :
    (len + n) ≤ L := by
  lia

-- leptonica/pix1_fuzzer: lib/V22/V22Drv1.v (assert)
example
    {word list_byte T3 : Type}
    (tid : word)
    (data : list_byte)
    (cap : Int)
    (len : Int)
    (vals : list_byte)
    (R : T3)
    (want : Int)
    (n : Int)
    (bv_unsigned : word → Int)
    (L : Int)
    (length : list_byte → Nat)
    (firstn : Nat → list_byte → list_byte)
    (getr : T3 → Int → word)
    (Rc : T3)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h2 : (length vals) = 42)
    (h3 : want = (min (cap - len) 65536))
    (h4 : (0 ≤ len ∧ len < cap))
    (h5 : len ≤ L)
    (h6 : L = (((length data) : Nat) : Int))
    (h7 : (((length (firstn (Int.toNat len) data)) : Nat) : Int) = len)
    (h8 : (1 ≤ want ∧ want ≤ 65536))
    (h9 : (bv_unsigned (getr R 17)) = 63)
    (h10 : n = (min want (L - len)))
    (h11 : len = L)
    (h12 : (bv_unsigned (getr Rc 17)) = 57)
    (h13 : (1 ≤ n ∧ n ≤ want))
    (h14 : (len + n) ≤ L) :
    (len + n) ≤ cap := by
  lia

-- leptonica/pix_orient_fuzzer: lib/Common/Musl/PFCoreS.v (replace)
example
    (sp0 : Int)
    (ka : Int)
    (f : Int)
    (cnt' : Int)
    (INT_MAX : Int)
    (h1 : ka ≤ 200)
    (h2 : f = (sp0 - 2400))
    (h3 : 0 ≤ cnt')
    (h4 : (cnt' + ka) ≤ INT_MAX)
    (h5 : 0 ≤ ka) :
    (sp0 - 3344) = ((sp0 - 3312) - 32) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3D/F_main_AA.v (replace)
example (cap : Int) (h1 : cap = 67108864) :
    (Int.toNat cap) = (Int.toNat ((cap * 2) - (((Int.toNat cap) : Nat) : Int))) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3P/F_fmt_errmsgA.v (replace)
example
    {T1 : Type}
    (len : Nat)
    (length : T1 → Nat)
    (vjk : T1)
    (rest : T1)
    (se : T1)
    (h1 : (length vjk) = (255 - len))
    (h2 : 2 ≤ (length vjk))
    (h3 : (length rest) = (255 - (length se))) :
    (Int.toNat (254 - ((len : Nat) : Int))) = (((253 - len) + 0) + 1) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3P/F_ngchk_fsegA__A3P.v (replace)
example
    {T1 : Type}
    (length : T1 → Nat)
    (shb_hdr : Int → T1)
    (TL : Int)
    (rest : T1)
    (h1 : (((length rest) : Nat) : Int) = (TL - 16))
    (h2 : (((length (shb_hdr TL)) : Nat) : Int) = 12) :
    (((length (shb_hdr TL)) : Nat) : Int) = 12 := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3P/F_pcap_fopenA.v (replace)
example
    (Fb : Int)
    (Z_shiftr : Int → Int → Int)
    (h1 : (2147450880 ≤ ((Z_shiftr Fb 3) + 2147450880) ∧ ((((Z_shiftr Fb 3) + 2147450880) + 8) ≤ 17594333495296 ∧ ((Fb + 64) ≤ 2147446784 ∨ (((Z_shiftr Fb 3) + 2147450880) + 8) ≤ Fb)))) :
    (Fb + 48) = (((Fb + 32) + ((4 : Nat) : Int)) + ((12 : Nat) : Int)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3P/F_pcap_open2A__A3P.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (length : T1 → Nat)
    (Fmt_snprintf : Nat → T2 → T3 → T1)
    (fs : T2)
    (args : T3)
    (pc_bufalloc : T4 → Int)
    (p' : T4)
    (h1 : 0 < (pc_bufalloc p')) :
    (((Int.toNat 256) - (length (Fmt_snprintf 256 fs args))) - 1) = (255 - (length (Fmt_snprintf 256 fs args))) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3P/F_sfchk_failA__A3P.v (replace)
example
    (Fb : Int)
    (Z_shiftr : Int → Int → Int)
    (h1 : (2147450880 ≤ ((Z_shiftr Fb 3) + 2147450880) ∧ ((((Z_shiftr Fb 3) + 2147450880) + 16) ≤ 17594333495296 ∧ ((Fb + 128) ≤ 2147446784 ∨ (((Z_shiftr Fb 3) + 2147450880) + 16) ≤ Fb)))) :
    (Fb + 36) = (Fb + ((36 : Nat) : Int)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3P/F_sfchk_failA__A3P.v (replace)
example
    {T1 : Type}
    (Fb : Int)
    (Z_shiftr : Int → Int → Int)
    (bv_unsigned : T1 → Int)
    (spa : T1)
    (SPA : Int)
    (h1 : (2147450880 ≤ ((Z_shiftr Fb 3) + 2147450880) ∧ ((((Z_shiftr Fb 3) + 2147450880) + 16) ≤ 17594333495296 ∧ ((Fb + 128) ≤ 2147446784 ∨ (((Z_shiftr Fb 3) + 2147450880) + 16) ≤ Fb))))
    (h2 : (bv_unsigned spa) = SPA) :
    (Fb + 36) = ((Fb + 32) + 4) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3S/F_printf_core_conv__A3S.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (FS : Int)
    (Ff : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (j : Int)
    (zlength : list_Z → Int)
    (W' : list_Z)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (KHIGH : Int)
    (x : Int)
    (dec_digits : Int → list_Z)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q ≤ (2 ^ (47 : Nat)))
    (h4 : (65536 ≤ A ∧ (A + (zlength fmt)) ≤ 204800))
    (h5 : ((684904 ≤ Fp ∧ (Fp + FS) ≤ 714232) ∨ (((AP + 8) ≤ Fp ∧ (Fp + FS) ≤ VA) ∨ (0 < Fp ∧ ((Fp + FS) ≤ lo ∧ ((Fp + FS) ≤ 65536 ∨ 6303744 ≤ Fp))))))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : 0 ≤ BS)
    (h10 : (Fp ≤ Ff ∧ (Ff + 232) ≤ (Fp + FS)))
    (h11 : KHIGH ≤ lo)
    (h12 : (x / 10) < 1844674407370955162)
    (h13 : 2 ≤ (zlength (dec_digits x))) :
    (Int.toNat (j - ((zlength W') + 1))) = (Int.toNat ((j - 1) - (zlength W'))) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3S/F_stdio_read__A3S.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (B : Int)
    (n : Int)
    (len : Int)
    (length : T1 → Nat)
    (rest2 : T1)
    (raw' : T1)
    (store_ok : T2 → T3 → T4 → Int → Bool)
    (asegs : T2)
    (mC : T3)
    (wa : Int → T4)
    (D : Int)
    (firstn : Nat → T1 → T1)
    (raw : T1)
    (skipn : Nat → T1 → T1)
    (h1 : (length raw') = ((length rest2) + 1))
    (h2 : (store_ok asegs mC (wa (D + 0)) 1) = true)
    (h3 : (length (firstn (Int.toNat (len - 1)) raw)) = (Int.toNat (len - 1)))
    (h4 : (length (skipn (Int.toNat (len - 1)) raw)) = ((length raw) - (Int.toNat (len - 1))))
    (h5 : (store_ok asegs mC (wa (D + (len - 1))) 1) = true)
    (h6 : (((length rest2) : Nat) : Int) = (n - len)) :
    (B + (n - (len - 1))) = ((B + 1) + (((length rest2) : Nat) : Int)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3S/I_fread_top__A3S.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (zlength : T2 → Int)
    (fmtz : T2)
    (slots : T2)
    (length : T3 → Nat)
    (fstr : T3)
    (h1 : 0 ≤ (zlength fmtz))
    (h2 : 0 ≤ (zlength slots))
    (h3 : (zlength fmtz) = ((((length fstr) : Nat) : Int) + 1)) :
    (bv_unsigned sp) = (((bv_unsigned sp) + (-48)) + 48) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3S/I_fread_top__A3S.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (zlength : T2 → Int)
    (slots : T2)
    (fmtz : T2)
    (length : T3 → Nat)
    (fstr : T3)
    (h1 : 0 ≤ (zlength slots))
    (h2 : 0 ≤ (zlength fmtz))
    (h3 : (zlength fmtz) = ((((length fstr) : Nat) : Int) + 1)) :
    (bv_unsigned sp) = (((bv_unsigned sp) + (-48)) + ((48 : Nat) : Int)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3S/I_strerror__A3S.v (replace)
example
    {word list_byte T3 : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (lo : Int)
    (str : list_byte)
    (slack : list_byte)
    (RLO : Int)
    (RHI : Int)
    (bv_unsigned : word → Int)
    (KHIGH : Int)
    (length : list_byte → Nat)
    (strchrnul_idx : T3 → list_byte → Nat)
    (cc : T3)
    (KEND : Int)
    (h1 : lo ≤ ((bv_unsigned sp) - 2224))
    (h2 : KHIGH ≤ lo)
    (h3 : ((-(((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h4 : ((bv_unsigned a1) % 256) ≠ 0)
    (h5 : 0 < (bv_unsigned a0))
    (h6 : ((((strchrnul_idx cc str) : Nat) : Int) + 1) ≤ (2 ^ (40 : Nat)))
    (h7 : (RLO ≤ (bv_unsigned a0) ∧ (((bv_unsigned a0) + ((((strchrnul_idx cc str) : Nat) : Int) + 1)) ≤ RHI ∧ ((RLO % 64) = 0 ∧ ((RHI % 64) = 0 ∧ (0 ≤ RLO ∧ RHI ≤ KEND)))))) :
    (bv_unsigned sp) = (((bv_unsigned sp) + (-72)) + ((72 : Nat) : Int)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3S/I_strerror__A3S.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (zlength : T2 → Int)
    (fmtz : T2)
    (slots : T2)
    (D : Int)
    (a2 : T1)
    (lo : Int)
    (length : T2 → Nat)
    (fstr : T2)
    (h1 : 0 ≤ (zlength fmtz))
    (h2 : 0 ≤ (zlength slots))
    (h3 : ((D + (bv_unsigned a2)) ≤ lo ∨ (bv_unsigned sp) ≤ D))
    (h4 : (0 < D ∧ (D + (bv_unsigned a2)) ≤ (2 ^ (63 : Nat))))
    (h5 : (((Int.toNat (bv_unsigned a2)) : Nat) : Int) = (bv_unsigned a2))
    (h6 : (((length fmtz) : Nat) : Int) = ((((length fstr) : Nat) : Int) + 1)) :
    ((bv_unsigned sp) + (-352)) = (((bv_unsigned sp) + (-304)) + (-48)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3S/I_strerror__A3S.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (zlength : T2 → Int)
    (fmtz : T2)
    (slots : T2)
    (D : Int)
    (a2 : T1)
    (lo : Int)
    (length : T2 → Nat)
    (fstr : T2)
    (h1 : 0 ≤ (zlength fmtz))
    (h2 : 0 ≤ (zlength slots))
    (h3 : ((D + (bv_unsigned a2)) ≤ lo ∨ (bv_unsigned sp) ≤ D))
    (h4 : (0 < D ∧ (D + (bv_unsigned a2)) ≤ (2 ^ (63 : Nat))))
    (h5 : (((Int.toNat (bv_unsigned a2)) : Nat) : Int) = (bv_unsigned a2))
    (h6 : (((length fmtz) : Nat) : Int) = ((((length fstr) : Nat) : Int) + 1)) :
    ((bv_unsigned sp) + (-304)) = (((bv_unsigned sp) + (-352)) + 48) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3S/Stdio_glue_foKitA__A3S.v (replace)
example
    {T1 T2 : Type}
    (length : T1 → Nat)
    (strerror_msgb : T2 → T1)
    (e : T2)
    (strerror : T2 → T1)
    (h1 : (length (strerror e)) = (length (strerror_msgb e))) :
    ((Int.toNat 256) - ((length (strerror_msgb e)) + 1)) = (255 - (length (strerror_msgb e))) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/ADepot_init__A3W.v (replace)
example
    {T1 : Type}
    (V : Nat → Int)
    (i : Int)
    (al_nodes : T1 → Int)
    (L : T1)
    (al_store : T1 → Int)
    (h1 : (al_nodes L) = (4096 * (V 469)))
    (h2 : (al_store L) = (4096 * (V 470))) :
    (((4096 * (V 470)) + 4096) + (i - 4080)) = (((4096 * (V 470)) + 16) + i) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/ADfn_recP__A3W.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 : Type}
    (al_t : T1 → Int)
    (L : T1)
    (bv_unsigned : T2 → Int)
    (sp : T2)
    (shad : Int → Int)
    (hm : Int)
    (mb : Int)
    (shlen : Int → Int)
    (rup : T3 → Int → Int)
    (n : T3)
    (ms : Int)
    (K_BATCH_CLASS : T4)
    (CSec : Int → Int → T3 → T5)
    (st : T6)
    (qfirst : T1 → T7 → Int)
    (q_loc : T8 → T7)
    (Q : T8)
    (enq_is_app : T9 → Bool)
    (st_r : T9)
    (st_enq : T9 → T5 → T10)
    (Q_CACHE : Int)
    (a_qloc_bytes : T10 → Int)
    (Q_MAX : Int)
    (a_qglob_bytes : T10 → Int)
    (aregion_info : T1 → T4 → Int)
    (al_space_beg : T1 → Int)
    (aregion : T1 → T4 → Int)
    (c_mapped_user : T11 → Int)
    (get_cls : T6 → T4 → T11)
    (K_REGION : Int)
    (h1 : True)
    (h2 : (bv_unsigned sp) < (2 ^ (47 : Nat)))
    (h3 : ((shad (hm + 16)) = ((shad mb) + 768) ∧ ((shlen (rup n 8)) ≤ ((ms / 8) - 768) ∧ (0 < (shlen (rup n 8)) ∧ (((hm + 16) + (rup n 8)) ≤ (mb + ms) ∧ (2148238848 ≤ (shad mb) ∧ ((shad mb) + (ms / 8)) ≤ 17594332446720))))))
    (h4 : (mb % 8) = 0)
    (h5 : (0 ≤ (qfirst L (q_loc Q)) ∧ (qfirst L (q_loc Q)) < (2 ^ (64 : Nat))))
    (h6 : (enq_is_app st_r) = false)
    (h7 : (enq_is_app st_r) = true)
    (h8 : Q_CACHE < (a_qloc_bytes (st_enq st_r (CSec mb ms n))))
    (h9 : Q_MAX < ((a_qglob_bytes (st_enq st_r (CSec mb ms n))) + (a_qloc_bytes (st_enq st_r (CSec mb ms n)))))
    (h10 : (aregion_info L K_BATCH_CLASS) = (((al_space_beg L) + 137438953472) + 3072))
    (h11 : (aregion L K_BATCH_CLASS) = ((al_space_beg L) + (24 * 4294967296)))
    (h12 : (2199023255552 ≤ (shad ((aregion L K_BATCH_CLASS) + (c_mapped_user (get_cls st K_BATCH_CLASS)))) ∧ ((shad (aregion L K_BATCH_CLASS)) + (shlen K_REGION)) ≤ 17594333495296))
    (h13 : ((mb + ms) ≤ ((aregion L K_BATCH_CLASS) + (c_mapped_user (get_cls st K_BATCH_CLASS))) ∨ ((aregion L K_BATCH_CLASS) + K_REGION) ≤ mb))
    (h14 : (((shad (hm + 16)) + (shlen (rup n 8))) ≤ (shad ((aregion L K_BATCH_CLASS) + (c_mapped_user (get_cls st K_BATCH_CLASS)))) ∨ ((shad (aregion L K_BATCH_CLASS)) + (shlen K_REGION)) ≤ (shad (hm + 16)))) :
    ((al_t L) + 2784) = (((al_t L) + 2768) + 16) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/AFake_arep.v (replace)
example
    {T1 : Type}
    (F : Int)
    (h_1 : Int)
    (Z_land : Int → Int → Int)
    (pos : Int)
    (fk_flag : T1 → Int → Int → Int)
    (L : T1)
    (al_fake : T1 → Int)
    (flag : Int)
    (fk_frame : T1 → Int → Int → Int)
    (shad : Int → Int)
    (shlen : Int → Int)
    (req : Int)
    (j : Int)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ pos ∧ pos < 128))
    (h3 : flag = (fk_flag L 7 pos))
    (h4 : F = (fk_frame L 7 pos))
    (h5 : (shad F) = (2147450880 + (F / 8)))
    (h6 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h7 : (shlen req) = (req / 8))
    (h8 : ((shad (al_fake L)) ≤ (shad F) ∧ ((shad F) + 1024) ≤ ((shad (al_fake L)) + 1446400)))
    (h9 : pos = (Z_land (h_1 + j) 127))
    (h10 : flag = (((al_fake L) + 36608) + pos))
    (h11 : F = (((al_fake L) + 7376896) + (pos * 8192))) :
    (F + 8184) = ((F + 8192) - 8) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/ARepInit_kit__A3W.v (replace)
example (V : Nat → Int) (ATOP : Int) (h1 : (((32768 * (V 0)) + (4096 * (V 10))) - 8388608) = ATOP) :
    ((((32768 * (V 0)) + (4096 * (V 10))) + (4096 * (V 344))) - 8388608) = (((32768 * (V 0)) + ((4096 * (V 10)) + (4096 * (V 344)))) + (-8388608)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/ARepInit_kit__A3W.v (replace)
example {T1 : Type} (al_t : T1 → Int) (L : T1) (c : Int) (i : Int) :
    ((al_t L) + ((208 + (c * 80)) + i)) = ((((al_t L) + 208) + (c * 80)) + i) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/ARepInit_kit__A3W.v (replace)
example
    (i : Int)
    (V : Nat → Int)
    (ATOP : Int)
    (h1 : (((32768 * (V 0)) + (4096 * (V 10))) - 8388608) = ATOP)
    (h2 : (0 ≤ i ∧ i < 4096)) :
    ((((4096 * (V 208)) + ((-4096) * (V 209))) + 137439019008) + i) = (((((4096 * (V 208)) + ((-4096) * (V 209))) + 65536) + (2 ^ (37 : Nat))) + i) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/F_amerge__A3W.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : Type}
    (length : T1 → Nat)
    (P : T1)
    (R' : T1)
    (L : T2)
    (cur : T3)
    (nx : T3)
    (baddr : T2 → T3 → Int)
    (Q_BATCH_BYTES : Int)
    (tfirst : T2 → T1 → Int → Int)
    (hd : T3 → T1 → T3)
    (map : T4 → T5 → T1)
    (Z_to_bv : Int → T4)
    (qhdrs : T2 → T6 → T7 → T5)
    (b_chunks : T8 → T6)
    (fst : T3 → T8)
    (qb_ks : T9 → T7)
    (snd : T3 → T9)
    (b_count : T8 → Int)
    (qb_slot : T9 → Int)
    (x : T3)
    (T : T1)
    (tf0 : Int)
    (tlast : T2 → T1 → T10 → Int)
    (tl0 : T10)
    (h1 : (((baddr L cur) + Q_BATCH_BYTES) ≤ (baddr L nx) ∨ ((baddr L nx) + Q_BATCH_BYTES) ≤ (baddr L cur)))
    (h2 : (tfirst L R' 0) = (baddr L (hd nx R')))
    (h3 : (0 ≤ (tfirst L R' 0) ∧ (tfirst L R' 0) < (2 ^ (64 : Nat))))
    (h4 : (length (map (Z_to_bv 64) (qhdrs L (b_chunks (fst cur)) (qb_ks (snd cur))))) = (Int.toNat (b_count (fst cur))))
    (h5 : (length (map (Z_to_bv 64) (qhdrs L (b_chunks (fst nx)) (qb_ks (snd nx))))) = (Int.toNat (b_count (fst nx))))
    (h6 : 0 ≤ (qb_slot (snd cur)))
    (h7 : 0 ≤ (qb_slot (snd nx)))
    (h8 : (qb_slot (snd x)) ≠ (qb_slot (snd cur)))
    (h9 : (qb_slot (snd x)) ≠ (qb_slot (snd nx)))
    (h10 : ((0 ≤ (tfirst L T tf0) ∧ (tfirst L T tf0) < (2 ^ (64 : Nat))) ∧ (0 ≤ (tlast L T tl0) ∧ (tlast L T tl0) < (2 ^ (64 : Nat))))) :
    ((((length P) + ((length R') + 1)) : Nat) : Int) = (((((length P) + (((length R') + 1) + 1)) : Nat) : Int) - 1) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/F_m2s_b__A3W.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (a0 : T1)
    (cells_size : T2 → Nat)
    (cs1 : T2)
    (i : Int) :
    ((bv_unsigned a0) + ((((cells_size cs1) : Nat) : Int) + i)) = (((bv_unsigned a0) + (((cells_size cs1) : Nat) : Int)) + i) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/F_m2s_b__A3W.v (assert)
example
    {word : Type}
    (sp : word)
    (a0 : word)
    (a2 : word)
    (lo : Int)
    (RLO2 : Int)
    (RHI2 : Int)
    (bv_unsigned : word → Int)
    (KHIGH : Int)
    (KEND : Int)
    (h1 : lo ≤ ((bv_unsigned sp) - 2208))
    (h2 : KHIGH ≤ lo)
    (h3 : (((bv_unsigned a0) + (bv_unsigned a2)) ≤ lo ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h4 : (bv_unsigned a2) ≤ (2 ^ (40 : Nat)))
    (h5 : (RLO2 ≤ (bv_unsigned a0) ∧ (((bv_unsigned a0) + (bv_unsigned a2)) ≤ RHI2 ∧ ((RLO2 % 64) = 0 ∧ ((RHI2 % 64) = 0 ∧ (0 ≤ RLO2 ∧ RHI2 ≤ KEND)))))) :
    lo ≤ ((bv_unsigned sp) - 2128) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/A3W/I_read.v (assert)
example
    {word : Type}
    (sp : word)
    (tp : word)
    (a1 : word)
    (lo : Int)
    (fd : Int)
    (count : Int)
    (RLO2 : Int)
    (RHI2 : Int)
    (ke : Int)
    (ks : Int)
    (kb : Int)
    (bv_unsigned : word → Int)
    (KHIGH : Int)
    (errno_addr : word → Int)
    (KEND : Int)
    (h1 : lo ≤ ((bv_unsigned sp) - 2208))
    (h2 : KHIGH ≤ lo)
    (h3 : (3 ≤ fd ∧ fd < (2 ^ (32 : Nat))))
    (h4 : (1 ≤ count ∧ count ≤ 16777216))
    (h5 : (6307840 ≤ (bv_unsigned a1) ∨ (6099024 ≤ (bv_unsigned a1) ∧ ((bv_unsigned a1) + count) ≤ 6307840)))
    (h6 : ((bv_unsigned a1) + count) ≤ lo)
    (h7 : (4096 ≤ (errno_addr tp) ∧ (((errno_addr tp) + 4) ≤ lo ∧ (((0 ≤ ke ∧ ke ≤ 1) ∧ ((0 ≤ ks ∧ ks ≤ 1) ∧ (0 ≤ kb ∧ kb ≤ 1))) ∧ ((ke = 0 ∧ (errno_addr tp) = 6166804) ∧ ((((errno_addr tp) + 4) ≤ (2147446784 + (ks * 18446744073709551616)) ∧ (17594333495296 * ks) ≤ (errno_addr tp)) ∧ (((bv_unsigned a1) + count) ≤ ((errno_addr tp) + (kb * 18446744073709551616)) ∧ ((errno_addr tp) + 4) ≤ ((bv_unsigned a1) + ((1 - kb) * 18446744073709551616)))))))))
    (h8 : 164 ≤ (bv_unsigned tp))
    (h9 : (RLO2 ≤ (bv_unsigned a1) ∧ (((bv_unsigned a1) + count) ≤ RHI2 ∧ ((RLO2 % 64) = 0 ∧ ((RHI2 % 64) = 0 ∧ (0 ≤ RLO2 ∧ RHI2 ≤ KEND)))))) :
    lo ≤ ((bv_unsigned sp) - 2128) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/AS/MainEntry__AS.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (a : T1)
    (tid : T2)
    (c : T3)
    (pl : T4)
    (js : T5)
    (usp : Int)
    (length : T5 → Nat)
    (V_of : T1 → T2 → T3 → T4 → T5 → Nat → Int)
    (h1 : (length js) = 92)
    (h2 : ((32768 * (V_of a tid c pl js 0)) + ((16 * (V_of a tid c pl js 6)) + (4096 * (V_of a tid c pl js 10)))) = usp) :
    8388608 = (usp - (usp - 8388608)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/EquivA/UStdioX.v (replace)
example
    {T1 : Type}
    (len0 : Int)
    (f_bufsize : T1 → Int)
    (f : T1)
    (len : Int)
    (h1 : ((0 ≤ len0 ∧ len0 < (2 ^ (62 : Nat))) ∧ (((f_bufsize f) = 0 → len0 = len) ∧ ((f_bufsize f) ≠ 0 → len0 = (len - 1))))) :
    (Int.toNat (len0 + 1)) = ((Int.toNat len0) + 1) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/Lib/MState.v (replace)
example (z : Int) (h1 : (0 ≤ z ∧ z < (2 ^ (64 : Nat)))) (h2 : (z % 2) = 0) :
    0 = (z % 2) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_fwritex__S3.v (replace)
example {T1 : Type} (length : T1 → Nat) (s : T1) (i : Int) :
    (((length s) : Nat) : Int) = (i + ((((length s) : Nat) : Int) - i)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_memmove__S3.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (p : Nat)
    (length : T1 → Nat)
    (xs : T1)
    (firstn : Nat → T2 → T1)
    (skipn : T3 → T4 → T2)
    (k : T3)
    (bs : T4)
    (h1 : (length (firstn p (skipn k bs))) = p) :
    (p + (length xs)) = (p + ((p + (length xs)) - p)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_memmove__S3.v (replace)
example
    {word list_byte : Type}
    (a0 : word)
    (bs : list_byte)
    (k : Int)
    (n : Int)
    (p : Int)
    (length : list_byte → Nat)
    (bv_unsigned : word → Int)
    (h1 : (length bs) = (Int.toNat (k + n)))
    (h2 : 1 ≤ k)
    (h3 : (0 ≤ n ∧ n < (2 ^ (62 : Nat))))
    (h4 : (0 ≤ (bv_unsigned a0) ∧ (((bv_unsigned a0) + k) + n) ≤ (2 ^ (64 : Nat)))) :
    (n - (p + 1)) = ((n - p) + (-1)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_memmove__S3.v (replace)
example
    {T1 T2 : Type}
    (length : T1 → Nat)
    (bs : T1)
    (n : Int)
    (bv_unsigned : T2 → Int)
    (a0 : T2)
    (k : Int)
    (h1 : (0 ≤ (bv_unsigned a0) ∧ (((bv_unsigned a0) + k) + n) ≤ (2 ^ (64 : Nat)))) :
    (((length bs) : Nat) : Int) = ((((Int.toNat n) : Nat) : Int) + ((((length bs) : Nat) : Int) - (((Int.toNat n) : Nat) : Int))) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_ngnextA.v (replace)
example
    {word T2 : Type}
    (sp : word)
    (bv_unsigned : word → Int)
    (usp0 : T2 → Int)
    (R : T2)
    (lo : Int)
    (rc_spmain : T2 → Int)
    (HA : Int)
    (DA : Int)
    (P : Int)
    (CEILZ : Int)
    (utp : T2 → Int)
    (Af : Int)
    (h1 : ((usp0 R) - 8388608) ≤ lo)
    (h2 : (lo + 81920) ≤ (bv_unsigned sp))
    (h3 : (bv_unsigned sp) ≤ (rc_spmain R))
    (h4 : ((bv_unsigned sp) % 16) = 0)
    (h5 : (bv_unsigned sp) ≤ HA)
    (h6 : (HA + 24) ≤ DA)
    (h7 : (DA + 8) ≤ (rc_spmain R))
    (h8 : (HA % 8) = 0)
    (h9 : (DA % 8) = 0)
    (h10 : 140735340871680 ≤ (usp0 R))
    (h11 : (usp0 R) ≤ (2 ^ (47 : Nat)))
    (h12 : 0 < P)
    (h13 : (P % 16) = 0)
    (h14 : (P + 680) ≤ CEILZ)
    (h15 : ((P + 680) ≤ 65536 ∨ 348160 ≤ P))
    (h16 : ((P + 680) ≤ ((utp R) - 200) ∨ (((utp R) - 200) + 4096) ≤ P))
    (h17 : 0 < Af)
    (h18 : (Af + 1264) ≤ CEILZ) :
    ((bv_unsigned sp) + (-104)) = ((((bv_unsigned sp) + (-160)) + ((32 : Nat) : Int)) + ((24 : Nat) : Int)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_ngnextD__S3.v (replace)
example
    (h1 : Int)
    (U : Int)
    (h0 : Int)
    (h2 : Int)
    (h3 : Int)
    (h1_1 : U = (((h0 + (256 * h1)) + (65536 * h2)) + (16777216 * h3)))
    (h2_1 : (0 ≤ U ∧ U < (2 ^ (32 : Nat)))) :
    (h1 * (2 ^ (48 : Nat))) = ((h1 * 256) * (2 ^ (40 : Nat))) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_printf_core__S3.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (zlength : T2 → Int)
    (fmtz : T2)
    (slots : T2)
    (D : Int)
    (n : Int)
    (lo : Int)
    (h1 : 0 ≤ (zlength fmtz))
    (h2 : 0 ≤ (zlength slots))
    (h3 : ((D + n) ≤ lo ∨ (bv_unsigned sp) ≤ D))
    (h4 : (0 < D ∧ (D + n) ≤ (2 ^ (63 : Nat)))) :
    (((bv_unsigned sp) + (-304)) + 232) = ((bv_unsigned sp) + (-72)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_printf_core_common.v (replace)
example
    {list_X : Type}
    (l : list_X)
    (i : Nat)
    (n : Nat)
    (length : list_X → Nat)
    (h1 : (n ≤ i ∧ i < (length l))) :
    n = (min n i) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_printf_core_conv__S3.v (replace)
example
    {list_Z : Type}
    (Fp : Int)
    (FS : Int)
    (Ff : Int)
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
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q ≤ (2 ^ (47 : Nat)))
    (h4 : (65536 ≤ A ∧ (A + (zlength fmt)) ≤ 77824))
    (h5 : ((142824 ≤ Fp ∧ (Fp + FS) ≤ 345288) ∨ (((AP + 8) ≤ Fp ∧ (Fp + FS) ≤ VA) ∨ (0 < Fp ∧ ((Fp + FS) ≤ lo ∧ ((Fp + FS) ≤ 65536 ∨ 352256 ≤ Fp))))))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : 0 ≤ BS)
    (h10 : (Fp ≤ Ff ∧ (Ff + 232) ≤ (Fp + FS)))
    (h11 : (znth fmt i) ≠ 0) :
    n = (((A + i) + n) - (A + i)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_printf_core_conv__S3.v (replace)
example
    {list_Z T2 : Type}
    (Fp : Int)
    (FS : Int)
    (Ff : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (j : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (x : Int)
    (hex_digits : T2 → Int → list_Z)
    (l : T2)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q ≤ (2 ^ (47 : Nat)))
    (h4 : (65536 ≤ A ∧ (A + (zlength fmt)) ≤ 77824))
    (h5 : ((142824 ≤ Fp ∧ (Fp + FS) ≤ 345288) ∨ (((AP + 8) ≤ Fp ∧ (Fp + FS) ≤ VA) ∨ (0 < Fp ∧ ((Fp + FS) ≤ lo ∧ ((Fp + FS) ≤ 65536 ∨ 352256 ≤ Fp))))))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : 0 ≤ BS)
    (h10 : (Fp ≤ Ff ∧ (Ff + 232) ≤ (Fp + FS)))
    (h11 : (x / 16) < 1152921504606846976)
    (h12 : 1 ≤ (zlength (hex_digits l x))) :
    ((q + (-392)) + (j - 1)) = (((q + (-392)) + j) + (-1)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_sfpcapng_aiE__S3.v (replace)
example
    {T1 T2 T3 : Type}
    (B : Int)
    (cur_off : T1 → Int)
    (c' : T1)
    (padded : Int)
    (length : T2 → Nat)
    (bs3 : T2)
    (pc_bufalloc : T3 → Int)
    (p : T3)
    (cur_remaining : T1 → Int)
    (buf' : T2)
    (post : T2)
    (olen : Int)
    (buf5 : T2)
    (h1 : (length bs3) = (Int.toNat (pc_bufalloc p)))
    (h2 : 8 ≤ (cur_off c'))
    (h3 : ((cur_off c') + (cur_remaining c')) ≤ (((length buf') : Nat) : Int))
    (h4 : (((length post) : Nat) : Int) = (((((length buf') : Nat) : Int) - (cur_off c')) - 4))
    (h5 : (0 ≤ olen ∧ olen < 65536))
    (h6 : ((olen ≤ padded ∧ padded ≤ (olen + 3)) ∧ (padded % 4) = 0))
    (h7 : (length buf5) = (length buf')) :
    (B + (((cur_off c') + 4) + padded)) = (((B + (cur_off c')) + 4) + padded) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_sfpcapng_blk__S3.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (P : Int)
    (B : Int)
    (pc_bufalloc : T2 → Int)
    (p : T2)
    (EB : Int)
    (rc_spmain : T3 → Int)
    (R : T3)
    (CUR : Int)
    (h1 : ((P + 680) ≤ B ∨ (B + (pc_bufalloc p)) ≤ P))
    (h2 : (((bv_unsigned sp) ≤ EB ∧ ((EB + 256) ≤ (rc_spmain R) ∧ ((EB + 256) ≤ CUR ∨ (CUR + 24) ≤ EB))) ∨ EB = (P + 216)))
    (h3 : (P % 8) = 0) :
    ((bv_unsigned sp) + (-88)) = (((bv_unsigned sp) + (-96)) + ((8 : Nat) : Int)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/F_strerror__S3.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (k : Nat)
    (length : T1 → Nat)
    (raw' : T1)
    (rest2 : T1)
    (store_ok : T2 → T3 → T4 → Int → Bool)
    (usegs : T2)
    (mC : T3)
    (wa : Int → T4)
    (D : Int)
    (firstn : Nat → T1 → T1)
    (zlength : T5 → Int)
    (s : T5)
    (raw : T1)
    (skipn : Nat → T1 → T1)
    (n : Int)
    (h1 : (length raw') = ((length rest2) + 1))
    (h2 : (store_ok usegs mC (wa (D + 0)) 1) = true)
    (h3 : (length (firstn (Int.toNat ((zlength s) - 1)) raw)) = (Int.toNat ((zlength s) - 1)))
    (h4 : (length (skipn (Int.toNat ((zlength s) - 1)) raw)) = ((length raw) - (Int.toNat ((zlength s) - 1))))
    (h5 : (store_ok usegs mC (wa (D + ((zlength s) - 1))) 1) = true)
    (h6 : (((length rest2) : Nat) : Int) = (n - (zlength s))) :
    (k + 1) = (1 + k) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/PcapRep.v (replace)
example
    {T1 T2 : Type}
    (P : Int)
    (rf : T1)
    (cs : T2)
    (csize : T1 → Nat)
    (cells_size : T2 → Nat)
    (h1 : (csize rf) = 8)
    (h2 : (cells_size cs) = 304) :
    (P + 216) = (P + ((216 : Nat) : Int)) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/RF_am_A__S3.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (r_base : T1 → Int)
    (r : T1)
    (snd : T2 → Int)
    (e : T2)
    (rsv : Int)
    (E : Int)
    (P : Int)
    (n : Int)
    (store_ok : T3 → T4 → T5 → Int → Bool)
    (usegs : T3)
    (mX : T4)
    (wa : Int → T5)
    (bv_unsigned : T6 → Int)
    (a0 : T6)
    (h1 : (0 ≤ rsv ∧ rsv < (2 ^ (31 : Nat))))
    (h2 : (0 ≤ E ∧ (E + 1) ≤ (2 ^ (64 : Nat))))
    (h3 : (16 ≤ P ∧ (P + n) ≤ E))
    (h4 : (E - (n + P)) = rsv)
    (h5 : (store_ok usegs mX (wa ((bv_unsigned a0) + (-3))) 1) = true)
    (h6 : (store_ok usegs mX (wa (((r_base r) + ((snd e) + (-rsv))) + 0)) 1) = true) :
    ((r_base r) + ((snd e) - rsv)) = (((r_base r) + ((snd e) + (-rsv))) + 0) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/RF_mm_syscalls__S3.v (assert)
example
    (a : Int)
    (on : Int)
    (old : Int)
    (nn : Int)
    (h1 : (0 ≤ (old + nn) ∧ (old + nn) < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ (on - nn) ∧ (on - nn) < (2 ^ (64 : Nat))))
    (h3 : ((old + nn) + (on - nn)) ≤ (2 ^ (64 : Nat)))
    (h4 : (0 ≤ (old + on) ∧ (old + on) < (2 ^ (64 : Nat))))
    (h5 : (0 ≤ (nn - on) ∧ (nn - on) < (2 ^ (64 : Nat))))
    (h6 : ((old + on) + (nn - on)) ≤ (2 ^ (64 : Nat)))
    (h7 : (0 ≤ old ∧ old < (2 ^ (64 : Nat))))
    (h8 : (old + on) ≤ (2 ^ (64 : Nat)))
    (h9 : (0 ≤ a ∧ a < (2 ^ (64 : Nat))))
    (h10 : (a + nn) < (2 ^ (64 : Nat)))
    (h11 : (0 ≤ on ∧ on < (2 ^ (64 : Nat))))
    (h12 : (on ≤ nn ∧ nn < (2 ^ (64 : Nat)))) :
    (0 ≤ (a + on) ∧ (a + on) < (2 ^ (64 : Nat))) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/S3/Startup_B__S3.v (assert)
example
    {word list_list_byte : Type}
    (sp0 : word)
    (argv : list_list_byte)
    (envp : list_list_byte)
    (tb : Int)
    (bv_unsigned : word → Int)
    (tpw : word)
    (alloc_ceiling : Int)
    (rnd_addr : word → list_list_byte → list_list_byte → Int)
    (argc : list_list_byte → Int)
    (length : list_list_byte → Nat)
    (envc : list_list_byte → Int)
    (P0 : Int)
    (h1 : alloc_ceiling ≤ ((bv_unsigned sp0) - 8388608))
    (h2 : (bv_unsigned sp0) ≤ (rnd_addr sp0 argv envp))
    (h3 : (argc argv) = (((length argv) : Nat) : Int))
    (h4 : (envc envp) = (((length envp) : Nat) : Int))
    (h5 : ((bv_unsigned sp0) + 184) ≤ P0)
    (h6 : (bv_unsigned tpw) = (tb + 200)) :
    tb = ((bv_unsigned tpw) - 200) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/Spec/LB_XferF__Spec.v (replace)
example
    {T1 : Type}
    (res' : Int)
    (snd : T1 → Int)
    (c : T1)
    (stride : Int)
    (IB : Int)
    (UNIT : Int)
    (off : Int)
    (n' : Int)
    (h1 : res' = (((stride - IB) - (UNIT * off)) - n')) :
    res' = (((((snd c) + stride) - IB) - ((snd c) + (UNIT * off))) - n') := by
  lia

-- libpcap/fuzz_pcap: lib/E2/Spec/MI_Realloc2__Spec.v (replace)
example
    (needed : Int)
    (IB : Int)
    (UNIT : Int)
    (nb : Int)
    (PGSZ : Int)
    (LEN_MAX : Int)
    (alloc_ceiling : Int)
    (h1 : (0 < nb ∧ (Int.fmod nb PGSZ) = 0))
    (h2 : (PGSZ ≤ needed ∧ ((Int.fmod needed PGSZ) = 0 ∧ (needed < LEN_MAX ∧ (nb + needed) ≤ alloc_ceiling)))) :
    (needed - IB) = ((UNIT + (needed - UNIT)) - IB) := by
  lia

-- libpcap/fuzz_pcap: lib/E2/U3/F_sfpcap_chkF__U3.v (replace)
example (a : Int) (b : Int) (h1 : (0 ≤ a ∧ a < 256)) (h2 : (0 ≤ b ∧ b < 256)) :
    (((a + (256 * b)) * (2 ^ (48 : Nat))) + (a * (2 ^ (64 : Nat)))) = (((a + (256 * b)) + (65536 * a)) * (2 ^ (48 : Nat))) := by
  lia

-- libpcap/fuzz_pcap: lib/Lib/NodesMmDrive__Lib.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (edenot : T2 → T3 → T1)
    (E : T2)
    (b : T3)
    (k : Int)
    (k' : Int)
    (i : Int) :
    (((bv_unsigned (edenot E b)) + k) + ((k' - k) + i)) = (((bv_unsigned (edenot E b)) + k') + i) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/AImgGlobals.v (replace)
example
    (x : Int)
    (a : Int)
    (n : Int)
    (h1 : (a / 8) ≤ (x / 8))
    (h2 : (x / 8) ≤ (((a + n) - 1) / 8)) :
    (x / 8) = ((a / 8) + (((Int.toNat ((x / 8) - (a / 8))) : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_ecp_point_free.v (replace)
example
    {art_layout T2 T3 : Type}
    (R : art_layout)
    (bv_unsigned : T2 → Int)
    (sp : T2)
    (arl_need_rt : art_layout → Int)
    (hl_img_lo : T3 → Int)
    (arl_L : art_layout → T3)
    (hl_data_lo : T3 → Int)
    (hl_data_hi : T3 → Int)
    (hl_img_hi : T3 → Int)
    (alloc_ceiling : Int)
    (h1 : 0 ≤ (arl_need_rt R))
    (h2 : ((hl_img_lo (arl_L R)) ≤ (hl_data_lo (arl_L R)) ∧ (hl_data_hi (arl_L R)) ≤ (hl_img_hi (arl_L R))))
    (h3 : alloc_ceiling ≤ (bv_unsigned sp)) :
    ((bv_unsigned sp) + (-16)) = ((bv_unsigned sp) - 16) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_imsetv.v (replace)
example
    {T1 T2 T3 : Type}
    (P : Int)
    (i : Int)
    (n : Int)
    (store_ok : T1 → T2 → T3 → Int → Bool)
    (asegs : T1)
    (m : T2)
    (Z_to_bv : Int → Int → T3)
    (m1 : T2)
    (h1 : (i + 16) ≤ n)
    (h2 : (store_ok asegs m (Z_to_bv 64 (P + i)) 8) = true)
    (h3 : (store_ok asegs m1 (Z_to_bv 64 ((P + i) + 8)) 8) = true) :
    (P + (i + 8)) = ((P + i) + 8) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_imsetv.v (replace)
example
    {T1 T2 T3 : Type}
    (i : Int)
    (n : Int)
    (store_ok : T1 → T2 → T3 → Int → Bool)
    (asegs : T1)
    (m : T2)
    (Z_to_bv : Int → Int → T3)
    (P : Int)
    (m1 : T2)
    (h1 : (i + 16) ≤ n)
    (h2 : (store_ok asegs m (Z_to_bv 64 (P + i)) 8) = true)
    (h3 : (store_ok asegs m1 (Z_to_bv 64 ((P + i) + 8)) 8) = true) :
    ((i + 8) + 8) = (i + 16) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_main_hdr.v (replace)
example
    {art_layout word T3 : Type}
    (R : art_layout)
    (sp0 : word)
    (TOP : Int)
    (STKHI : Int)
    (msp : Int)
    (al_sb : T3 → Int)
    (AL : T3)
    (al_gsb : T3 → Int)
    (arl_malloc : art_layout → Int)
    (arl_free : art_layout → Int)
    (arl_memcpy_i : art_layout → Int)
    (arl_tp : art_layout → Int)
    (bv_unsigned : word → Int)
    (arl_stklo : art_layout → Int)
    (h1 : (al_sb AL) = 2147450880)
    (h2 : (al_gsb AL) = 1074680)
    (h3 : (arl_malloc R) = 429836)
    (h4 : (arl_free R) = 429832)
    (h5 : (arl_memcpy_i R) = 424004)
    (h6 : (arl_tp R) = 6526608)
    (h7 : 140735340871680 ≤ (bv_unsigned sp0))
    (h8 : (bv_unsigned sp0) ≤ 140737488355328)
    (h9 : ((bv_unsigned sp0) % 16) = 0)
    (h10 : (arl_stklo R) = ((bv_unsigned sp0) - 8388608))
    (h11 : ((bv_unsigned sp0) - 48) ≤ TOP)
    (h12 : (bv_unsigned sp0) ≤ STKHI) :
    msp = ((msp + (-16)) + ((16 : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_main_loop.v (replace)
example (nb : Int) (buf : Int) (len : Int) :
    nb = (((buf + len) + nb) - (buf + len)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_main_loop.v (replace)
example
    {art_layout word list_byte T4 : Type}
    (R : art_layout)
    (sp0 : word)
    (fdata : list_byte)
    (TOP : Int)
    (STKHI : Int)
    (cap : Int)
    (Ab : Int)
    (al_sb : T4 → Int)
    (AL : T4)
    (al_gsb : T4 → Int)
    (arl_malloc : art_layout → Int)
    (arl_free : art_layout → Int)
    (arl_memcpy_i : art_layout → Int)
    (arl_tp : art_layout → Int)
    (bv_unsigned : word → Int)
    (arl_stklo : art_layout → Int)
    (w : Int)
    (len : Int)
    (nb : Int)
    (length : list_byte → Nat)
    (firstn : Nat → list_byte → list_byte)
    (h1 : (al_sb AL) = 2147450880)
    (h2 : (al_gsb AL) = 1074680)
    (h3 : (arl_malloc R) = 429836)
    (h4 : (arl_free R) = 429832)
    (h5 : (arl_memcpy_i R) = 424004)
    (h6 : (arl_tp R) = 6526608)
    (h7 : 140735340871680 ≤ (bv_unsigned sp0))
    (h8 : (bv_unsigned sp0) ≤ 140737488355328)
    (h9 : ((bv_unsigned sp0) % 16) = 0)
    (h10 : (arl_stklo R) = ((bv_unsigned sp0) - 8388608))
    (h11 : ((bv_unsigned sp0) - 48) ≤ TOP)
    (h12 : (bv_unsigned sp0) ≤ STKHI)
    (h13 : ((1 ≤ w ∧ w ≤ 65536) ∧ (len + w) ≤ cap))
    (h14 : len = (((length fdata) : Nat) : Int))
    (h15 : (len + nb) = cap)
    (h16 : (((length (firstn (Int.toNat (len + nb)) fdata)) : Nat) : Int) = cap) :
    cap = ((Ab + cap) - Ab) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_main_loop.v (replace)
example
    {art_layout word list_byte T4 : Type}
    (R : art_layout)
    (sp0 : word)
    (fdata : list_byte)
    (TOP : Int)
    (STKHI : Int)
    (cap : Int)
    (len : Int)
    (nb : Int)
    (al_sb : T4 → Int)
    (AL : T4)
    (al_gsb : T4 → Int)
    (arl_malloc : art_layout → Int)
    (arl_free : art_layout → Int)
    (arl_memcpy_i : art_layout → Int)
    (arl_tp : art_layout → Int)
    (bv_unsigned : word → Int)
    (arl_stklo : art_layout → Int)
    (w : Int)
    (length : list_byte → Nat)
    (firstn : Nat → list_byte → list_byte)
    (h1 : (al_sb AL) = 2147450880)
    (h2 : (al_gsb AL) = 1074680)
    (h3 : (arl_malloc R) = 429836)
    (h4 : (arl_free R) = 429832)
    (h5 : (arl_memcpy_i R) = 424004)
    (h6 : (arl_tp R) = 6526608)
    (h7 : 140735340871680 ≤ (bv_unsigned sp0))
    (h8 : (bv_unsigned sp0) ≤ 140737488355328)
    (h9 : ((bv_unsigned sp0) % 16) = 0)
    (h10 : (arl_stklo R) = ((bv_unsigned sp0) - 8388608))
    (h11 : ((bv_unsigned sp0) - 48) ≤ TOP)
    (h12 : (bv_unsigned sp0) ≤ STKHI)
    (h13 : ((1 ≤ w ∧ w ≤ 65536) ∧ (len + w) ≤ cap))
    (h14 : len = (((length fdata) : Nat) : Int))
    (h15 : (len + nb) = cap)
    (h16 : (((length (firstn (Int.toNat (len + nb)) fdata)) : Nat) : Int) = cap) :
    cap = (len + nb) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_main_loop.v (replace)
example
    {art_layout word list_byte T4 : Type}
    (R : art_layout)
    (sp0 : word)
    (fdata : list_byte)
    (TOP : Int)
    (STKHI : Int)
    (len : Int)
    (nb : Int)
    (cap : Int)
    (al_sb : T4 → Int)
    (AL : T4)
    (al_gsb : T4 → Int)
    (arl_malloc : art_layout → Int)
    (arl_free : art_layout → Int)
    (arl_memcpy_i : art_layout → Int)
    (arl_tp : art_layout → Int)
    (bv_unsigned : word → Int)
    (arl_stklo : art_layout → Int)
    (w : Int)
    (length : list_byte → Nat)
    (firstn : Nat → list_byte → list_byte)
    (h1 : (al_sb AL) = 2147450880)
    (h2 : (al_gsb AL) = 1074680)
    (h3 : (arl_malloc R) = 429836)
    (h4 : (arl_free R) = 429832)
    (h5 : (arl_memcpy_i R) = 424004)
    (h6 : (arl_tp R) = 6526608)
    (h7 : 140735340871680 ≤ (bv_unsigned sp0))
    (h8 : (bv_unsigned sp0) ≤ 140737488355328)
    (h9 : ((bv_unsigned sp0) % 16) = 0)
    (h10 : (arl_stklo R) = ((bv_unsigned sp0) - 8388608))
    (h11 : ((bv_unsigned sp0) - 48) ≤ TOP)
    (h12 : (bv_unsigned sp0) ≤ STKHI)
    (h13 : ((1 ≤ w ∧ w ≤ 65536) ∧ (len + w) ≤ cap))
    (h14 : len = (((length fdata) : Nat) : Int))
    (h15 : (len + nb) = cap)
    (h16 : (((length (firstn (Int.toNat (len + nb)) fdata)) : Nat) : Int) = cap) :
    (Int.toNat (len + nb)) = (Int.toNat cap) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_mpi_div_mpi_L_c24.v (replace)
example
    {art_layout artA_asegs_R HST_asegs_R_HIA list_blk word mpd T7 T8 : Type}
    (R : art_layout)
    (HIA : artA_asegs_R)
    (h_1 : HST_asegs_R_HIA)
    (LB : list_blk)
    (LF : list_blk)
    (ra : word)
    (sp : word)
    (X : Int)
    (A : Int)
    (B : Int)
    (lo : Int)
    (dX : mpd)
    (dA : mpd)
    (dB : mpd)
    (PHIb : Int)
    (FRb : Int)
    (sp1 : Int)
    (gapn : Nat)
    (slo : Int)
    (vy : Int)
    (idx : Int)
    (ny : Int)
    (i : Int)
    (arl_need_smalloc : art_layout → Int)
    (arl_need_rt : art_layout → Int)
    (arl_stklo : art_layout → Int)
    (bv_unsigned : word → Int)
    (MPI_DIV_MPI_STACK_A : Int)
    (htop : T7 → art_layout → artA_asegs_R → HST_asegs_R_HIA → Int)
    (asegs : T7)
    (length : list_blk → Nat)
    (md_addr : mpd → Int)
    (hl_img_lo : T8 → Int)
    (arl_L : art_layout → T8)
    (hl_data_lo : T8 → Int)
    (hl_data_hi : T8 → Int)
    (hl_img_hi : T8 → Int)
    (havol : T7 → art_layout → artA_asegs_R → HST_asegs_R_HIA → Int)
    (AVOL_MAX : Int)
    (hfr : T7 → art_layout → artA_asegs_R → HST_asegs_R_HIA → Int)
    (FR_MAX : Int)
    (cnt24 : list_blk → Int)
    (C24_DIV_MPI : Int)
    (C24MAX : Int)
    (Zpow : Int → Int → Int)
    (md_n : mpd → Int)
    (h1 : 0 ≤ (arl_need_smalloc R))
    (h2 : 0 ≤ (arl_need_rt R))
    (h3 : (arl_stklo R) ≤ lo)
    (h4 : lo ≤ (((bv_unsigned sp) - MPI_DIV_MPI_STACK_A) - (arl_need_rt R)))
    (h5 : lo ≤ (((bv_unsigned sp) - 320) - (arl_need_smalloc R)))
    (h6 : (bv_unsigned sp) ≤ (htop asegs R HIA h_1))
    (h7 : ((bv_unsigned sp) % 16) = 0)
    (h8 : (length LF) < 512)
    (h9 : X = (md_addr dX))
    (h10 : A = (md_addr dA))
    (h11 : B = (md_addr dB))
    (h12 : ((hl_img_lo (arl_L R)) ≤ (hl_data_lo (arl_L R)) ∧ (hl_data_hi (arl_L R)) ≤ (hl_img_hi (arl_L R))))
    (h13 : (((md_addr dX) + 16) ≤ lo ∨ (bv_unsigned sp) ≤ (md_addr dX)))
    (h14 : ((bv_unsigned ra) % 2) = 0)
    (h15 : (((bv_unsigned sp) - 304) ≤ sp1 ∧ sp1 ≤ ((bv_unsigned sp) - 288)))
    (h16 : (sp1 % 32) = 0)
    (h17 : ((gapn : Nat) : Int) = (((bv_unsigned sp) + (-104)) - (sp1 + 184)))
    (h18 : ((havol asegs R HIA h_1) + PHIb) ≤ AVOL_MAX)
    (h19 : ((hfr asegs R HIA h_1) + FRb) ≤ FR_MAX)
    (h20 : ((cnt24 LB) + C24_DIV_MPI) ≤ C24MAX)
    (h21 : (arl_stklo R) ≤ slo)
    (h22 : slo ≤ lo)
    (h23 : ((vy).natAbs : Int) < (Zpow 2 (32 * ny)))
    (h24 : 0 ≤ ny)
    (h25 : 0 ≤ idx)
    (h26 : (ny + idx) = i)
    (h27 : i ≤ (md_n dA))
    (h28 : (Zpow 2 (32 * (i + 1))) = (((Zpow 2 (32 * ny)) * 4294967296) * (Zpow 2 (idx * 32)))) :
    (((32 * ny) + 32) + (idx * 32)) = (32 * (i + 1)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_mpi_grow.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (lo : Int)
    (X : Int)
    (asegs : T2)
    (n : Int)
    (P : Int)
    (htop : T2 → T3 → T4 → T5 → Int)
    (R : T3)
    (HIA : T4)
    (h2 : T5)
    (A : Int)
    (nb : Int)
    (h4 : T5)
    (h1 : ((X + 16) ≤ lo ∨ (bv_unsigned sp) ≤ X))
    (h2_1 : (bv_unsigned sp) ≤ (htop asegs R HIA h2))
    (h3 : ((X + 16) ≤ A ∨ (A + (4 * nb)) ≤ X))
    (h4_1 : (A + (4 * nb)) ≤ lo)
    (h5 : ((A + (4 * nb)) ≤ P ∨ (P + (4 * n)) ≤ A))
    (h6 : (bv_unsigned sp) ≤ (htop asegs R HIA h4)) :
    (bv_unsigned sp) = (lo + ((bv_unsigned sp) - lo)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_mpi_read_binary_c24.v (replace)
example
    {art_layout artA_asegs_R T3 T4 T5 T6 T7 : Type}
    (R : art_layout)
    (HIA : artA_asegs_R)
    (bv_unsigned : T3 → Int)
    (sp : T3)
    (lo : Int)
    (arl_need_rt : art_layout → Int)
    (asegs : T4)
    (hl_img_lo : T5 → Int)
    (arl_L : art_layout → T5)
    (hl_data_lo : T5 → Int)
    (hl_data_hi : T5 → Int)
    (hl_img_hi : T5 → Int)
    (X : Int)
    (len : Int)
    (length : T6 → Nat)
    (ibs : T6)
    (chars_to_limbs4 : Int → Int)
    (htop : T4 → art_layout → artA_asegs_R → T7 → Int)
    (h2 : T7)
    (read_be_ret : Int → Int → Int)
    (B : Int)
    (p2 : Int)
    (h1 : 0 ≤ (arl_need_rt R))
    (h2_1 : ((hl_img_lo (arl_L R)) ≤ (hl_data_lo (arl_L R)) ∧ (hl_data_hi (arl_L R)) ≤ (hl_img_hi (arl_L R))))
    (h3 : 0 ≤ lo)
    (h4 : ((X + 16) ≤ lo ∨ (bv_unsigned sp) ≤ X))
    (h5 : len = (((length ibs) : Nat) : Int))
    (h6 : (0 ≤ (chars_to_limbs4 len) ∧ ((4 * (chars_to_limbs4 len)) ≤ (len + 3) ∧ len ≤ (4 * (chars_to_limbs4 len)))))
    (h7 : ((chars_to_limbs4 len) = 0 ↔ len = 0))
    (h8 : (bv_unsigned sp) ≤ (htop asegs R HIA h2))
    (h9 : (read_be_ret (chars_to_limbs4 len) len) = 0)
    (h10 : len = 0)
    (h11 : 1 ≤ len)
    (h12 : ((B + len) ≤ p2 ∨ (p2 + (4 * (chars_to_limbs4 len))) ≤ B))
    (h13 : ((X + 16) ≤ p2 ∨ (p2 + (4 * (chars_to_limbs4 len))) ≤ X))
    (h14 : (p2 + (4 * (chars_to_limbs4 len))) ≤ lo) :
    (bv_unsigned sp) = (lo + ((bv_unsigned sp) - lo)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_mpi_read_binary_c24.v (replace)
example
    {art_layout artA_asegs_R T3 T4 T5 T6 T7 : Type}
    (R : art_layout)
    (HIA : artA_asegs_R)
    (chars_to_limbs4 : Int → Int)
    (len : Int)
    (p2 : Int)
    (arl_need_rt : art_layout → Int)
    (asegs : T3)
    (hl_img_lo : T4 → Int)
    (arl_L : art_layout → T4)
    (hl_data_lo : T4 → Int)
    (hl_data_hi : T4 → Int)
    (hl_img_hi : T4 → Int)
    (lo : Int)
    (bv_unsigned : T5 → Int)
    (sp : T5)
    (X : Int)
    (length : T6 → Nat)
    (ibs : T6)
    (htop : T3 → art_layout → artA_asegs_R → T7 → Int)
    (h2 : T7)
    (read_be_ret : Int → Int → Int)
    (B : Int)
    (h1 : 0 ≤ (arl_need_rt R))
    (h2_1 : ((hl_img_lo (arl_L R)) ≤ (hl_data_lo (arl_L R)) ∧ (hl_data_hi (arl_L R)) ≤ (hl_img_hi (arl_L R))))
    (h3 : 0 ≤ lo)
    (h4 : ((X + 16) ≤ lo ∨ (bv_unsigned sp) ≤ X))
    (h5 : len = (((length ibs) : Nat) : Int))
    (h6 : (0 ≤ (chars_to_limbs4 len) ∧ ((4 * (chars_to_limbs4 len)) ≤ (len + 3) ∧ len ≤ (4 * (chars_to_limbs4 len)))))
    (h7 : ((chars_to_limbs4 len) = 0 ↔ len = 0))
    (h8 : (bv_unsigned sp) ≤ (htop asegs R HIA h2))
    (h9 : (read_be_ret (chars_to_limbs4 len) len) = 0)
    (h10 : len = 0)
    (h11 : 1 ≤ len)
    (h12 : ((B + len) ≤ p2 ∨ (p2 + (4 * (chars_to_limbs4 len))) ≤ B))
    (h13 : ((X + 16) ≤ p2 ∨ (p2 + (4 * (chars_to_limbs4 len))) ≤ X))
    (h14 : (p2 + (4 * (chars_to_limbs4 len))) ≤ lo) :
    (4 * (chars_to_limbs4 len)) = ((p2 + (4 * (chars_to_limbs4 len))) - p2) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_mpi_shrink.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (lo : Int)
    (havol : T2 → T3 → T4 → T5 → Int)
    (asegs : T2)
    (R : T3)
    (HIA : T4)
    (h_1 : T5)
    (k : Int)
    (AVOL_CALL : Int)
    (AVOL_MAX : Int)
    (htop : T2 → T3 → T4 → T6 → Int)
    (h2 : T6)
    (X : Int)
    (n : Int)
    (P : Int)
    (limbs : T7)
    (A : Int)
    (length : T8 → Nat)
    (firstn : Nat → T7 → T8)
    (h4 : T6)
    (h1 : ((havol asegs R HIA h_1) + ((8 * k) + (2 * AVOL_CALL))) ≤ AVOL_MAX)
    (h2_1 : (bv_unsigned sp) ≤ (htop asegs R HIA h2))
    (h3 : ((X + 16) ≤ A ∨ (A + (4 * k)) ≤ X))
    (h4_1 : (A + (4 * k)) ≤ lo)
    (h5 : ((A + (4 * k)) ≤ P ∨ (P + (4 * n)) ≤ A))
    (h6 : (length (firstn (Int.toNat k) limbs)) = (Int.toNat k))
    (h7 : (bv_unsigned sp) ≤ (htop asegs R HIA h4)) :
    (bv_unsigned sp) = (lo + ((bv_unsigned sp) - lo)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_mpi_sub_int_sz_c24.v (replace)
example
    (b : Int)
    (h1 : (Int.fdiv b (2 ^ (31 : Nat))) = (-1))
    (h2 : (Int.fmod b (2 ^ (64 : Nat))) = ((2 ^ (64 : Nat)) + b))
    (h3 : ((Int.fmod (((2 ^ (64 : Nat)) + b) + (2 ^ (31 : Nat))) (2 ^ (32 : Nat))) - (2 ^ (31 : Nat))) = b) :
    ((b + (2 ^ (31 : Nat))) + ((2 ^ (32 : Nat)) * (2 ^ (32 : Nat)))) = (((2 ^ (64 : Nat)) + b) + (2 ^ (31 : Nat))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_pk_setup.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (lo : Int)
    (PKA : Int)
    (Z_shiftr : Int → Int → Int)
    (info : Int)
    (C : Int)
    (h1 : 0 ≤ lo)
    (h2 : (PKA + 16) ≤ (2 ^ (47 : Nat)))
    (h3 : (0 ≤ (Z_shiftr PKA 3) ∧ (Z_shiftr PKA 3) < (2 ^ (44 : Nat))))
    (h4 : (978496 ≤ info ∧ info ≤ 978752))
    (h5 : (info % 64) = 0)
    (h6 : (0 < info ∧ info < (2 ^ (32 : Nat))))
    (h7 : ((C + 256) ≤ PKA ∨ (PKA + 16) ≤ C))
    (h8 : ((C + 256) ≤ lo ∨ (bv_unsigned sp) ≤ C)) :
    (bv_unsigned sp) = (lo + ((bv_unsigned sp) - lo)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_refused.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (edenot : T2 → T3 → T1)
    (E : T2)
    (b : T3)
    (k : Int) :
    ((bv_unsigned (edenot E b)) + (k + 1)) = (((bv_unsigned (edenot E b)) + k) + ((1 : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_tail_openfail.v (replace)
example
    {art_layout word list_byte T4 : Type}
    (R : art_layout)
    (sp0 : word)
    (path : list_byte)
    (pathp : word)
    (STKHI : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (al_sb : T4 → Int)
    (AL : T4)
    (arl_stklo : art_layout → Int)
    (spw : word)
    (msp : Int)
    (lo : Int)
    (g : Int)
    (h1 : (al_sb AL) = 2147450880)
    (h2 : 140735340871680 ≤ (bv_unsigned sp0))
    (h3 : (bv_unsigned sp0) ≤ 140737488355328)
    (h4 : ((bv_unsigned sp0) % 16) = 0)
    (h5 : (arl_stklo R) = ((bv_unsigned sp0) - 8388608))
    (h6 : (bv_unsigned sp0) ≤ STKHI)
    (h7 : STKHI ≤ (2 ^ (47 : Nat)))
    (h8 : (STKHI % 64) = 0)
    (h9 : (bv_unsigned spw) = msp)
    (h10 : (140735324094464 + 16384) ≤ (bv_unsigned spw))
    (h11 : ((bv_unsigned spw) + 128) ≤ 140737488355328)
    (h12 : ((bv_unsigned spw) % 16) = 0)
    (h13 : 17594333495295 < lo)
    (h14 : (lo + 16384) ≤ (bv_unsigned spw))
    (h15 : ((bv_unsigned spw) - 8388608) ≤ lo)
    (h16 : ((bv_unsigned spw) + 128) ≤ STKHI)
    (h17 : STKHI ≤ 140737488355328)
    (h18 : (lo % 8) = 0)
    (h19 : (lo ≤ g ∧ ((g + 8) ≤ STKHI ∧ (g % 8) = 0))) :
    (((bv_unsigned pathp) + (((length path) : Nat) : Int)) + 1) = ((bv_unsigned pathp) + ((((length path) + 1) : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/A/A_tail_usage_S8.v (replace)
example
    {word list_byte : Type}
    (sp0 : word)
    (lo : Int)
    (STKHI : Int)
    (P : word)
    (path : list_byte)
    (bv_unsigned : word → Int)
    (L : Int)
    (length : list_byte → Nat)
    (buf : list_byte)
    (h1 : (140735324094464 + 16384) ≤ (bv_unsigned sp0))
    (h2 : ((bv_unsigned sp0) + 128) ≤ 140737488355328)
    (h3 : ((bv_unsigned sp0) % 16) = 0)
    (h4 : 17594333495295 < lo)
    (h5 : (lo + 16384) ≤ (bv_unsigned sp0))
    (h6 : ((bv_unsigned sp0) - 8388608) ≤ lo)
    (h7 : ((bv_unsigned sp0) + 144) ≤ STKHI)
    (h8 : STKHI ≤ 140737488355328)
    (h9 : (STKHI % 64) = 0)
    (h10 : (((((bv_unsigned P) + L) / 8) * 8) + 8) ≤ ((bv_unsigned P) + (((length buf) : Nat) : Int)))
    (h11 : ((bv_unsigned sp0) + 128) ≤ (bv_unsigned P))
    (h12 : ((bv_unsigned P) + (((length buf) : Nat) : Int)) ≤ STKHI)
    (h13 : (((bv_unsigned P) + L) + 16) ≤ STKHI)
    (h14 : L ≤ 131071)
    (h15 : (67 ≤ L ∧ L ≤ 73))
    (h16 : L = (((length path) : Nat) : Int)) :
    ((bv_unsigned sp0) - 457) = (((bv_unsigned sp0) + (-464)) + 7) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AH0Layout.v (replace)
example
    {me_params T2 T3 : Type}
    (p : me_params)
    (STKHI : Int)
    (uv : me_params → T2 → Int)
    (v_s1 : T2)
    (v_s2 : T2)
    (ACEIL : Int)
    (STKPG : me_params → Int)
    (SP : Int)
    (PG : me_params → T3 → Int)
    (v_prim : T3)
    (v_pslack : T3)
    (v_tpg : T2)
    (h1 : ACEIL = ((STKPG p) - 8388608))
    (h2 : SP < STKHI)
    (h3 : (STKHI % 4096) = 0)
    (h4 : STKHI ≤ (2 ^ (47 : Nat)))
    (h5 : STKHI ≤ (SP + (2 ^ (23 : Nat))))
    (h6 : ((STKPG p) ≤ SP ∧ SP < ((STKPG p) + 4096)))
    (h7 : (Int.fmod (((PG p v_prim) - (PG p v_pslack)) + 65536) (2 ^ (16 : Nat))) = 0)
    (h8 : (((32768 * (uv p v_s1)) + (4096 * (uv p v_tpg))) % 4096) = 0)
    (h9 : ((((32768 * (uv p v_s1)) + (16 * (uv p v_s2))) - 48) % 16) = 0)
    (h10 : ((((32768 * (uv p v_s1)) + (16 * (uv p v_s2))) - (2 ^ (23 : Nat))) % 16) = 0) :
    ((((2048 * (uv p v_s1)) + (uv p v_s2)) - (2 ^ (19 : Nat))) * 16) = (((32768 * (uv p v_s1)) + (16 * (uv p v_s2))) - (2 ^ (23 : Nat))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AJTop.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (h_1 : T1)
    (t : T2)
    (fa_beg : T3 → T4 → Int)
    (h_L : T1 → T3)
    (c : T4)
    (j : Int)
    (kUserMapSize : Int)
    (t_lit : T2 → Bool)
    (r_mapped_user : T5 → Int)
    (h_reg : T1 → T4 → T5)
    (h1 : (t_lit t) = false)
    (h2 : (j + 1) ≤ (Int.fdiv (r_mapped_user (h_reg h_1 c)) (2 ^ (18 : Nat)))) :
    ((fa_beg (h_L h_1) c) + (j * kUserMapSize)) = ((fa_beg (h_L h_1) c) + (j * kUserMapSize)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AModelX.v (assert)
example (c : Int) (Zpow : Int → Int → Int) (h1 : (1 ≤ c ∧ c ≤ 31)) (h2 : 0 ≤ ((c - 16) / 2)) :
    (512 * (Zpow 2 ((c - 16) / 2))) = ((256 * (Zpow 2 ((c - 16) / 2))) * 2) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AW_B12WalkP.v (replace)
example (SP0 : Int) :
    (((SP0 + (-640)) + (-128)) + (-48)) = ((SP0 + (-640)) + (-176)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AW_CbRecycle.v (replace)
example
    (mq : Int)
    (kk : Int)
    (n : Int)
    (rz_size : Int → Int)
    (R : Int)
    (k : Int)
    (sz : Int)
    (c : Int)
    (SB : Int)
    (AB : Int)
    (m : Int)
    (h1 : kk = ((n + 7) / 8))
    (h2 : (16 ≤ (rz_size n) ∧ (rz_size n) ≤ 2048))
    (h3 : ((rz_size n) % 16) = 0)
    (h4 : (0 ≤ kk ∧ (n ≤ (8 * kk) ∧ (8 * kk) < (n + 8))))
    (h5 : R = ((k * sz) + ((rz_size n) - 16)))
    (h6 : (0 ≤ R ∧ R < 4294967296))
    (h7 : k < 134217728)
    (h8 : (Int.fdiv (Int.fmod ((c * 4294967296) + R) (2 ^ (32 : Nat))) sz) = k)
    (h9 : (sz % 16) = 0)
    (h10 : ((SB + 4294967296) ≤ AB ∧ (AB + sz) ≤ (SB + 133143986176)))
    (h11 : (c * 4294967296) ≤ (30 * 4294967296))
    (h12 : ((k * sz) + sz) ≤ 3758096384)
    (h13 : ((AB + 16) ≤ (m + 16) ∧ ((m + 16) + (8 * kk)) ≤ (AB + sz))) :
    ((mq * 4) * 4) = (16 * mq) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AW_DepotC.v (replace)
example (tf : Int) (count : Int) :
    ((tf + count) - 1) = ((count + (-1)) + tf) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AW_FreePhP.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (region_beg : T1 → T2 → Int)
    (h_L : T3 → T1)
    (h_1 : T3)
    (ck_cls : T4 → T2)
    (k : T4)
    (i : Int)
    (class_size : T2 → Int)
    (rz_size : T5 → Int)
    (ck_n : T4 → T5) :
    (((((region_beg (h_L h_1) (ck_cls k)) / 16) + (i * ((class_size (ck_cls k)) / 16))) + ((rz_size (ck_n k)) / 16)) * 16) = (((16 * ((region_beg (h_L h_1) (ck_cls k)) / 16)) + (i * (16 * ((class_size (ck_cls k)) / 16)))) + (16 * ((rz_size (ck_n k)) / 16))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AW_IMemmove.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (D : Int)
    (i : Int)
    (store_ok : T1 → T2 → T3 → Int → Bool)
    (asegs : T1)
    (m : T2)
    (Z_to_bv : Int → Int → T3)
    (length : T4 → Nat)
    (firstn : Nat → T5 → T4)
    (ss : T5)
    (h1 : (store_ok asegs m (Z_to_bv 64 (D + i)) 1) = true)
    (h2 : (length (firstn (Int.toNat i) ss)) = (Int.toNat i)) :
    (D + (i + 1)) = ((D + i) + ((1 : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AW_PfVsn.v (replace)
example
    {T1 T2 : Type}
    (BUF : Int)
    (off : Int)
    (length : T1 → Nat)
    (lit : T1)
    (upd : T1 → Nat → T2 → T1)
    (bs : T1)
    (b : T2)
    (h1 : (length (upd bs (Int.toNat off) b)) = (length bs)) :
    ((BUF + (off + 1)) + (((length lit) : Nat) : Int)) = ((BUF + off) + ((((length lit) : Nat) : Int) + 1)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/AHeap/AW_SecC.v (replace)
example
    (STK : Int)
    (lo : Int)
    (SPA : Int)
    (AB : Int)
    (a : Int)
    (UB : Int)
    (rz_size : Int → Int)
    (n : Int)
    (CHB : Int)
    (rd : Int)
    (nfix : Int → Int)
    (PGS : Int)
    (Z_shiftr : Int → Int → Int)
    (needed2 : Int → Int)
    (ACEIL : Int)
    (h1 : lo ≤ (SPA - 512))
    (h2 : SPA ≤ (2 ^ (62 : Nat)))
    (h3 : (SPA % 16) = 0)
    (h4 : AB = (a + 4096))
    (h5 : UB = (AB + (rz_size n)))
    (h6 : CHB = ((AB + (rz_size n)) + (-16)))
    (h7 : rd = (((nfix n) / 8) * 8))
    (h8 : PGS = (2147450880 + (Z_shiftr (UB + rd) 3)))
    (h9 : 6664192 ≤ AB)
    (h10 : (AB + (needed2 n)) ≤ ACEIL)
    (h11 : (AB % 16) = 0)
    (h12 : ((AB + (needed2 n)) ≤ 2147450880 ∨ (17594333495296 ≤ AB ∧ (AB + (needed2 n)) ≤ ACEIL)))
    (h13 : (Z_shiftr (UB + rd) 3) = (((a / 8) + 768) + ((nfix n) / 8)))
    (h14 : (min (nfix n) 4096) = 4096) :
    (STK + 2064) = ((((STK + ((16 : Nat) : Int)) + (((8 * 30) : Nat) : Int)) + ((1800 : Nat) : Int)) + ((8 : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/BB/SymExec.v (replace)
example (n : Nat) :
    ((8 * ((n : Nat) : Int)) + 8) = (8 * (((n + 1) : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/Heap/KCost.v (replace)
example {T1 : Type} (K2 : Nat) (C2 : Int) (K : Nat) (emaps : T1 → Nat) (e : T1) (h1 : 0 ≤ C2) :
    ((K + K2) + (emaps e)) = ((K + (emaps e)) + K2) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/Heap/MStrat.v (replace)
example (N_1 : Nat) (B : Int) (MA : Int) (h1 : 0 ≤ (B + MA)) :
    ((N_1 + 1) + 0) = (N_1 + 1) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/LX/LxSoundStep.v (replace)
example (k : Int) (x : Int) (Zpow : Int → Int → Int) :
    (Int.fmod (x + (Zpow 2 (k - 1))) (Zpow 2 k)) = (((Int.fmod (x + (Zpow 2 (k - 1))) (Zpow 2 k)) - (Zpow 2 (k - 1))) + (Zpow 2 (k - 1))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/LX/LxSoundSum.v (replace)
example {env T2 : Type} (E : env) (zden : env → T2 → Int) (hi : T2) (lo : T2) :
    ((zden E hi) + ((-1) * (zden E lo))) = ((zden E hi) - (zden E lo)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/LX/LxSoundSum.v (replace)
example
    {env lxcfg list_pfact list_mfact list___expr_expr T6 T7 : Type}
    (E : env)
    (C : lxcfg)
    (pf : list_pfact)
    (mf : list_mfact)
    (W : list___expr_expr)
    (l : Nat)
    (dp : Bool)
    (crs : list___expr_expr)
    (wcl : Bool)
    (wne : Bool)
    (f : T6)
    (zden : env → T7 → Int)
    (hi : T7)
    (lo : T7)
    (law_survives : Bool → lxcfg → Nat → list_pfact → list___expr_expr → list_mfact → list___expr_expr → Bool → Bool → T6 → Bool)
    (h1 : (law_survives dp C l pf crs mf W wcl wne f) = true) :
    ((zden E hi) + ((-1) * (zden E lo))) = ((zden E hi) - (zden E lo)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/LX/LxTac.v (lemma)
example
    (z1 : Int)
    (z2 : Int)
    (a : Int)
    (b : Int)
    (c : Int)
    (d : Int)
    (h1 : ((a ≤ b ∧ c ≤ d) ∨ (z1 = 0 ∧ z2 = 0))) :
    ((z1 = 0 ∨ (a ≤ b ∨ a ≤ b)) ∧ ((z1 = 0 ∨ (c ≤ d ∨ c ≤ d)) ∧ ((z2 = 0 ∨ (a ≤ b ∨ a ≤ b)) ∧ (z2 = 0 ∨ (c ≤ d ∨ c ≤ d))))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/LXA/LxAEcpSums.v (replace)
example (d : Int) (D : Int) (i : Int) (h1 : d = (D + (4 * i))) (h2 : 0 ≤ i) :
    d = (D + (4 * (((Int.toNat i) : Nat) : Int))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/LXA/LxAEcpSums.v (replace)
example
    (d : Int)
    (X : Int)
    (i : Int)
    (s : Int)
    (j : Int)
    (h1 : d = (X + (4 * i)))
    (h2 : s = (X + (4 * j)))
    (h3 : 0 ≤ i)
    (h4 : 0 ≤ j) :
    d = (X + (4 * (((Int.toNat i) : Nat) : Int))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/LXA/LxAEcpSums.v (replace)
example
    (s : Int)
    (X : Int)
    (j : Int)
    (d : Int)
    (i : Int)
    (h1 : d = (X + (4 * i)))
    (h2 : s = (X + (4 * j)))
    (h3 : 0 ≤ i)
    (h4 : 0 ≤ j) :
    s = (X + (4 * (((Int.toNat j) : Nat) : Int))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/LXP/LxPMpiTac.v (replace)
example {T1 : Type} (i : Int) (length : T1 → Nat) (ws : T1) (h1 : (Int.toNat i) < (length ws)) :
    ((4 * i) + (4 + (((4 * (((length ws) : Nat) : Int)) - (4 * i)) - 4))) = (4 * (((length ws) : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/Lib/MpiCoreAux.v (replace)
example
    {word : Type}
    (w : word)
    (x : Int)
    (b : Int)
    (i : Int)
    (bv_unsigned : word → Int)
    (Z_log2 : Int → Int)
    (Z_testbit : Int → Int → Bool)
    (h1 : x = (Int.fmod (bv_unsigned w) (2 ^ (32 : Nat))))
    (h2 : x ≠ 0)
    (h3 : b = (Z_log2 x))
    (h4 : (0 ≤ b ∧ b ≤ 31))
    (h5 : (Z_testbit x 31) = (b == 31))
    (h6 : (2 ^ (31 : Nat)) ≤ x)
    (h7 : x < (2 ^ (31 : Nat)))
    (h8 : i = b) :
    (32 + (i - 32)) = i := by
  lia

-- mbedtls/fuzz_pkcs7: lib/Lib/X509Aux.v (replace)
example
    (r : Int)
    (c : Int)
    (h1 : ((-65536) < r ∧ r ≤ 0))
    (h2 : (((2 ^ (64 : Nat)) - 65536) ≤ c ∧ c < (2 ^ (64 : Nat))))
    (h3 : ((Int.fmod r (2 ^ (64 : Nat))) = (r + 18446744073709551616) ∨ (Int.fmod r (2 ^ (64 : Nat))) = r)) :
    (((r + (c - (2 ^ (64 : Nat)))) + 2147483648) + (8589934592 * 4294967296)) = (((r + 18446744073709551616) + c) + 2147483648) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/HP_RASlot_M5S.v (replace)
example
    {word T2 T3 T4 T5 T6 : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (bv_unsigned : word → Int)
    (size_class : Int → Int)
    (rceil : Int)
    (RAS_STACK : Int → Int)
    (ncls : Int → Int → Int)
    (cnt1 : Int)
    (st3 : T2)
    (mm : T3)
    (conc : T2 → T3 → Int)
    (st2 : T2)
    (szc : Int)
    (strideg : Int)
    (g3 : T3)
    (b3 : T3)
    (r3 : T4)
    (idx : Int)
    (r_base : T4 → Int)
    (snd : T3 → Int)
    (p : T3)
    (X : Int)
    (round_up_pg : T5 → Int)
    (r_len : T4 → T5)
    (m_last_idx : T6 → Int)
    (get_meta_rec : T2 → T3 → T6)
    (stT : T2)
    (usage : T2 → Int → Int)
    (P : Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : rceil ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (RAS_STACK sc)))
    (h6 : (conc st3 mm) = (conc st2 mm))
    (h7 : (((16 * szc) * cnt1) + 16) ≤ strideg)
    (h8 : (16 * szc) ≤ ((16 * szc) * cnt1))
    (h9 : (conc st3 b3) = ((r_base r3) + (snd b3)))
    (h10 : (conc st3 p) = ((r_base r3) + X))
    (h11 : 0 ≤ (strideg * idx))
    (h12 : (X + strideg) ≤ (round_up_pg (r_len r3)))
    (h13 : ((strideg * idx) + strideg) ≤ (strideg * ((m_last_idx (get_meta_rec st3 g3)) + 1)))
    (h14 : (0 ≤ (ncls sc cnt1) ∧ (ncls sc cnt1) < 48))
    (h15 : (0 ≤ (usage stT sc) ∧ (usage stT sc) < (2 ^ (60 : Nat))))
    (h16 : P = ((r_base r3) + X)) :
    ((bv_unsigned sp) - 144) = ((bv_unsigned sp) + (-144)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/HP_RF_ntf.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (conc : T1 → T2 → Int)
    (stU : T1)
    (p : T2)
    (lo : Int)
    (bv_unsigned : T3 → Int)
    (sp : T3)
    (g : T4)
    (get_meta_rec : T1 → T4 → T5)
    (stX : T1)
    (m_last_idx : T5 → Int)
    (stG : T1)
    (m_maplen : T5 → Int)
    (r : T6)
    (snd : T2 → Int)
    (sstart_of : T5 → Int → Int)
    (g1 : T4)
    (i1 : Int)
    (b1 : T2)
    (get_stride : T5 → Int)
    (round_up_pg : T7 → Int)
    (r_len : T6 → T7)
    (h1 : lo ≤ ((bv_unsigned sp) - 96))
    (h2 : (m_maplen (get_meta_rec stG g)) ≠ 0)
    (h3 : (m_maplen (get_meta_rec stG g)) = 0)
    (h4 : (snd p) = (sstart_of (get_meta_rec stX g1) i1))
    (h5 : ((snd b1) + 16) ≤ (snd p))
    (h6 : 0 ≤ ((get_stride (get_meta_rec stX g1)) * i1))
    (h7 : (0 ≤ ((snd p) - 4) ∧ (snd p) < (round_up_pg (r_len r))))
    (h8 : 0 ≤ ((get_stride (get_meta_rec stG g)) * ((m_last_idx (get_meta_rec stG g)) + 1))) :
    ((conc stU p) - 2) = ((((conc stU p) - 4) + 1) + 1) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/P_main_body.v (replace)
example (d : Int) :
    (Int.toNat (2 * (d - 1))) = (2 * (Int.toNat (d - 1))) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/P_main_body.v (replace)
example (d : Int) :
    (Int.toNat ((d + 2) - 1)) = ((Int.toNat (d + 1)) + 0) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/P_main_file.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (buf : Int)
    (len : Int)
    (length : T1 → Nat)
    (fdata : T1)
    (psegs : T2)
    (m : T3)
    (store_ok : T2 → T3 → T4 → Nat → Bool)
    (Z_to_bv : Int → Int → T4)
    (w : Int)
    (nb : Int)
    (bv_lts : T4 → T4 → Bool)
    (h1 : (store_ok psegs m (Z_to_bv 64 301161) (Int.toNat w)) = true)
    (h2 : (bv_lts (Z_to_bv 64 nb) (Z_to_bv 64 0)) = false)
    (h3 : len = (((length fdata) : Nat) : Int)) :
    (buf + len) = (buf + (((min (Int.toNat len) (length fdata)) : Nat) : Int)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/P_main_file.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (cap : Int)
    (len : Int)
    (psegs : T1)
    (m : T2)
    (store_ok : T1 → T2 → T3 → Nat → Bool)
    (Z_to_bv : Int → Int → T3)
    (w : Int)
    (nb : Int)
    (fdata : T4)
    (bv_lts : T3 → T3 → Bool)
    (length : T4 → Nat)
    (h1 : (store_ok psegs m (Z_to_bv 64 301161) (Int.toNat w)) = true)
    (h2 : (bv_lts (Z_to_bv 64 nb) (Z_to_bv 64 0)) = false)
    (h3 : len = (((length fdata) : Nat) : Int)) :
    (cap - len) = (cap + (-len)) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/P_mpi_div_mpi.v (replace)
example (N_1 : Nat) :
    ((((N_1 + 1) : Nat) : Int) - 1) = ((N_1 : Nat) : Int) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/P_mpi_exp_mod.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    (((bv_unsigned sp) + (-96)) + (-192)) = (((bv_unsigned sp) + (-96)) - 192) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/P/P_stdio_readerr_tail.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (bv_unsigned : T1 → Int)
    (sp0 : T1)
    (P : Int)
    (store_ok : T2 → T3 → T4 → Nat → Bool)
    (RSEGS : T2)
    (M' : T3)
    (dst : T4)
    (h1 : (store_ok RSEGS M' dst 1) = true) :
    ((bv_unsigned sp0) + ((-541) + P)) = (((bv_unsigned sp0) - 541) + P) := by
  lia

-- mbedtls/fuzz_pkcs7: lib/Spec/MpiClient.v (replace)
example
    {T1 : Type}
    (n : Int)
    (md_addr : T1 → Int)
    (d : T1)
    (A : Int)
    (h1 : (((md_addr d) + 16) ≤ A ∨ (A + (4 * n)) ≤ (md_addr d))) :
    (Int.toNat (4 * n)) = (4 * (Int.toNat n)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/ALib/InitMem.v (replace)
example {T1 T2 : Type} (bv_unsigned : T1 → Int) (sp : T1) (length : T2 → Nat) (argv : T2) :
    (((bv_unsigned sp) + ((8 : Nat) : Int)) + (((8 * (length argv)) : Nat) : Int)) = (((bv_unsigned sp) + 8) + (((8 * (length argv)) : Nat) : Int)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/AsanW/ACallocG.v (replace)
example
    {alayout word astate T4 : Type}
    (L : alayout)
    (sp : word)
    (st : astate)
    (c : Int)
    (lo : Int)
    (size : Int)
    (bv_unsigned : word → Int)
    (ATOP : Int)
    (al_t : alayout → Int)
    (class_id : Int → Int)
    (K_BATCH_CLASS : Int)
    (K_NUM_CLASSES : Int)
    (acache_addr : alayout → Int → Int)
    (c_count : T4 → Int)
    (get_cls : astate → Int → T4)
    (aregion_info : alayout → Int → Int)
    (aregion : alayout → Int → Int)
    (K_REGION : Int)
    (shad : Int → Int)
    (shlen : Int → Int)
    (h1 : ATOP ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 1584))
    (h3 : (16 ≤ size ∧ size ≤ 65536))
    (h4 : (size % 8) = 0)
    (h5 : (class_id size) = c)
    (h6 : c = K_BATCH_CLASS)
    (h7 : (1 ≤ c ∧ c ≤ 30))
    (h8 : (1 ≤ c ∧ c < K_NUM_CLASSES))
    (h9 : (acache_addr L c) = (((al_t L) + 208) + (c * 80)))
    (h10 : (c_count (get_cls st c)) = 0)
    (h11 : (((aregion_info L c) + 128) ≤ ATOP ∧ (((aregion L c) + K_REGION) ≤ ATOP ∧ ((shad (aregion L c)) + (shlen K_REGION)) ≤ 17594333495296))) :
    ((bv_unsigned sp) + (-48)) = ((bv_unsigned sp) - 48) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/AsanW/AFake_arep.v (replace)
example
    {T1 : Type}
    (F : Int)
    (jn : Nat)
    (jz : Int)
    (Z_land : Int → Int → Int)
    (h_1 : Int)
    (pos : Int)
    (flag : Int)
    (fk_flag : T1 → Int → Int → Int)
    (L : T1)
    (fk_frame : T1 → Int → Int → Int)
    (fflag : T1 → Int → Int → Int)
    (shad : Int → Int)
    (al_fake : T1 → Int)
    (shlen : Int → Int)
    (c : Int)
    (pos' : Int)
    (a' : Int)
    (h1 : ((jn : Nat) : Int) = jz)
    (h2 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ pos ∧ pos < 16384))
    (h4 : flag = (fk_flag L 0 pos))
    (h5 : F = (fk_frame L 0 pos))
    (h6 : (fflag L 0 F) = flag)
    (h7 : (shad F) = (2147450880 + (F / 8)))
    (h8 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h9 : ((((shad (al_fake L)) + 4608) + (8 * pos)) = (shad F) ∧ (((shad F) + 8) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 8) ≤ 17594333495296)))
    (h10 : (((shad F) + 8) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h11 : pos = (Z_land (h_1 + ((jn : Nat) : Int)) 16383))
    (h12 : flag = (((al_fake L) + 4096) + pos))
    (h13 : F = (((al_fake L) + 36864) + (pos * 64)))
    (h14 : ((jn : Nat) : Int) < 16384)
    (h15 : (F % 64) = 0)
    (h16 : (fk_flag L c pos') ≠ flag)
    (h17 : (shad a') = (2147450880 + (a' / 8))) :
    (F + 24) = ((F + ((8 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/AsanW/AFake_arep.v (replace)
example
    {T1 : Type}
    (shad : Int → Int)
    (F : Int)
    (jn : Nat)
    (jz : Int)
    (h_1 : Int)
    (pos : Int)
    (L : T1)
    (fk_frame : T1 → Int → Int → Int)
    (al_fake : T1 → Int)
    (shlen : Int → Int)
    (h1 : ((jn : Nat) : Int) = jz)
    (h2 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ pos ∧ pos < 4096))
    (h4 : F = (fk_frame L 2 pos))
    (h5 : (shad F) = (2147450880 + (F / 8)))
    (h6 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h7 : ((((shad (al_fake L)) + 266752) + (32 * pos)) = (shad F) ∧ (((shad F) + 32) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 32) ≤ 17594333495296)))
    (h8 : (((shad F) + 32) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F))) :
    ((shad F) + 16) = ((shad F) + ((16 : Nat) : Int)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/AsanW/AFake_arep.v (replace)
example
    {T1 : Type}
    (F : Int)
    (jn : Nat)
    (jz : Int)
    (Z_land : Int → Int → Int)
    (h_1 : Int)
    (pos : Int)
    (flag : Int)
    (fk_flag : T1 → Int → Int → Int)
    (L : T1)
    (fk_frame : T1 → Int → Int → Int)
    (fflag : T1 → Int → Int → Int)
    (shad : Int → Int)
    (al_fake : T1 → Int)
    (shlen : Int → Int)
    (a' : Int)
    (h1 : ((jn : Nat) : Int) = jz)
    (h2 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ pos ∧ pos < 4096))
    (h4 : flag = (fk_flag L 2 pos))
    (h5 : F = (fk_frame L 2 pos))
    (h6 : (fflag L 2 F) = flag)
    (h7 : (shad F) = (2147450880 + (F / 8)))
    (h8 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h9 : ((((shad (al_fake L)) + 266752) + (32 * pos)) = (shad F) ∧ (((shad F) + 32) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 32) ≤ 17594333495296)))
    (h10 : (((shad F) + 32) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h11 : pos = (Z_land (h_1 + ((jn : Nat) : Int)) 4095))
    (h12 : flag = (((al_fake L) + 28672) + pos))
    (h13 : F = (((al_fake L) + 2134016) + (pos * 256)))
    (h14 : ((jn : Nat) : Int) < 4096)
    (h15 : (2147450880 ≤ (shad ((al_fake L) + 36864)) ∧ ((shad ((al_fake L) + 11571200)) ≤ 17594333495296 ∧ ((shad ((al_fake L) + 11571200)) = ((shad (al_fake L)) + 1446400) ∧ (shad (al_fake L)) ≤ (shad ((al_fake L) + 36864))))))
    (h16 : (F % 256) = 0)
    (h17 : (shlen 11571200) = 1446400)
    (h18 : 2147450880 ≤ (shad F))
    (h19 : (shad a') = (2147450880 + (a' / 8)))
    (h20 : (F % 8) = 0) :
    (F + 8) = (F + ((8 : Nat) : Int)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/AsanW/AFake_arep.v (replace)
example
    {T1 : Type}
    (F : Int)
    (jn : Nat)
    (jz : Int)
    (Z_land : Int → Int → Int)
    (h_1 : Int)
    (pos : Int)
    (flag : Int)
    (fk_flag : T1 → Int → Int → Int)
    (L : T1)
    (fk_frame : T1 → Int → Int → Int)
    (fflag : T1 → Int → Int → Int)
    (shad : Int → Int)
    (al_fake : T1 → Int)
    (shlen : Int → Int)
    (a' : Int)
    (h1 : ((jn : Nat) : Int) = jz)
    (h2 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ pos ∧ pos < 4096))
    (h4 : flag = (fk_flag L 2 pos))
    (h5 : F = (fk_frame L 2 pos))
    (h6 : (fflag L 2 F) = flag)
    (h7 : (shad F) = (2147450880 + (F / 8)))
    (h8 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h9 : ((((shad (al_fake L)) + 266752) + (32 * pos)) = (shad F) ∧ (((shad F) + 32) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 32) ≤ 17594333495296)))
    (h10 : (((shad F) + 32) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h11 : pos = (Z_land (h_1 + ((jn : Nat) : Int)) 4095))
    (h12 : flag = (((al_fake L) + 28672) + pos))
    (h13 : F = (((al_fake L) + 2134016) + (pos * 256)))
    (h14 : ((jn : Nat) : Int) < 4096)
    (h15 : (2147450880 ≤ (shad ((al_fake L) + 36864)) ∧ ((shad ((al_fake L) + 11571200)) ≤ 17594333495296 ∧ ((shad ((al_fake L) + 11571200)) = ((shad (al_fake L)) + 1446400) ∧ (shad (al_fake L)) ≤ (shad ((al_fake L) + 36864))))))
    (h16 : (F % 256) = 0)
    (h17 : (shlen 11571200) = 1446400)
    (h18 : 2147450880 ≤ (shad F))
    (h19 : (shad a') = (2147450880 + (a' / 8)))
    (h20 : (F % 8) = 0) :
    (F + 24) = ((F + ((8 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/AsanW/ARealloc_x.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (Z_to_bv : Int → Int → T1)
    (n : Int)
    (nold : Int)
    (k : Nat)
    (length : T2 → Nat)
    (src : T2)
    (junk : T2)
    (h1 : (bv_unsigned sp) < (2 ^ (47 : Nat)))
    (h2 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-2208)))) = ((bv_unsigned sp) + (-2208)))
    (h3 : k ≤ (Int.toNat nold))
    (h4 : (length src) = k)
    (h5 : k ≤ (Int.toNat n))
    (h6 : (length junk) = (Int.toNat n))
    (h7 : ((k : Nat) : Int) = (min n nold)) :
    ((bv_unsigned sp) + (-2120)) = (((bv_unsigned sp) + (-2136)) + 16) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/AsanW/F_aalloc1.v (replace)
example
    (n : Int)
    (is_primary16 : Int → Bool)
    (rounded_size16 : Int → Int)
    (h1 : 1 ≤ n)
    (h2 : (is_primary16 n) = true)
    (h3 : (((max n 8) ≤ (rounded_size16 n) ∧ (rounded_size16 n) ≤ ((max n 8) + 15)) ∧ (((rounded_size16 n) % 16) = 0 ∧ (rounded_size16 n) = (((max n 8) + 15) - (((max n 8) + 15) % 16))))) :
    ((max n 8) + 15) = (((max n 8) + 16) - 1) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/AsanW/I_asan_memcpy0.v (assert)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (bv_unsigned : word → Int)
    (KHIGH : Int)
    (h1 : lo ≤ ((bv_unsigned sp) - 2240))
    (h2 : KHIGH ≤ lo) :
    lo ≤ ((bv_unsigned sp) - 2160) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Br/HeapCtr.v (replace)
example
    {T1 : Type}
    (a : T1)
    (b : T1)
    (w2Z : T1 → Int)
    (two63 : Int)
    (w2Zs : T1 → Int)
    (h1 : ((-two63) ≤ ((w2Zs a) - (w2Zs b)) ∧ ((w2Zs a) - (w2Zs b)) < two63)) :
    ((((w2Z a) - (w2Z b)) + 18446744073709551616) + ((-1) * 18446744073709551616)) = ((w2Z a) - (w2Z b)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Bridge/CallA.v (replace)
example
    {T1 T2 T3 : Type}
    (E : T1)
    (n : T2)
    (bv_unsigned : T3 → Int)
    (den : T1 → T2 → T3)
    (h1 : 1 ≤ (bv_unsigned (den E n))) :
    (((bv_unsigned (den E n)) - 1) + (1 * (2 ^ (64 : Nat)))) = ((bv_unsigned (den E n)) + ((2 ^ (64 : Nat)) - 1)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Bridge/CtrAnnot.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (E : T1)
    (k : T2)
    (to_Z : T3 → Int)
    (wl : T4 → T3)
    (o : T4)
    (bv_unsigned : T5 → Int)
    (ev : T1 → T2 → T5)
    (den : T1 → T6 → T5)
    (VP : T2 → T4 → T6)
    (h1 : ((bv_unsigned (ev E k)) % 8) = 0)
    (h2 : (bv_unsigned (ev E k)) < (2 ^ (62 : Nat)))
    (h3 : (bv_unsigned (den E (VP k o))) = ((bv_unsigned (ev E k)) + (to_Z (wl o)))) :
    (to_Z (wl o)) = (((bv_unsigned (ev E k)) + (to_Z (wl o))) - (bv_unsigned (ev E k))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Bridge/CtrNull.v (replace)
example
    {T1 : Type}
    (AERRNO : Int)
    (a : Int)
    (AIMG_HI : Int)
    (x : Int)
    (shad : Int → Int)
    (A : Int)
    (i : Int)
    (st : T1)
    (fresh_ok : T1 → Bool)
    (h1 : (0 ≤ AERRNO ∧ ((AERRNO + 4) ≤ AIMG_HI ∧ AIMG_HI < (2 ^ (47 : Nat)))))
    (h2 : (0 ≤ a ∧ a < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ x ∧ x < (2 ^ (64 : Nat))))
    (h4 : (AIMG_HI ≤ ((shad A) + i) ∧ ((shad A) + i) < (2 ^ (64 : Nat))))
    (h5 : (0 ≤ (A / 8) ∧ (A / 8) ≤ A))
    (h6 : (fresh_ok st) = true) :
    (AERRNO + (a - AERRNO)) = a := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Bridge/CtrPost.v (replace)
example
    {env sstate int region list_____int_sv_w64 T6 T7 T8 T9 : Type}
    (E : env)
    (st : sstate)
    (N_1 : Int)
    (ks : int)
    (rss : region)
    (ksp : int)
    (wnl : list_____int_sv_w64)
    (to_Z : T6 → Int)
    (s_next : sstate → T6)
    (fresh_ok : sstate → Bool)
    (sp : Int)
    (bv_unsigned : T7 → Int)
    (ev : env → int → T7)
    (keyZ : int → Int)
    (aregions_justified : sstate → list_____int_sv_w64 → Bool)
    (ATOP : Int)
    (den : env → T8 → T7)
    (loZ : region → Int)
    (nsv : T8)
    (hiZ : T9 → region → Int)
    (E' : T9)
    (blk_region : region)
    (h1 : (fresh_ok st) = true)
    (h2 : sp = ((bv_unsigned (ev E ks)) + (keyZ ksp)))
    (h3 : (aregions_justified st wnl) = true)
    (h4 : (ATOP + 4096) ≤ ((bv_unsigned (ev E ks)) + (loZ rss)))
    (h5 : (loZ rss) ≤ (keyZ ksp))
    (h6 : ((keyZ ksp) % 16) = 0)
    (h7 : (bv_unsigned (den E nsv)) = N_1)
    (h8 : (hiZ E' blk_region) = N_1)
    (h9 : (loZ blk_region) = 0) :
    15 = (((to_Z (s_next st)) + 15) - (to_Z (s_next st))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/EH/Pool.v (replace)
example {T1 T2 : Type} (to_Z : T1 → Int) (FL : T1) (pe_addr : T2 → T1) (e : T2) (i : Int) :
    ((to_Z FL) + (((to_Z (pe_addr e)) + i) - (to_Z FL))) = ((to_Z (pe_addr e)) + i) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/FX/MemProofs.v (replace)
example
    {T1 T2 T3 : Type}
    (keyZ : T1 → Int)
    (g1 : T1)
    (j : Int)
    (to_Z : T2 → Int)
    (c_idx : T3 → T2)
    (c : T3)
    (A : Int)
    (w : T2)
    (two64 : Int)
    (h1 : (0 ≤ A ∧ (A + (to_Z w)) ≤ two64)) :
    ((8 * (keyZ g1)) + j) = (((8 * (keyZ g1)) + (to_Z (c_idx c))) + (j - (to_Z (c_idx c)))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/FX/MemProofs.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (bv_unsigned : T1 → Int)
    (ev : T2 → T3 → T1)
    (E : T2)
    (k : T3)
    (keyZ : T4 → Int)
    (g1 : T4)
    (to_Z : T5 → Int)
    (c_idx : T6 → T5)
    (c : T6)
    (t : Int)
    (A : Int)
    (w : T5)
    (two64 : Int)
    (h1 : (0 ≤ A ∧ (A + (to_Z w)) ≤ two64)) :
    (((bv_unsigned (ev E k)) + (8 * (keyZ g1))) + ((to_Z (c_idx c)) + t)) = ((((bv_unsigned (ev E k)) + (8 * (keyZ g1))) + (to_Z (c_idx c))) + t) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/FX/ValProofs.v (replace)
example
    {list_fact T2 T3 T4 T5 T6 T7 T8 T9 : Type}
    (fs : list_fact)
    (G : T2)
    (U : T3 → Int)
    (v1 : T3)
    (two64 : Int)
    (w2Z : T4 → Int)
    (c : T4)
    (add_carries : T5 → T5 → Bool)
    (snd : T6 → T5)
    (sv_bounds : list_fact → T3 → T6)
    (v2 : T3)
    (l_eval : T7 → Int)
    (l_comb : T8 → Int → T8 → T7)
    (linz : T2 → list_fact → T3 → T8)
    (VAlu : T9 → T3 → T3 → T3)
    (ALU_ADD : T9)
    (wneg : T4 → T4)
    (h1 : ((add_carries (snd (sv_bounds fs v1)) (snd (sv_bounds fs v2))) = false → (l_eval (l_comb (linz G fs v1) 1 (linz G fs v2))) = (U (VAlu ALU_ADD v1 v2))))
    (h2 : (w2Z (wneg c)) = (two64 - (w2Z c)))
    (h3 : (two64 - (w2Z c)) ≤ (U v1)) :
    (((U v1) - (two64 - (w2Z c))) + (1 * two64)) = ((U v1) + (w2Z c)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/GlueA/InitAsan2.v (replace)
example
    {word list_list_byte EntryDraw T4 : Type}
    (sp : word)
    (argv : list_list_byte)
    (envp : list_list_byte)
    (uid : word)
    (hwcap : word)
    (draw : EntryDraw)
    (a : Int)
    (usp : Int)
    (length : list_list_byte → Nat)
    (V : Nat → Int)
    (argc : Int)
    (envc : Int)
    (build_stack_bytes : T4 → word → list_list_byte → list_list_byte → word → word → EntryDraw → list_list_byte)
    (PH : T4)
    (bv_unsigned : word → Int)
    (h1 : (length argv) = 2)
    (h2 : (((32768 * (V 0)) + (4096 * (V 10))) + (16 * (V 6))) = usp)
    (h3 : (V 1) = argc)
    (h4 : (V 2) = envc)
    (h5 : (V 4) = ((((((length (build_stack_bytes PH sp argv envp uid hwcap draw)) : Nat) : Int) - 16) - (((8 * (((length argv) : Nat) : Int)) + (8 * (((length envp) : Nat) : Int))) + 184)) / 8))
    (h6 : (V 8) = (bv_unsigned uid))
    (h7 : (V 9) = (bv_unsigned hwcap))
    (h8 : (1 ≤ (V 44) ∧ (V 44) ≤ 4194303))
    (h9 : ((usp + (-8384512)) ≤ a ∧ a < (usp + 24))) :
    a = (usp + (a - usp)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/GlueA/InitBothN.v (replace)
example
    {word list_list_byte EntryDraw T4 : Type}
    (sp : word)
    (argv : list_list_byte)
    (envp : list_list_byte)
    (uid : word)
    (hwcap : word)
    (draw : EntryDraw)
    (a : Int)
    (usp : Int)
    (argc : Int)
    (envc : Int)
    (length : list_list_byte → Nat)
    (V : Nat → Int)
    (build_stack_bytes : T4 → word → list_list_byte → list_list_byte → word → word → EntryDraw → list_list_byte)
    (PH : T4)
    (bv_unsigned : word → Int)
    (h1 : (length argv) ≠ 2)
    (h2 : (((32768 * (V 0)) + (4096 * (V 10))) + (16 * (V 6))) = usp)
    (h3 : (V 1) = argc)
    (h4 : (V 2) = envc)
    (h5 : (V 4) = ((((((length (build_stack_bytes PH sp argv envp uid hwcap draw)) : Nat) : Int) - 16) - (((8 * (((length argv) : Nat) : Int)) + (8 * (((length envp) : Nat) : Int))) + 184)) / 8))
    (h6 : (V 8) = (bv_unsigned uid))
    (h7 : (V 9) = (bv_unsigned hwcap))
    (h8 : (1 ≤ (V 44) ∧ (V 44) ≤ 4194303)) :
    a = ((((usp + (8 * argc)) + (8 * envc)) + 24) + (a - (((usp + (8 * argc)) + (8 * envc)) + 24))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/GlueA/InitBothN.v (replace)
example
    {word list_list_byte EntryDraw T4 : Type}
    (sp : word)
    (argv : list_list_byte)
    (envp : list_list_byte)
    (uid : word)
    (hwcap : word)
    (draw : EntryDraw)
    (a : Int)
    (ZSHF_LO : Int)
    (length : list_list_byte → Nat)
    (V : Nat → Int)
    (usp : Int)
    (argc : Int)
    (envc : Int)
    (build_stack_bytes : T4 → word → list_list_byte → list_list_byte → word → word → EntryDraw → list_list_byte)
    (PH : T4)
    (bv_unsigned : word → Int)
    (ZSH_LO : Int)
    (ZSH_HI : Int)
    (h1 : (length argv) ≠ 2)
    (h2 : (((32768 * (V 0)) + (4096 * (V 10))) + (16 * (V 6))) = usp)
    (h3 : (V 1) = argc)
    (h4 : (V 2) = envc)
    (h5 : (V 4) = ((((((length (build_stack_bytes PH sp argv envp uid hwcap draw)) : Nat) : Int) - 16) - (((8 * (((length argv) : Nat) : Int)) + (8 * (((length envp) : Nat) : Int))) + 184)) / 8))
    (h6 : (V 8) = (bv_unsigned uid))
    (h7 : (V 9) = (bv_unsigned hwcap))
    (h8 : (1 ≤ (V 44) ∧ (V 44) ≤ 4194303))
    (h9 : (ZSH_LO ≤ a ∧ a < ZSH_HI)) :
    a = (ZSHF_LO + (a - ZSHF_LO)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/GlueA/InitBothN.v (assert)
example
    {word list_list_byte EntryDraw T4 : Type}
    (sp : word)
    (argv : list_list_byte)
    (envp : list_list_byte)
    (uid : word)
    (hwcap : word)
    (draw : EntryDraw)
    (SI_total_nat : list_list_byte → Nat)
    (SI_pad : list_list_byte → list_list_byte → Nat)
    (length : list_list_byte → Nat)
    (V : Nat → Int)
    (usp : Int)
    (argc : Int)
    (envc : Int)
    (build_stack_bytes : T4 → word → list_list_byte → list_list_byte → word → word → EntryDraw → list_list_byte)
    (PH : T4)
    (bv_unsigned : word → Int)
    (h1 : (length argv) ≠ 2)
    (h2 : (((32768 * (V 0)) + (4096 * (V 10))) + (16 * (V 6))) = usp)
    (h3 : (V 1) = argc)
    (h4 : (V 2) = envc)
    (h5 : (V 4) = ((((((length (build_stack_bytes PH sp argv envp uid hwcap draw)) : Nat) : Int) - 16) - (((8 * (((length argv) : Nat) : Int)) + (8 * (((length envp) : Nat) : Int))) + 184)) / 8))
    (h6 : (V 8) = (bv_unsigned uid))
    (h7 : (V 9) = (bv_unsigned hwcap))
    (h8 : (1 ≤ (V 44) ∧ (V 44) ≤ 4194303)) :
    (0 ≤ (((SI_total_nat argv) : Nat) : Int) ∧ (0 ≤ (((SI_total_nat envp) : Nat) : Int) ∧ 0 ≤ (((SI_pad argv envp) : Nat) : Int))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/GlueA/MemsetPost.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (A0 : Int)
    (bv_unsigned : T1 → Int)
    (x : T1)
    (to_Z : T2 → Int)
    (st : T3)
    (sv_vars_below : T4 → T5 → Bool)
    (s_next : T3 → T4)
    (VP : T6 → T7 → T5)
    (kd : T6)
    (od : T7)
    (den : T8 → T5 → T1)
    (E' : T8)
    (b : T2)
    (h1 : (sv_vars_below (s_next st) (VP kd od)) = true)
    (h2 : (bv_unsigned (den E' (VP kd od))) = A0)
    (h3 : (0 ≤ (to_Z b) ∧ (to_Z b) < 256)) :
    (A0 + ((bv_unsigned x) - A0)) = (bv_unsigned x) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/GlueA/ReadPost.v (replace)
example
    {T1 T2 : Type}
    (a : Int)
    (STAGE : Int)
    (ATOP : Int)
    (CtrPre_sp_lo : T1 → T2 → Int)
    (E : T1)
    (st : T2)
    (sp : Int)
    (shad : Int → Int)
    (ASHOFF : Int)
    (h1 : ((ATOP + 4096) ≤ (CtrPre_sp_lo E st) ∧ ((CtrPre_sp_lo E st) ≤ (sp - 4096) ∧ sp < (2 ^ (47 : Nat)))))
    (h2 : (shad ATOP) = (ASHOFF + (ATOP / 8)))
    (h3 : (STAGE ≤ a ∧ a < (STAGE + 65536))) :
    a = (STAGE + (a - STAGE)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/GlueA/SmPost.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (F : Int)
    (a : Int)
    (AIMG_HI : Int)
    (n : Int)
    (KLS : Int)
    (ATOP : Int)
    (to_Z : T1 → Int)
    (kf : T1)
    (s_next : T2 → T1)
    (st : T2)
    (shf : T1)
    (bv_unsigned : T3 → Int)
    (ev : T4 → T1 → T3)
    (E' : T4)
    (shad : Int → Int)
    (wb : T5 → T6 → Int → Bool)
    (asegs : T5)
    (m' : T6)
    (h1 : ((AIMG_HI ≤ F ∧ (F + n) ≤ KLS) ∨ (17594333495296 ≤ F ∧ (F + n) ≤ ATOP)))
    (h2 : (to_Z kf) = ((to_Z (s_next st)) + 15))
    (h3 : (to_Z shf) = ((to_Z (s_next st)) + 16))
    (h4 : (6483968 ≤ F ∧ (F + n) < (2 ^ (47 : Nat))))
    (h5 : (bv_unsigned (ev E' kf)) = F)
    (h6 : (bv_unsigned (ev E' shf)) = (shad F))
    (h7 : (wb asegs m' a) = true) :
    (F + (a - F)) = a := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Ref/RF_aligned16_W.v (replace)
example
    {T1 : Type}
    (G : Int)
    (stride : Int)
    (i : Int)
    (avail : Int)
    (freed : Int)
    (last_idx : Int)
    (freeable : Int)
    (sc : Int)
    (maplen : Int)
    (size_class : Int → Int)
    (mword : Int)
    (b3 : Int)
    (Z_land : Int → Int → Int)
    (Z_to_bv : Int → Int → T1)
    (bv_unsigned : T1 → Int)
    (gw : T1)
    (Zpow : Int → Int → Int)
    (Z_shiftr : Int → Int → Int)
    (Z_shiftl : Int → Int → Int)
    (h1 : ((maplen = 0 ∨ last_idx ≠ 0) → (sc < 48 ∧ stride = (16 * (size_class sc)))))
    (h2 : ((last_idx = 0 ∧ maplen ≠ 0) → stride = ((maplen * 4096) - 16)))
    (h3 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h4 : (0 ≤ b3 ∧ b3 < 256))
    (h5 : (Z_land b3 31) = i)
    (h6 : (bv_unsigned gw) = G)
    (h7 : (Z_land mword 31) = last_idx)
    (h8 : (0 ≤ (Zpow 2 i) ∧ (Zpow 2 i) < (2 ^ (32 : Nat))))
    (h9 : (Z_land avail (Zpow 2 i)) = 0)
    (h10 : (Z_land freed (Zpow 2 i)) = 0)
    (h11 : (Z_shiftr (bv_unsigned (Z_to_bv 64 (Z_shiftl mword 52))) 58) = sc) :
    (((last_idx + (32 * freeable)) * (2 ^ (52 : Nat))) + (sc * (2 ^ (58 : Nat)))) = (((last_idx + (32 * freeable)) + (64 * sc)) * (2 ^ (52 : Nat))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Ref/RF_realloc_hdr.v (replace)
example
    {T1 : Type}
    (G : Int)
    (i : Int)
    (avail : Int)
    (freed : Int)
    (last_idx : Int)
    (freeable : Int)
    (sc : Int)
    (maplen : Int)
    (mword : Int)
    (b3 : Int)
    (Z_land : Int → Int → Int)
    (Z_to_bv : Int → Int → T1)
    (bv_unsigned : T1 → Int)
    (gw : T1)
    (Zpow : Int → Int → Int)
    (Z_shiftr : Int → Int → Int)
    (Z_shiftl : Int → Int → Int)
    (h1 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ b3 ∧ b3 < 256))
    (h3 : (Z_land b3 31) = i)
    (h4 : (bv_unsigned gw) = G)
    (h5 : (Z_land mword 31) = last_idx)
    (h6 : (0 ≤ (Zpow 2 i) ∧ (Zpow 2 i) < (2 ^ (32 : Nat))))
    (h7 : (Z_land avail (Zpow 2 i)) = 0)
    (h8 : (Z_land freed (Zpow 2 i)) = 0)
    (h9 : (Z_shiftr (bv_unsigned (Z_to_bv 64 (Z_shiftl mword 52))) 58) = sc) :
    ((((last_idx + (32 * freeable)) + (64 * sc)) * (2 ^ (52 : Nat))) + (maplen * (2 ^ (64 : Nat)))) = ((((last_idx + (32 * freeable)) + (64 * sc)) + (4096 * maplen)) * (2 ^ (52 : Nat))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Ref/RF_realloc_moveS.v (replace)
example
    {word bptr list_byte T4 : Type}
    (tp : word)
    (p : bptr)
    (A : Int)
    (old : Int)
    (n : Int)
    (oldbs : list_byte)
    (A' : Int)
    (k : Int)
    (i : Int)
    (bv_unsigned : word → Int)
    (Z_to_bv : Int → Int → word)
    (sp1 : Int)
    (p' : bptr)
    (length : T4 → Nat)
    (firstn : Nat → list_byte → T4)
    (bptr_eqb : bptr → bptr → Bool)
    (h1 : ((bv_unsigned tp) + (-164)) = 422892)
    (h2 : (bv_unsigned (Z_to_bv 64 sp1)) = sp1)
    (h3 : old < (2 ^ (48 : Nat)))
    (h4 : ((0 ≤ k ∧ k ≤ n) ∧ k ≤ old))
    (h5 : (length (firstn (Int.toNat k) oldbs)) = (Int.toNat k))
    (h6 : (bv_unsigned (Z_to_bv 64 A)) = A)
    (h7 : (bv_unsigned (Z_to_bv 64 A')) = A')
    (h8 : (bv_unsigned (Z_to_bv 64 k)) = k)
    (h9 : (bptr_eqb p' p) = false) :
    ((A' + k) + (i - k)) = (A' + i) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Ref/RF_realloc_rrep.v (replace)
example
    {mstate aptr T3 T4 T5 : Type}
    (st : mstate)
    (g : aptr)
    (nb : Int)
    (needed : Int)
    (o : Int)
    (i : Int)
    (get_meta_rec : mstate → aptr → T3)
    (m_maplen : T3 → Int)
    (OL : Int)
    (m_last_idx : T3 → Int)
    (m_freeable : T3 → Int)
    (m_sizeclass : T3 → Int)
    (alloc_ceiling : Int)
    (ranges_free : T4 → Int → Int → Bool)
    (ref_reserved : T4)
    (kt : Int)
    (actives : mstate → T5)
    (usages : mstate → T5)
    (unmap_seqs : mstate → T5)
    (bouncess : mstate → T5)
    (length : T5 → Nat)
    (conc : mstate → aptr → Int)
    (ag : aptr)
    (AREA_HDR : Int)
    (META_SIZE : Int)
    (kg : Int)
    (k : Int)
    (h1 : ((m_maplen (get_meta_rec st g)) * 4096) = OL)
    (h2 : ((0 ≤ (m_last_idx (get_meta_rec st g)) ∧ (m_last_idx (get_meta_rec st g)) < 32) ∧ ((0 ≤ (m_freeable (get_meta_rec st g)) ∧ (m_freeable (get_meta_rec st g)) < 2) ∧ (0 ≤ (m_sizeclass (get_meta_rec st g)) ∧ (m_sizeclass (get_meta_rec st g)) < 64))))
    (h3 : 0 < nb)
    (h4 : (nb % 4096) = 0)
    (h5 : (needed % 4096) = 0)
    (h6 : 0 < needed)
    (h7 : (nb + needed) ≤ alloc_ceiling)
    (h8 : (ranges_free ref_reserved nb needed) = true)
    (h9 : 16 ≤ OL)
    (h10 : 16 ≤ kt)
    (h11 : (length (actives st)) = 48)
    (h12 : (length (usages st)) = 48)
    (h13 : (length (unmap_seqs st)) = 32)
    (h14 : (length (bouncess st)) = 32)
    (h15 : (conc st g) = ((conc st ag) + (AREA_HDR + (META_SIZE * kg))))
    (h16 : (((conc st ag) + 24) + (40 * kg)) = (conc st g))
    (h17 : ((conc st ag) ≤ (conc st g) ∧ ((conc st g) + 40) ≤ ((conc st ag) + 4096)))
    (h18 : k ≠ kg) :
    (nb + (o + i)) = ((nb + o) + i) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Unp/G3.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (lv_P : T1 → Int)
    (l' : T1)
    (lv_k : T1 → Int)
    (n : T2)
    (E' : T3)
    (PrimInt63_ltb : T2 → T2 → Bool)
    (kS : T2)
    (ev : T3 → T2 → T4)
    (g : T5)
    (u_cur_slot : T5 → Int)
    (l : T1)
    (lv_slot : T1 → Int)
    (bv_unsigned : T4 → Int)
    (w2Z : T6 → Int)
    (lv_bytes : T1 → Int)
    (hiZ : T3 → T7 → Int)
    (empty_slot_region : T7)
    (loZ : T7 → Int)
    (GPot_GPot_D_RETw : T6)
    (h1 : (PrimInt63_ltb kS n) = true)
    (h2 : (u_cur_slot g) = (lv_slot l))
    (h3 : (bv_unsigned (ev E' kS)) = (lv_slot l))
    (h4 : ((lv_P l) ≤ (lv_slot l') ∧ ((lv_slot l') + 24) ≤ ((lv_P l) + (lv_bytes l))))
    (h5 : (bv_unsigned (ev E' n)) = (lv_slot l'))
    (h6 : (hiZ E' empty_slot_region) = 24)
    (h7 : (loZ empty_slot_region) = 0)
    (h8 : (0 ≤ (w2Z GPot_GPot_D_RETw) ∧ (w2Z GPot_GPot_D_RETw) ≤ (2 ^ (20 : Nat)))) :
    ((lv_P l') + ((3 * (lv_k l')) * 8)) = ((lv_P l') + (24 * (lv_k l'))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Unp/G4A.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 : Type}
    (to_Z : T1 → Int)
    (find_align : T2 → T3 → T1)
    (s_facts : T4 → T2)
    (st : T4)
    (kC : T3)
    (PrimInt63_ltb : T3 → T3 → Bool)
    (kZP : T3)
    (n : T3)
    (rf_allb : T5 → T6 → Bool)
    (sv_vars_below : T3 → T5)
    (s_rf : T4 → T6)
    (E' : T7)
    (ev : T7 → T3 → T8)
    (den : T7 → T9 → T8)
    (R : T9)
    (SZ : T9)
    (h_1 : T9)
    (u_zone : T10 → T11)
    (g : T10)
    (bv_unsigned : T8 → Int)
    (z_ptr : T11 → Int)
    (zp : Int)
    (zf : Int)
    (two64 : Int)
    (zfree : T9)
    (hiZ : T7 → T12 → Int)
    (new_region : T9 → T12)
    (sz : Int)
    (loZ : T12 → Int)
    (chunk_hi : T9 → Int)
    (Zpow : Int → Int → Int)
    (w2Z : T13 → Int)
    (hi : T13)
    (two63 : Int)
    (align8 : Int → Int)
    (szw : T13)
    (hlen : T13)
    (c : Int)
    (h1 : (PrimInt63_ltb kZP n) = true)
    (h2 : (rf_allb (sv_vars_below n) (s_rf st)) = true)
    (h3 : (bv_unsigned (ev E' kZP)) = (z_ptr (u_zone g)))
    (h4 : (bv_unsigned (den E' zfree)) = zf)
    (h5 : (hiZ E' (new_region SZ)) = sz)
    (h6 : (loZ (new_region SZ)) = 0)
    (h7 : (chunk_hi h_1) = (zp + zf))
    (h8 : 8 ≤ zp)
    (h9 : (bv_unsigned (den E' R)) = zp)
    (h10 : sz ≤ zf)
    (h11 : (Int.fmod sz two64) = sz)
    (h12 : (bv_unsigned (ev E' n)) = zp)
    (h13 : 0 < (Zpow 2 ((to_Z (find_align (s_facts st) kZP)) - 3)))
    (h14 : (w2Z hi) < two63)
    (h15 : ((bv_unsigned (den E' R)) = (align8 zp) ∧ ((zp ≤ (align8 zp) ∧ (align8 zp) ≤ (zp + 7)) ∧ ((align8 zp) % 8) = 0)))
    (h16 : ((align8 zp) + sz) ≤ (zp + zf))
    (h17 : (Int.fmod (((align8 zp) - zp) + sz) two64) = (((align8 zp) - zp) + sz))
    (h18 : (bv_unsigned (ev E' n)) = (align8 zp))
    (h19 : (w2Z szw) < two63)
    (h20 : (w2Z szw) = (Int.fmod ((w2Z hlen) - 8) two64))
    (h21 : (w2Z hlen) = (8 + (w2Z szw)))
    (h22 : (bv_unsigned (ev E' n)) = (c + 8))
    (h23 : (c % 16) = 0) :
    (4 + ((to_Z (find_align (s_facts st) kC)) - 4)) = (to_Z (find_align (s_facts st) kC)) := by
  lia
