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

These goals are proved by Rocq's `lia` but not yet by Lean's `lia`. When `lia` learns to
prove one, `fail_if_success` fails and the example belongs in `lia_oss_verify_<n>.lean`.
-/

set_option linter.unusedVariables false

set_option warn.sorry false

/-! Nonlinear monomials: Rocq's `lia` normalizes products of atoms (commutativity, associativity,
distributivity) before solving, so `a * b` and `b * a` are the same monomial. -/

-- openssl/ct: lib/CtTimeP/TimeMagic.v (replace)
example
    (x : Int)
    (m : Int)
    (d : Int)
    (K : Int)
    (e : Int)
    (B : Int)
    (Zpow : Int → Int → Int)
    (h1 : 0 < d)
    (h2 : 0 < e)
    (h3 : 0 ≤ K)
    (h4 : (m * d) = ((Zpow 2 K) + e))
    (h5 : 0 ≤ B)
    (h6 : (B * e) ≤ (Zpow 2 K))
    (h7 : (0 ≤ x ∧ x ≤ B))
    (h8 : (x * e) ≤ (B * e)) :
    ((-x) * m) = (x * (-m)) := by
  fail_if_success lia
  sorry

-- jsoncons/fuzz_ubjson_parser_max: lib/SymExec2Sound.v (replace)
example
    {T1 T2 T3 : Type}
    (tden : T1 → T2 → Int)
    (E : T1)
    (ldiv_terms : Int → T3 → T2)
    (sh : Int)
    (Zpow : Int → Int → Int)
    (ts : T3)
    (c : Int)
    (h1 : 0 < (Zpow 2 sh)) :
    (((tden E (ldiv_terms (Zpow 2 sh) ts)) * (Zpow 2 sh)) + c) = (c + ((Zpow 2 sh) * (tden E (ldiv_terms (Zpow 2 sh) ts)))) := by
  fail_if_success lia
  sorry

-- bzip2/bzip2_compress_target: lib/K/AS/AxSymExec3Sound.v (replace)
example
    {word : Type}
    (sh : Int)
    (y : word)
    (A : Int)
    (Zpow : Int → Int → Int)
    (c : Int)
    (T : Int)
    (bv_unsigned : word → Int)
    (h1 : ((bv_unsigned y) % 64) = sh)
    (h2 : 0 < (Zpow 2 sh)) :
    ((A * (Zpow 2 sh)) + (c + T)) = (c + (((Zpow 2 sh) * A) + T)) := by
  fail_if_success lia
  sorry

-- yajl-ruby/json_fuzzer: lib/B/BF_fakestack_rep.v (replace)
example
    {T1 : Type}
    (fsbase : T1)
    (cid : Int)
    (pos : Int)
    (fs_frame_bytes : Int → Int)
    (fs_frames_base : T1 → Int → Int)
    (h1 : 0 ≤ cid)
    (h2 : 0 ≤ pos)
    (h3 : 0 < (fs_frame_bytes cid)) :
    (pos * (fs_frame_bytes cid)) = (((fs_frames_base fsbase cid) + ((fs_frame_bytes cid) * pos)) - (fs_frames_base fsbase cid)) := by
  fail_if_success lia
  sorry

-- zstd/fse_read_ncount: lib/Spec/AsanTotal.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (cv : Int)
    (size : Int)
    (q : Int)
    (cntP : T1 → T2 → Int)
    (c : T1)
    (all_chunks : T3 → T4 → T5 → T2)
    (pc : T3)
    (pb : T4)
    (st1 : T5)
    (nbatch : T1 → T6 → Int)
    (qbatches : T4 → T5 → T6)
    (c_num_freed : T7 → Int)
    (get_cls : T5 → T1 → T7)
    (K_FREEARR_MAP : Int)
    (K_FREEARR_MAX : Int)
    (c_mapped_user : T7 → Int)
    (c_allocated_user : T7 → Int)
    (K_FREEARR_OFF : Int)
    (h1 : 0 ≤ ((cntP c (all_chunks pc pb st1)) + (nbatch c (qbatches pb st1))))
    (h2 : ((4 * ((c_num_freed (get_cls st1 c)) + q)) + K_FREEARR_MAP) ≤ K_FREEARR_MAX)
    (h3 : (size * ((c_num_freed (get_cls st1 c)) + q)) ≤ (c_mapped_user (get_cls st1 c)))
    (h4 : (size * (c_num_freed (get_cls st1 c))) ≤ (c_allocated_user (get_cls st1 c)))
    (h5 : (32 * ((c_num_freed (get_cls st1 c)) + q)) ≤ K_FREEARR_OFF)
    (h6 : cv = (q * size))
    (h7 : (32 * ((c_num_freed (get_cls st1 c)) + q)) ≤ (c_mapped_user (get_cls st1 c))) :
    cv = (size * q) := by
  fail_if_success lia
  sorry

-- zstd/simple_decompress: lib/BothW/F_amalloc_arep.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (k : Int)
    (c : Int)
    (c_allocated_user : T1 → Int)
    (get_cls : T2 → Int → T1)
    (st : T2)
    (AB : Int)
    (aslot_addr : T3 → Int → Int → Int)
    (L : T3)
    (UB : Int)
    (rz_size : Int → Int)
    (n : Int)
    (grz : Int)
    (g : Int)
    (room : Int)
    (shad : Int → Int)
    (bv_unsigned : T4 → Int)
    (Z_to_bv : Int → T5 → T4)
    (acompact : Int → Int → T5)
    (h1 : 0 ≤ (k * (32 * c)))
    (h2 : (k + 1) ≤ (Int.fdiv (c_allocated_user (get_cls st c)) (32 * c)))
    (h3 : ((k + 1) * (32 * c)) ≤ ((Int.fdiv (c_allocated_user (get_cls st c)) (32 * c)) * (32 * c)))
    (h4 : AB = (aslot_addr L c k))
    (h5 : UB = (AB + (rz_size n)))
    (h6 : (grz = ((rz_size n) / 8) ∧ g = ((n - (n % 8)) / 8)))
    (h7 : 2 ≤ grz)
    (h8 : 0 ≤ g)
    (h9 : (0 ≤ room ∧ room ≤ 1))
    (h10 : (shad UB) = ((shad AB) + grz))
    (h11 : ((bv_unsigned (Z_to_bv 64 (acompact c k))) = ((k * 2) * c) ∧ ((k * 2) * c) < (2 ^ (32 : Nat)))) :
    ((k * 2) * c) = (k * (2 * c)) := by
  fail_if_success lia
  sorry

-- leptonica/edge_fuzzer: lib/K5/B9/Px_getpixel_c0.v (replace)
example
    {T1 : Type}
    (p_wpl : T1 → Int)
    (v : T1)
    (y : Int)
    (usp : Int)
    (lo : Int)
    (pval : Int)
    (pix : Int)
    (p_data : T1 → Int)
    (rsize : T1 → Int)
    (x : Int)
    (p_w : T1 → Int)
    (p_h : T1 → Int)
    (h1 : (0 ≤ usp ∧ usp < (2 ^ (64 : Nat))))
    (h2 : (pval + 4) ≤ lo)
    (h3 : ((pval + 4) ≤ pix ∨ (pix + 64) ≤ pval))
    (h4 : ((pval + 4) ≤ (p_data v) ∨ ((p_data v) + (rsize v)) ≤ pval))
    (h5 : (((0 ≤ x ∧ x < (p_w v)) ∧ (0 ≤ y ∧ y < (p_h v))) ∨ (¬ ((0 ≤ x ∧ x < (p_w v)) ∧ (0 ≤ y ∧ y < (p_h v))))))
    (h6 : ((x / 32) + 1) ≤ (p_wpl v))
    (h7 : (0 ≤ ((p_wpl v) * y) ∧ (((p_wpl v) * y) + (p_wpl v)) ≤ ((p_wpl v) * (p_h v)))) :
    ((p_wpl v) * y) = (y * (p_wpl v)) := by
  fail_if_success lia
  sorry

-- cjson/cjson_read_fuzzer: lib/A/RTW_unwind.v (replace)
example
    {T1 T2 : Type}
    (k : Int)
    (pos : Int)
    (fsz : Int → Int)
    (fs : Int)
    (FS_FRAMES_OFF : Int)
    (Z_shiftl : Int → T1 → Int)
    (FS_LOG : T1)
    (fcap : Int → Int)
    (flag_live : T2 → Int → Int → Bool)
    (st : T2)
    (h1 : (k = 1 ∨ k = 2))
    (h2 : (0 ≤ pos ∧ pos < (fcap k)))
    (h3 : (flag_live st k pos) = false) :
    (pos * (fsz k)) = ((((fs + FS_FRAMES_OFF) + ((Z_shiftl 1 FS_LOG) * k)) + ((fsz k) * pos)) - ((fs + FS_FRAMES_OFF) + ((Z_shiftl 1 FS_LOG) * k))) := by
  fail_if_success lia
  sorry

-- simdjson/fuzz_utf8: lib/Common/AxSymExec3Sound.v (replace)
example (v : Int) (q : Int) (P : Int) (h1 : 0 ≤ v) (h2 : 0 < P) :
    ((q * P) + (P - 1)) = ((((P * q) + 0) + P) - 1) := by
  fail_if_success lia
  sorry

-- openssl/echconfiglist_parser: lib/Ub/RASlot_M4.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (cnt1 : Int)
    (hceil : Int)
    (bv_unsigned : word → Int)
    (RAS_STACK : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : hceil ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (RAS_STACK sc))) :
    ((UNIT * (size_class sc)) * cnt1) = (((size_class sc) * UNIT) * cnt1) := by
  fail_if_success lia
  sorry

-- openssl/echconfiglist_parser: lib/Ub/RASlot_M4.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (hceil : Int)
    (bv_unsigned : word → Int)
    (RAS_STACK : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : hceil ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (RAS_STACK sc))) :
    (UNIT * (size_class sc)) = ((size_class sc) * UNIT) := by
  fail_if_success lia
  sorry

-- openssl/bndiv: lib/BnAsan/W_bin2bnA.v (replace)
example
    {T1 : Type}
    (x : Int)
    (W : Int)
    (l : Int)
    (length : T1 → Nat)
    (fl : T1)
    (rfl : T1)
    (j : Nat)
    (Zpow : Int → Int → Int)
    (h1 : ((length fl) : Nat) = ((length rfl) + 1))
    (h2 : ((1 : Int) ≤ (Zpow 2 (8 * ((j : Nat) : Int))) ∧ ((Zpow 2 (8 * ((j : Nat) : Int))) : Int) ≤ (2 ^ (56 : Nat))))
    (h3 : ((Zpow 2 (8 * (((j + 1) : Nat) : Int))) : Int) = (256 * (Zpow 2 (8 * ((j : Nat) : Int))))) :
    (((x * W) + l) : Int) = (l + (W * (x + (256 * 0)))) := by
  fail_if_success lia
  sorry

-- leptonica/colorfill_fuzzer: lib/K5/AS/AsanAcct.v (replace)
example
    (r : Int)
    (q : Int)
    (page_size : Int)
    (z : Int)
    (h1 : 0 ≤ z)
    (h2 : 0 < page_size)
    (h3 : ((Int.fdiv z page_size) * page_size) = (((page_size * (2 ^ (52 : Nat))) * q) + ((Int.fdiv r page_size) * page_size))) :
    (r + (((2 ^ (52 : Nat)) * q) * page_size)) = (((page_size * (2 ^ (52 : Nat))) * q) + r) := by
  fail_if_success lia
  sorry

-- leptonica/colorfill_fuzzer: lib/K5/AS/AsanAcct.v (replace)
example
    (r : Int)
    (page_size : Int)
    (q : Int)
    (z : Int)
    (h1 : 0 ≤ z)
    (h2 : 0 < page_size)
    (h3 : ((Int.fdiv z page_size) * page_size) = (((page_size * (2 ^ (52 : Nat))) * q) + ((Int.fdiv r page_size) * page_size))) :
    (((Int.fdiv r page_size) * page_size) + (q * (page_size * (2 ^ (52 : Nat))))) = (((page_size * (2 ^ (52 : Nat))) * q) + ((Int.fdiv r page_size) * page_size)) := by
  fail_if_success lia
  sorry

-- varnish/esi_parse_fuzzer: lib/Zk/RASl4er.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (AS_STACK : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : alloc_ceiling ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (AS_STACK sc))) :
    (UNIT * (size_class sc)) = ((size_class sc) * UNIT) := by
  fail_if_success lia
  sorry

-- varnish/esi_parse_fuzzer: lib/Zk/RASl4er.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (cnt1 : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (AS_STACK : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : alloc_ceiling ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (AS_STACK sc))) :
    ((UNIT * (size_class sc)) * cnt1) = (((size_class sc) * UNIT) * cnt1) := by
  fail_if_success lia
  sorry

-- openssl/bndiv: lib/BnU/W_bin2bn.v (replace)
example
    {T1 : Type}
    (x : Int)
    (W : Int)
    (l : Int)
    (length : T1 → Nat)
    (fl : T1)
    (rfl : T1)
    (h1 : ((length fl) : Nat) = ((length rfl) + 1)) :
    (((x * W) + l) : Int) = (l + (W * (x + (256 * 0)))) := by
  fail_if_success lia
  sorry

-- openssl/pem: lib/MallocP/RF_realloc_spec.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 : Type}
    (off : Int)
    (UNIT : Int)
    (conc : T1 → T2 → Int)
    (st : T1)
    (c : T2)
    (c_init_done : T3 → Int)
    (ctx : T1 → T3)
    (sstart : T4 → Int → Int)
    (MR : T1 → T5 → T4)
    (g : T5)
    (i : Int)
    (snd : T6 → Int)
    (bg : T6)
    (stride : Int)
    (A : Int)
    (r_base : T7 → Int)
    (r : T7)
    (m_sizeclass : T8 → Int)
    (get_meta_rec : T1 → T5 → T8)
    (st' : T1)
    (round_up_pg : T9 → Int)
    (r_len : T7 → T9)
    (aadd : T2 → Int → T2)
    (h1 : (c_init_done (ctx st)) ≠ 0)
    (h2 : (sstart (MR st g) i) = (((snd bg) + 16) + (stride * i)))
    (h3 : A = ((r_base r) + ((((snd bg) + 16) + (stride * i)) + (16 * off))))
    (h4 : (0 ≤ A ∧ A < (2 ^ (64 : Nat))))
    (h5 : ((m_sizeclass (get_meta_rec st g)) < 48 → stride < (2 ^ (20 : Nat))))
    (h6 : (((r_base r) + (round_up_pg (r_len r))) ≤ 65536 ∨ 3198976 ≤ (r_base r)))
    (h7 : (conc st' (aadd c (UNIT * off))) = A) :
    (off * UNIT) = (((conc st c) + (UNIT * off)) - (conc st c)) := by
  fail_if_success lia
  sorry

-- fast_float/from_chars: lib/Common/FxFacts.v (assert)
example
    (k : Int)
    (Zpow : Int → Int → Int)
    (t2 : Int)
    (t : Int)
    (z : Int)
    (u : Int)
    (v : Int)
    (y : Int)
    (h1 : (2 ^ (64 : Nat)) = ((Zpow 2 k) * (Zpow 2 (64 - k))))
    (h2 : 0 < (Zpow 2 k))
    (h3 : 0 < (Zpow 2 (64 - k)))
    (h4 : (Int.fmod (z - ((Zpow 2 k) * u)) (2 ^ (64 : Nat))) = 0)
    (h5 : (Int.fmod (v - u) (2 ^ (64 : Nat))) = 0)
    (h6 : y = (u + ((Zpow 2 (64 - k)) * t)))
    (h7 : (v - y) = ((Zpow 2 (64 - k)) * (((Zpow 2 k) * t2) - t)))
    (h8 : (((Zpow 2 k) * t2) - t) = 0)
    (h9 : (Zpow 2 (64 - k)) ≤ (((v - y)).natAbs : Int)) :
    1 ≤ (((((Zpow 2 k) * t2) - t)).natAbs : Int) := by
  fail_if_success lia
  sorry

-- bzip2/bzip2_compress_target: lib/RS0/RASlot_W3.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 131056))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 131056)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- simdjson/fuzz_dump: lib/A/R_popfree.v (replace)
example
    (auser : Int)
    (k : Int)
    (ClassSize : Int → Int)
    (c : Int)
    (h1 : (k * (ClassSize c)) ≤ (2 ^ (22 : Nat)))
    (h2 : (ClassSize c) = (32 * c)) :
    (auser + (k * (ClassSize c))) = (auser + ((ClassSize c) * k)) := by
  fail_if_success lia
  sorry

-- simdjson/fuzz_dump: lib/A/R_popfree.v (replace)
example
    (auser : Int)
    (k : Int)
    (ClassSize : Int → Int)
    (c : Int)
    (Z_land : Int → Nat → Int)
    (h1 : (k * (ClassSize c)) ≤ (2 ^ (22 : Nat)))
    (h2 : (ClassSize c) = (32 * c))
    (h3 : (Z_land (ClassSize c) 18446744073709551615) = (ClassSize c)) :
    (auser + (k * (ClassSize c))) = (auser + ((ClassSize c) * k)) := by
  fail_if_success lia
  sorry

-- skcms/iccprofile_info: lib/AsLib/AsLibBswap.v (replace)
example
    (v : Int)
    (n : Int)
    (m : Int)
    (i : Int)
    (Zpow : Int → Int → Int)
    (h1 : (0 ≤ v ∧ v < (Zpow 2 n)))
    (h2 : (0 ≤ i ∧ i < n)) :
    (v + (m * (Zpow 2 n))) = (v + ((Zpow 2 n) * m)) := by
  fail_if_success lia
  sorry

-- msgpack-c/unpack_pack_fuzzer: lib/Ref/RASlot_M4.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (cnt1 : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (RAS_STACK : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : alloc_ceiling ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (RAS_STACK sc))) :
    ((UNIT * (size_class sc)) * cnt1) = (((size_class sc) * UNIT) * cnt1) := by
  fail_if_success lia
  sorry

-- msgpack-c/unpack_pack_fuzzer: lib/Ref/RASlot_M4.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (RAS_STACK : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : alloc_ceiling ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (RAS_STACK sc))) :
    (UNIT * (size_class sc)) = ((size_class sc) * UNIT) := by
  fail_if_success lia
  sorry

-- mbedtls/fuzz_pkcs7: lib/P/HP_calloc.v (replace)
example (cnt : Int) (sz : Int) :
    (cnt * sz) = (sz * cnt) := by
  fail_if_success lia
  sorry

-- openssl/bignum: lib/BgBnRB/W_bin2bnA.v (replace)
example
    {T1 : Type}
    (x : Int)
    (W : Int)
    (l : Int)
    (length : T1 → Nat)
    (fl : T1)
    (rfl : T1)
    (Q : Int)
    (j : Nat)
    (Zpow : Int → Int → Int)
    (t : Nat)
    (h1 : ((length fl) : Nat) = ((length rfl) + 1))
    (h2 : (0 : Int) ≤ Q)
    (h3 : ((1 : Int) ≤ (Zpow 2 (8 * ((j : Nat) : Int))) ∧ ((Zpow 2 (8 * ((j : Nat) : Int))) : Int) ≤ (2 ^ (56 : Nat))))
    (h4 : ((Zpow 2 (8 * (((j + 1) : Nat) : Int))) : Int) = (256 * (Zpow 2 (8 * ((j : Nat) : Int)))))
    (h5 : (t : Nat) = 0) :
    (((x * W) + l) : Int) = (l + (W * (x + (256 * 0)))) := by
  fail_if_success lia
  sorry

-- glaze/binary_reflection: lib/GxSymExec3Sound.v (replace)
example
    {T1 T2 word : Type}
    (E : T1)
    (a : T2)
    (sh : Int)
    (y : word)
    (A : Int)
    (Zpow : Int → Int → Int)
    (c : Int)
    (T : Int)
    (bv_unsigned : word → Int)
    (edenot : T1 → T2 → word)
    (q : Int)
    (L : Int)
    (lo : Int)
    (hi : Int)
    (h1 : ((bv_unsigned y) % 64) = sh)
    (h2 : 0 < (Zpow 2 sh))
    (h3 : ((q * (2 ^ (64 : Nat))) ≤ L ∧ L < ((q + 1) * (2 ^ (64 : Nat)))))
    (h4 : ((Int.fdiv lo (2 ^ (64 : Nat))) ≤ (Int.fdiv L (2 ^ (64 : Nat))) ∧ (Int.fdiv L (2 ^ (64 : Nat))) ≤ (Int.fdiv hi (2 ^ (64 : Nat)))))
    (h5 : (Int.fdiv L (2 ^ (64 : Nat))) = q)
    (h6 : (bv_unsigned (edenot E a)) = (L - (q * (2 ^ (64 : Nat))))) :
    ((A * (Zpow 2 sh)) + (c + T)) = (c + (((Zpow 2 sh) * A) + T)) := by
  fail_if_success lia
  sorry

-- glaze/binary_reflection: lib/GxSymExec3Sound.v (replace)
example
    {T1 T2 word T4 T5 : Type}
    (E : T1)
    (a : T2)
    (sh : Int)
    (y : word)
    (tden : T1 → T4 → Int)
    (ldiv_terms : Int → T5 → T4)
    (Zpow : Int → Int → Int)
    (ts : T5)
    (c : Int)
    (q : Int)
    (bv_unsigned : word → Int)
    (edenot : T1 → T2 → word)
    (L : Int)
    (lo : Int)
    (hi : Int)
    (h1 : ((bv_unsigned y) % 64) = sh)
    (h2 : 0 < (Zpow 2 sh))
    (h3 : ((q * (2 ^ (64 : Nat))) ≤ L ∧ L < ((q + 1) * (2 ^ (64 : Nat)))))
    (h4 : ((Int.fdiv lo (2 ^ (64 : Nat))) ≤ (Int.fdiv L (2 ^ (64 : Nat))) ∧ (Int.fdiv L (2 ^ (64 : Nat))) ≤ (Int.fdiv hi (2 ^ (64 : Nat)))))
    (h5 : (Int.fdiv L (2 ^ (64 : Nat))) = q)
    (h6 : (bv_unsigned (edenot E a)) = (L - (q * (2 ^ (64 : Nat))))) :
    (((tden E (ldiv_terms (Zpow 2 sh) ts)) * (Zpow 2 sh)) + (c - (q * (2 ^ (64 : Nat))))) = ((c + ((Zpow 2 sh) * (tden E (ldiv_terms (Zpow 2 sh) ts)))) - (q * (2 ^ (64 : Nat)))) := by
  fail_if_success lia
  sorry

-- glaze/binary_reflection: lib/GxSymExec3Sound.v (replace)
example
    {T1 T2 word T4 T5 : Type}
    (E : T1)
    (a : T2)
    (sh : Int)
    (y : word)
    (tden : T1 → T4 → Int)
    (ldiv_terms : Int → T5 → T4)
    (Zpow : Int → Int → Int)
    (ts : T5)
    (c : Int)
    (bv_unsigned : word → Int)
    (edenot : T1 → T2 → word)
    (q : Int)
    (L : Int)
    (lo : Int)
    (hi : Int)
    (h1 : ((bv_unsigned y) % 64) = sh)
    (h2 : 0 < (Zpow 2 sh))
    (h3 : ((q * (2 ^ (64 : Nat))) ≤ L ∧ L < ((q + 1) * (2 ^ (64 : Nat)))))
    (h4 : ((Int.fdiv lo (2 ^ (64 : Nat))) ≤ (Int.fdiv L (2 ^ (64 : Nat))) ∧ (Int.fdiv L (2 ^ (64 : Nat))) ≤ (Int.fdiv hi (2 ^ (64 : Nat)))))
    (h5 : (Int.fdiv L (2 ^ (64 : Nat))) = q)
    (h6 : (bv_unsigned (edenot E a)) = (L - (q * (2 ^ (64 : Nat))))) :
    (((tden E (ldiv_terms (Zpow 2 sh) ts)) * (Zpow 2 sh)) + c) = (c + ((Zpow 2 sh) * (tden E (ldiv_terms (Zpow 2 sh) ts)))) := by
  fail_if_success lia
  sorry

-- varnish/esi_parse_fuzzer: lib/Zn/RASlwvv.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 131056))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 131128)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- pupnp/FuzzHttp: lib/P0/RASlot_W3.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 132420))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 132420)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- jsoncons/fuzz_bigint: lib/CJ/Ref/RASlot_W3.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 131192))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 131192)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- leptonica/fhmtgen_fuzzer: lib/K5/A10/R_asan_calloc.v (replace)
example (nm : Int) (sz : Int) :
    (nm * sz) = (sz * nm) := by
  fail_if_success lia
  sorry

-- json-c/json_object_fuzzer: lib/Qc9I.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (off : Int)
    (UNIT : Int)
    (conc : T1 → T2 → Int)
    (st : T1)
    (c : T2)
    (p : T3)
    (real_off : T4 → T2 → T3 → Int)
    (ps_m : T5 → T4)
    (s : T5)
    (h1 : (real_off (ps_m s) c p) = off) :
    (off * UNIT) = (((conc st c) + (UNIT * off)) - (conc st c)) := by
  fail_if_success lia
  sorry

-- openssl/bignum: lib/BgA/R_asan_calloc.v (replace)
example (k : Int) (sz : Int) :
    (k * sz) = (sz * k) := by
  fail_if_success lia
  sorry

-- coturn/FuzzStunClient: lib/Asan/AxSymExec3Sound.v (replace)
example
    {T1 T2 T3 : Type}
    (A : Int)
    (t : Int)
    (Zpow : Int → Int → Int)
    (c : Int)
    (edenot : T1 → T2 → T3)
    (E : T1)
    (a : T2)
    (bv_unsigned : T3 → Int)
    (h1 : 0 < (Zpow 2 t))
    (h2 : (Int.fdiv (bv_unsigned (edenot E a)) (Zpow 2 t)) = ((Int.fdiv c (Zpow 2 t)) + A)) :
    ((A * (Zpow 2 t)) + c) = (c + ((Zpow 2 t) * A)) := by
  fail_if_success lia
  sorry

-- jsoncons/fuzz_json_cursor: lib/Pm9ArtSecAlloc.v (replace)
example
    (k : Int)
    (j : Int)
    (x : Int)
    (q : Int)
    (Zpow : Int → Int → Int)
    (r : Int)
    (h1 : (0 ≤ j ∧ j ≤ k))
    (h2 : (0 ≤ x ∧ x < (Zpow 2 k)))
    (h3 : 0 < (Zpow 2 j)) :
    ((q * (Zpow 2 j)) + r) = (((Zpow 2 j) * q) + r) := by
  fail_if_success lia
  sorry

-- json-c/json_object_fuzzer: lib/QcYs.v (replace)
example {T1 : Type} (class_size : T1 → Int) (c : T1) (req : Int) :
    ((class_size c) * req) = (req * (class_size c)) := by
  fail_if_success lia
  sorry

-- pupnp/FuzzHttp: lib/Spec/MI_WSlot2.v (replace)
example {T1 : Type} (UNIT : Int) (c3 : Int) (size_class : T1 → Int) (sc : T1) :
    (UNIT + (c3 * (UNIT * (size_class sc)))) = (((UNIT * (size_class sc)) * c3) + UNIT) := by
  fail_if_success lia
  sorry

-- glaze/binary_reflection: lib/AsAinvOpsPf3e.v (replace)
example
    {as_boot : Type}
    (bt : as_boot)
    (pos : Int)
    (FS : Int → Int)
    (k : Int)
    (bt_fs : as_boot → Int)
    (AS_HEAPLO : Int)
    (SBEG : Int)
    (h1 : AS_HEAPLO ≤ SBEG) :
    (pos * (FS k)) = (((((bt_fs bt) + 36864) + (k * (2 ^ (20 : Nat)))) + ((FS k) * pos)) - (((bt_fs bt) + 36864) + (k * (2 ^ (20 : Nat))))) := by
  fail_if_success lia
  sorry

-- glaze/binary_reflection: lib/AsAinvEntry3.v (replace)
example
    {T1 T2 : Type}
    (pos : Int)
    (FS : Int → Int)
    (k : Int)
    (bt_fs : T1 → Int)
    (bt : T1)
    (fpos : T1 → T2 → Int → Int)
    (fake_frame_addr : Int → Int → Int → T2)
    (h1 : (fpos bt (fake_frame_addr (bt_fs bt) k pos) k) = pos) :
    (pos * (FS k)) = (((((bt_fs bt) + 36864) + (k * (2 ^ (20 : Nat)))) + ((FS k) * pos)) - (((bt_fs bt) + 36864) + (k * (2 ^ (20 : Nat))))) := by
  fail_if_success lia
  sorry

-- leptonica/graymorph_fuzzer: lib/K5/B14/GmL_d3h_loop.v (assert)
example
    (i : Int)
    (wpl : Int)
    (h_1 : Int)
    (h1 : ((wpl * i) + wpl) ≤ (wpl * h_1))
    (h2 : 0 ≤ (wpl * i))
    (h3 : (0 ≤ (i * wpl) ∧ (i * wpl) ≤ 100000000)) :
    (i * wpl) = (wpl * i) := by
  fail_if_success lia
  sorry

-- boost-json/fuzz_parse: lib/Agent/ASlot_M5D.v (replace)
example (j : Int) (s : Int) (c : Int) (a : Int) (h1 : (Int.fdiv (a - c) s) = j) :
    (j * s) = ((c + (s * j)) - c) := by
  fail_if_success lia
  sorry

-- jsoncons/fuzz_ubjson_parser_max: lib/AxSymExec3Sound.v (replace)
example (A : Int) (sh : Int) (Zpow : Int → Int → Int) (c : Int) (T : Int) (h1 : 0 < (Zpow 2 sh)) :
    ((A * (Zpow 2 sh)) + (c + T)) = (c + (((Zpow 2 sh) * A) + T)) := by
  fail_if_success lia
  sorry

-- mbedtls/fuzz_pkcs7: lib/P/HP_RASlot_M4.v (replace)
example {T1 : Type} (UNIT : Int) (size_class : T1 → Int) (sc : T1) :
    (UNIT * (size_class sc)) = ((size_class sc) * UNIT) := by
  fail_if_success lia
  sorry

-- mbedtls/fuzz_pkcs7: lib/P/HP_RASlot_M4.v (replace)
example {T1 : Type} (UNIT : Int) (size_class : T1 → Int) (sc : T1) (cnt1 : Int) :
    ((UNIT * (size_class sc)) * cnt1) = (((size_class sc) * UNIT) * cnt1) := by
  fail_if_success lia
  sorry

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/TablRep.v (replace)
example {T1 : Type} (i : Int) (INSN_STRIDE : Int) (ti_insn : T1 → Int) (ti : T1) :
    (i * INSN_STRIDE) = (((ti_insn ti) + (INSN_STRIDE * i)) - (ti_insn ti)) := by
  fail_if_success lia
  sorry

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/TablRep.v (replace)
example {T1 : Type} (i : Int) (EXT_STRIDE : Int) (ti_ext : T1 → Int) (ti : T1) :
    (i * EXT_STRIDE) = (((ti_ext ti) + (EXT_STRIDE * i)) - (ti_ext ti)) := by
  fail_if_success lia
  sorry

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/TablRep.v (replace)
example {T1 : Type} (i : Int) (OPND_STRIDE : Int) (ti_opnd : T1 → Int) (ti : T1) :
    (i * OPND_STRIDE) = (((ti_opnd ti) + (OPND_STRIDE * i)) - (ti_opnd ti)) := by
  fail_if_success lia
  sorry

-- openssl/pem: lib/Malloc/MallocFacts_inv.v (replace)
example {T1 T2 : Type} (st : T1) (o0 : Int) (UNIT : Int) (conc : T1 → T2 → Int) (c0 : T2) :
    (o0 * UNIT) = (((conc st c0) + (UNIT * o0)) - (conc st c0)) := by
  fail_if_success lia
  sorry

-- skcms/iccprofile_info: lib/AsLib/AsSymExecSound.v (replace)
example
    {T1 word T3 : Type}
    (E : T1)
    (sh : Int)
    (y : word)
    (tden : T1 → T3 → Int)
    (ts' : T3)
    (Zpow : Int → Int → Int)
    (c : Int)
    (bv_unsigned : word → Int)
    (h1 : ((bv_unsigned y) % 64) = sh)
    (h2 : 0 < (Zpow 2 sh)) :
    (((tden E ts') * (Zpow 2 sh)) + c) = (c + ((Zpow 2 sh) * (tden E ts'))) := by
  fail_if_success lia
  sorry

-- libpcap/fuzz_pcap: lib/E2/S3/RMalloc_ifaceP__S3.v (replace)
example
    (sz : Int)
    (cnt : Int)
    (RCALLOC_MAX : Int)
    (h1 : (0 ≤ (sz * cnt) ∧ (sz * cnt) ≤ RCALLOC_MAX)) :
    (sz * cnt) = (cnt * sz) := by
  fail_if_success lia
  sorry

-- openssl/pem: lib/Common/AxSymExec3Sound.v (replace)
example
    {word : Type}
    (sh : Int)
    (y : word)
    (A : Int)
    (Zpow : Int → Int → Int)
    (c : Int)
    (T : Int)
    (bv_unsigned : word → Int)
    (h1 : ((bv_unsigned y) % 64) = sh)
    (h2 : 0 < (Zpow 2 sh))
    (h3 : (0 ≤ (Int.fdiv (c + T) (Zpow 2 sh)) ∧ (Int.fdiv (c + T) (Zpow 2 sh)) ≤ (c + T))) :
    ((A * (Zpow 2 sh)) + (c + T)) = (c + (((Zpow 2 sh) * A) + T)) := by
  fail_if_success lia
  sorry

-- openssl/pem: lib/Common/AxSymExec3Sound.v (replace)
example
    {T1 word T3 T4 : Type}
    (E : T1)
    (sh : Int)
    (y : word)
    (tden : T1 → T3 → Int)
    (ldiv_terms : Int → T4 → T3)
    (Zpow : Int → Int → Int)
    (ts : T4)
    (c : Int)
    (bv_unsigned : word → Int)
    (T : Int)
    (h1 : ((bv_unsigned y) % 64) = sh)
    (h2 : 0 < (Zpow 2 sh))
    (h3 : (0 ≤ (Int.fdiv (c + T) (Zpow 2 sh)) ∧ (Int.fdiv (c + T) (Zpow 2 sh)) ≤ (c + T))) :
    (((tden E (ldiv_terms (Zpow 2 sh) ts)) * (Zpow 2 sh)) + c) = (c + ((Zpow 2 sh) * (tden E (ldiv_terms (Zpow 2 sh) ts)))) := by
  fail_if_success lia
  sorry

-- libpcap/fuzz_pcap: lib/E2/S3/F_lock__S3.v (replace)
example (A : Int) (B : Int) (P : Int) :
    (A + (B * P)) = (A + (P * B)) := by
  fail_if_success lia
  sorry

-- libpcap/fuzz_pcap: lib/E2/S3/F_lock__S3.v (replace)
example (B : Int) (P : Int) (A : Int) :
    ((B * P) + A) = (A + (P * B)) := by
  fail_if_success lia
  sorry

-- leptonica/paintcmap_fuzzer: lib/K5/A21/Pm_hdr2.v (replace)
example
    (d : Int)
    (w : Int)
    (depth_okb : Int → Bool)
    (h_1 : Int)
    (h1 : (0 ≤ d ∧ d ≤ 32))
    (h2 : (depth_okb d) = true)
    (h3 : (1 ≤ (d * w) ∧ (d * w) ≤ 640000))
    (h4 : (1 ≤ ((((d * w) + 31) / 32) * h_1) ∧ ((((d * w) + 31) / 32) * h_1) ≤ 16777216)) :
    (d * w) = (w * d) := by
  fail_if_success lia
  sorry

-- leptonica/paintcmap_fuzzer: lib/K5/A21/Pm_hdr2.v (replace)
example
    (w : Int)
    (d : Int)
    (depth_okb : Int → Bool)
    (h_1 : Int)
    (h1 : (0 ≤ d ∧ d ≤ 32))
    (h2 : (depth_okb d) = true)
    (h3 : (1 ≤ (d * w) ∧ (d * w) ≤ 640000))
    (h4 : (1 ≤ ((((d * w) + 31) / 32) * h_1) ∧ ((((d * w) + 31) / 32) * h_1) ≤ 16777216)) :
    (w * d) = (d * w) := by
  fail_if_success lia
  sorry

-- double-conversion/string_to_double_fuzzer: lib/BnCbdLib.v (replace)
example
    (v : Int)
    (F : Int)
    (X : Int)
    (L : Int)
    (M : Int)
    (P : Int)
    (W : Int)
    (T : Int)
    (h1 : (0 ≤ v ∧ v < L))
    (h2 : (0 < F ∧ F ≤ X))
    (h3 : (0 < M ∧ M ≤ W))
    (h4 : (L * X) ≤ P)
    (h5 : 1 ≤ W)
    (h6 : (P * W) < T)
    (h7 : (v * F) < (L * X))
    (h8 : 0 ≤ P)
    (h9 : (P * 1) ≤ (P * W))
    (h10 : 0 ≤ (v * F))
    (h11 : ((v * F) * M) ≤ ((v * F) * W))
    (h12 : ((v * F) * W) < ((L * X) * W))
    (h13 : ((L * X) * W) ≤ (P * W)) :
    ((v * F) * M) = ((F * M) * v) := by
  fail_if_success lia
  sorry

-- double-conversion/string_to_double_fuzzer: lib/BnCbdLib.v (replace)
example
    (v : Int)
    (F : Int)
    (M : Int)
    (P : Int)
    (W : Int)
    (Q : Int)
    (T : Int)
    (h1 : (0 ≤ v ∧ v < Q))
    (h2 : (0 < F ∧ F ≤ P))
    (h3 : (0 < M ∧ M ≤ W))
    (h4 : 1 ≤ W)
    (h5 : ((Q * P) * W) < T)
    (h6 : (v * F) < (Q * P))
    (h7 : 0 ≤ (Q * P))
    (h8 : ((Q * P) * 1) ≤ ((Q * P) * W))
    (h9 : 0 ≤ (v * F))
    (h10 : ((v * F) * M) ≤ ((v * F) * W))
    (h11 : ((v * F) * W) < ((Q * P) * W)) :
    ((v * F) * M) = ((F * M) * v) := by
  fail_if_success lia
  sorry

-- tinyobjloader/fuzz_tobj_c: lib/Fw3/SymSoundM.v (replace)
example
    {T1 : Type}
    (bytes_le_to_Z : T1 → Int)
    (bs2 : T1)
    (w : Int)
    (Zpow : Int → Int → Int)
    (s : Int)
    (u : Int)
    (h1 : 0 < (Zpow 2 (8 * s)))
    (h2 : 0 < (Zpow 2 (8 * w)))
    (h3 : ((Int.fmod u (Zpow 2 (8 * w))) * (Zpow 2 (8 * s))) < (2 ^ (64 : Nat))) :
    (((bytes_le_to_Z bs2) * (Zpow 2 (8 * w))) * (Zpow 2 (8 * s))) = ((bytes_le_to_Z bs2) * ((Zpow 2 (8 * w)) * (Zpow 2 (8 * s)))) := by
  fail_if_success lia
  sorry

-- varnish/esi_parse_fuzzer: lib/Zq/ARt34mx.v (replace)
example
    {T1 : Type}
    (au : Int)
    (req : Int)
    (class_size : T1 → Int)
    (c : T1)
    (mu : Int)
    (ums : Int)
    (h1 : (((au + (req * (class_size c))) - mu) ≤ ums ∧ ums < (((au + (req * (class_size c))) - mu) + 262144))) :
    (((au + (req * (class_size c))) - mu) - 1) = (((au + ((class_size c) * req)) - mu) - 1) := by
  fail_if_success lia
  sorry

-- openssl/echconfiglist_parser: lib/LazyRestrict.v (replace)
example
    (z : Int)
    (q : Int)
    (ps : Int)
    (r : Int)
    (M : Int)
    (h1 : 0 ≤ z)
    (h2 : M = (ps * (2 ^ (52 : Nat))))
    (h3 : 0 < ps)
    (h4 : z = ((M * q) + r))
    (h5 : (0 ≤ r ∧ r < M))
    (h6 : (Int.fdiv z ps) = (((2 ^ (52 : Nat)) * q) + (Int.fdiv r ps))) :
    ((((2 ^ (52 : Nat)) * q) * ps) + r) = (((ps * (2 ^ (52 : Nat))) * q) + r) := by
  fail_if_success lia
  sorry

-- mbedtls/fuzz_pkcs7: lib/Heap/MI_Kit.v (replace)
example {T1 : Type} (i : Int) (stride : Int) (snd : T1 → Int) (p : T1) (UNIT : Int) :
    (i * stride) = ((((snd p) + (UNIT + (stride * i))) - (snd p)) - UNIT) := by
  fail_if_success lia
  sorry

-- varnish/esi_parse_fuzzer: lib/Yc/Hull.v (replace)
example (z : Int) (page_size : Int) (h1 : 0 ≤ z) :
    (page_size * (Int.fdiv z page_size)) = ((Int.fdiv z page_size) * page_size) := by
  fail_if_success lia
  sorry

-- leptonica/graymorph_fuzzer: lib/K5/B14/Gm_hdr_sure.v (replace)
example (d : Int) (w : Int) (h1 : (1 ≤ d ∧ d ≤ 32)) (h2 : (1 ≤ (d * w) ∧ (d * w) ≤ 640000)) :
    (d * w) = (w * d) := by
  fail_if_success lia
  sorry

-- jsoncons/fuzz_ubjson_parser_max: lib/AsanPlanSoundK.v (replace)
example (V : Int) (c : Int) (Y : Int) (h1 : (Int.fdiv (c * V) c) ≤ (Int.fdiv Y c)) :
    (V * c) = (c * V) := by
  fail_if_success lia
  sorry

-- openssl/pem: lib/MallocP/RF_aligned_spec.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (off : Int)
    (UNIT : Int)
    (conc : T1 → T2 → Int)
    (st : T1)
    (c : T2)
    (c_init_done : T3 → Int)
    (ctx : T1 → T3)
    (sstart : T4 → Int → Int)
    (MR : T1 → T5 → T4)
    (g : T5)
    (i : Int)
    (snd : T6 → Int)
    (bg : T6)
    (stride : Int)
    (A : Int)
    (r_base : T7 → Int)
    (r : T7)
    (round_up_pg : T8 → Int)
    (r_len : T7 → T8)
    (h1 : (c_init_done (ctx st)) ≠ 0)
    (h2 : (sstart (MR st g) i) = (((snd bg) + 16) + (stride * i)))
    (h3 : A = ((r_base r) + ((((snd bg) + 16) + (stride * i)) + (16 * off))))
    (h4 : stride < (2 ^ (20 : Nat)))
    (h5 : off ≤ 255)
    (h6 : (((r_base r) + (round_up_pg (r_len r))) ≤ 65536 ∨ 3198976 ≤ (r_base r))) :
    (off * UNIT) = (((conc st c) + (UNIT * off)) - (conc st c)) := by
  fail_if_success lia
  sorry

-- bzip2/bzip2_compress_target: lib/Bz/BzR5cG.v (replace)
example
    (r : Int)
    (m : Int)
    (q : Int)
    (Zpow : Int → Int → Int)
    (h1 : 1 ≤ r)
    (h2 : (Zpow 2 r) = (2 * (Zpow 2 (r - 1))))
    (h3 : 0 ≤ q)
    (h4 : (0 ≤ (Int.fdiv m (Zpow 2 (r - 1))) ∧ (Int.fdiv m (Zpow 2 (r - 1))) < 2)) :
    (m + ((q * 2) * (Zpow 2 (r - 1)))) = (((2 * (Zpow 2 (r - 1))) * q) + m) := by
  fail_if_success lia
  sorry

-- yajl-ruby/json_fuzzer: lib/U/UASlot_W3.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 139824))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 139824)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- speex/speex_decode_fuzzer_float: lib/Ref/X1k5.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 131056))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 131316)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- openssl/bignum: lib/Spec/BgInvSpec.v (replace)
example
    (sh1 : Int)
    (Zpow : Int → Int → Int)
    (X1 : Int)
    (a : Int)
    (sh2 : Int)
    (Z_odd : Int → Bool)
    (B1 : Int)
    (A1 : Int)
    (N_1 : Int)
    (Z_gcd : Int → Int → Int)
    (h1 : 0 < (Zpow 2 sh1))
    (h2 : 0 < (Zpow 2 sh2))
    (h3 : (Z_odd B1) = true)
    (h4 : (Z_odd A1) = true)
    (h5 : (0 < B1 ∧ B1 ≤ N_1))
    (h6 : ((Zpow 2 sh1) * B1) ≤ 0)
    (h7 : (0 < A1 ∧ A1 ≤ N_1))
    (h8 : ((Zpow 2 sh2) * A1) ≤ 0)
    (h9 : (Z_gcd (Zpow 2 sh1) N_1) = 1)
    (h10 : (Z_gcd (Zpow 2 sh2) N_1) = 1)
    (h11 : (Int.fmod (X1 * a) N_1) = (Int.fmod B1 N_1)) :
    (((Zpow 2 sh1) * X1) * a) = ((X1 * a) * (Zpow 2 sh1)) := by
  fail_if_success lia
  sorry

-- json-c/json_object_fuzzer: lib/Qkaz.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 881216))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 881216)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- json-c/json_object_fuzzer: lib/Qkaz.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 849368))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 849368)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- yajl-ruby/json_fuzzer: lib/R/RASlot_W3.v (replace)
example
    {T1 T2 T3 : Type}
    (cnt : Int)
    (size : Int)
    (Z_shiftr : T1 → Int → Int)
    (meta_word : T2 → T1)
    (mr : T2)
    (span_exit : Int → Int → Int → Bool)
    (span : Int)
    (size_class : T3 → Int)
    (sc' : T3)
    (ai0 : Int)
    (h1 : (0 ≤ (Z_shiftr (meta_word mr) 5) ∧ (Z_shiftr (meta_word mr) 5) < (2 ^ (64 : Nat))))
    (h2 : (16 ≤ size ∧ size ≤ 137416))
    (h3 : (2 ≤ cnt ∧ cnt ≤ 33))
    (h4 : (0 ≤ (cnt * size) ∧ (cnt * size) ≤ (33 * 137416)))
    (h5 : (span_exit 300 span size) = true)
    (h6 : span = ((cnt * size) + 16))
    (h7 : size = ((size_class sc') * 16))
    (h8 : cnt = (ai0 + 2)) :
    (cnt * size) = (size * cnt) := by
  fail_if_success lia
  sorry

-- mbedtls/fuzz_pkcs7: lib/Lib/MpiCoreAux.v (replace)
example (x : Int) (Q : Int) (L : Int) (P : Int) (R : Int) :
    (x + (((Q * L) + (((P * Q) * Q) * R)) * P)) = (x + ((P * Q) * (L + ((P * Q) * R)))) := by
  fail_if_success lia
  sorry

-- mbedtls/fuzz_pkcs7: lib/Lib/MpiCoreAux.v (replace)
example (L : Int) (Q : Int) (R : Int) (P : Int) :
    (L + ((Q * R) * P)) = (L + ((P * Q) * R)) := by
  fail_if_success lia
  sorry

-- leptonica/grayquant_fuzzer: lib/K5/A15/Lept_hdr.v (replace)
example (d : Int) (w : Int) (h1 : 0 < w) (h2 : 1 ≤ d) (h3 : (1 ≤ (d * w) ∧ (d * w) ≤ 640000)) :
    (d * w) = (w * d) := by
  fail_if_success lia
  sorry

-- openssl/bignum: lib/Spec/MI_Kit.v (replace)
example {T1 : Type} (k : Int) (stride : Int) (snd : T1 → Int) (p : T1) (UNIT : Int) :
    (k * stride) = ((((snd p) + (UNIT + (stride * k))) - (snd p)) - UNIT) := by
  fail_if_success lia
  sorry

-- jsoncons/fuzz_ubjson_parser_max: lib/JatSecAlloc.v (replace)
example (q : Int) (j : Int) (Zpow : Int → Int → Int) (r : Int) (h1 : 0 < (Zpow 2 j)) :
    ((q * (Zpow 2 j)) + r) = (((Zpow 2 j) * q) + r) := by
  fail_if_success lia
  sorry

-- fast_float/from_chars: lib/Common/FxStep.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (sgn64 : T1 → Int)
    (c : T1)
    (K : Int)
    (two64 : Int)
    (q : Int)
    (k : Int)
    (Zpow : Int → Int → Int)
    (fst : T2 → Int)
    (l_iv : T3 → T4 → T2)
    (fs : T3)
    (LIN : T1 → T5 → T4)
    (t0 : T5)
    (snd : T2 → Int)
    (bv_unsigned : T6 → Int)
    (lden : T7 → T4 → T6)
    (E : T7)
    (izl : T7 → T4 → Int)
    (tsumz : T7 → T5 → Int)
    (Z_shiftr : Int → Int → Int)
    (t' : Int)
    (h1 : 0 < two64)
    (h2 : ((K * two64) ≤ (fst (l_iv fs (LIN c t0))) ∧ (fst (l_iv fs (LIN c t0))) < ((K * two64) + two64)))
    (h3 : ((K * two64) ≤ (snd (l_iv fs (LIN c t0))) ∧ (snd (l_iv fs (LIN c t0))) < ((K * two64) + two64)))
    (h4 : (bv_unsigned (lden E (LIN c t0))) = ((izl E (LIN c t0)) - (K * two64)))
    (h5 : (izl E (LIN c t0)) = ((sgn64 c) + (tsumz E t0)))
    (h6 : 0 < (Zpow 2 k))
    (h7 : (Z_shiftr (bv_unsigned (lden E (LIN c t0))) k) = (q + t')) :
    (((sgn64 c) - (K * two64)) + (q * (Zpow 2 k))) = (((sgn64 c) + ((Zpow 2 k) * q)) - (K * two64)) := by
  fail_if_success lia
  sorry

-- fast_float/from_chars: lib/Common/FxStep.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (sgn64 : T1 → Int)
    (c : T1)
    (K : Int)
    (two64 : Int)
    (q : Int)
    (k : Int)
    (Zpow : Int → Int → Int)
    (fst : T2 → Int)
    (iv : T2)
    (V : Int)
    (snd : T2 → Int)
    (E : T3)
    (LIN : T1 → T4 → T5)
    (t0 : T4)
    (bv_unsigned : T6 → Int)
    (lden : T3 → T5 → T6)
    (Z_shiftr : Int → Int → Int)
    (t' : Int)
    (h1 : ((fst iv) ≤ V ∧ V ≤ (snd iv)))
    (h2 : 0 < two64)
    (h3 : ((K * two64) ≤ (fst iv) ∧ (fst iv) < ((K * two64) + two64)))
    (h4 : ((K * two64) ≤ (snd iv) ∧ (snd iv) < ((K * two64) + two64)))
    (h5 : (bv_unsigned (lden E (LIN c t0))) = (V - (K * two64)))
    (h6 : 0 < (Zpow 2 k))
    (h7 : (Z_shiftr (bv_unsigned (lden E (LIN c t0))) k) = (q + t')) :
    (((sgn64 c) - (K * two64)) + (q * (Zpow 2 k))) = (((sgn64 c) + ((Zpow 2 k) * q)) - (K * two64)) := by
  fail_if_success lia
  sorry

-- leptonica/paintcmap_fuzzer: lib/K5/B21/Pm_hdr2.v (replace)
example
    (w : Int)
    (d : Int)
    (depth_okb : Int → Bool)
    (h_1 : Int)
    (h1 : (0 ≤ d ∧ d ≤ 32))
    (h2 : (1 ≤ d ∧ d ≤ 32))
    (h3 : (depth_okb d) = true)
    (h4 : (1 ≤ (d * w) ∧ (d * w) ≤ 640000))
    (h5 : (1 ≤ ((((d * w) + 31) / 32) * h_1) ∧ ((((d * w) + 31) / 32) * h_1) ≤ 16777216)) :
    (w * d) = (d * w) := by
  fail_if_success lia
  sorry

-- leptonica/paintcmap_fuzzer: lib/K5/B21/Pm_hdr2.v (replace)
example
    (d : Int)
    (w : Int)
    (depth_okb : Int → Bool)
    (h_1 : Int)
    (h1 : (0 ≤ d ∧ d ≤ 32))
    (h2 : (1 ≤ d ∧ d ≤ 32))
    (h3 : (depth_okb d) = true)
    (h4 : (1 ≤ (d * w) ∧ (d * w) ≤ 640000))
    (h5 : (1 ≤ ((((d * w) + 31) / 32) * h_1) ∧ ((((d * w) + 31) / 32) * h_1) ≤ 16777216)) :
    (d * w) = (w * d) := by
  fail_if_success lia
  sorry

-- simdjson/fuzz_parser: lib/Seg/SegSrl.v (replace)
example (s : Int) (A : Int) (Zpow : Int → Int → Int) (c : Int) (T : Int) (h1 : 0 < (Zpow 2 s)) :
    ((A * (Zpow 2 s)) + (c + T)) = (c + (((Zpow 2 s) * A) + T)) := by
  fail_if_success lia
  sorry

-- simdjson/fuzz_parser: lib/Seg/SegSrl.v (replace)
example (s : Int) (A : Int) (Zpow : Int → Int → Int) (c : Int) (h1 : 0 < (Zpow 2 s)) :
    ((A * (Zpow 2 s)) + c) = (c + (((Zpow 2 s) * A) + 0)) := by
  fail_if_success lia
  sorry

-- boost-beast/http_request: lib/SymExec2SoundX.v (replace)
example
    (j : Int)
    (q : Int)
    (Zpow : Int → Int → Int)
    (r : Int)
    (h1 : (0 ≤ j ∧ j < 64))
    (h2 : 0 < (Zpow 2 j)) :
    ((q * (Zpow 2 j)) + r) = (((Zpow 2 j) * q) + r) := by
  fail_if_success lia
  sorry

-- boost-beast/http_request: lib/SymExec2SoundX.v (replace)
example
    {T1 word T3 T4 : Type}
    (E : T1)
    (sh : Int)
    (y : word)
    (tden : T1 → T3 → Int)
    (ldiv_terms : Int → T4 → T3)
    (Zpow : Int → Int → Int)
    (ts : T4)
    (c : Int)
    (bv_unsigned : word → Int)
    (h1 : ((bv_unsigned y) % 64) = sh)
    (h2 : 0 < (Zpow 2 sh)) :
    (((tden E (ldiv_terms (Zpow 2 sh) ts)) * (Zpow 2 sh)) + c) = (c + ((Zpow 2 sh) * (tden E (ldiv_terms (Zpow 2 sh) ts)))) := by
  fail_if_success lia
  sorry

-- jsoncons/fuzz_json_cursor: lib/CutCert/CutRtA.v (replace)
example (p : Int) (q : Int) (m : Int) :
    ((p * q) * m) = (p * (q * m)) := by
  fail_if_success lia
  sorry

-- jsoncons/fuzz_bson_parser_max: lib/AsanPlanSoundK.v (replace)
example
    (Y : Int)
    (c : Int)
    (V : Int)
    (h1 : 0 < c)
    (h2 : (c * V) ≤ Y)
    (h3 : (Int.fdiv (c * V) c) ≤ (Int.fdiv Y c)) :
    (V * c) = (c * V) := by
  fail_if_success lia
  sorry

-- zstd/fse_read_ncount: lib/Plain/RASlot_M4.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (cnt1 : Int)
    (ATOP : Int)
    (bv_unsigned : word → Int)
    (RAS_STACK : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : ATOP ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (RAS_STACK sc))) :
    ((UNIT * (size_class sc)) * cnt1) = (((size_class sc) * UNIT) * cnt1) := by
  fail_if_success lia
  sorry

-- zstd/fse_read_ncount: lib/Plain/RASlot_M4.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (sc : Int)
    (req : Int)
    (UNIT : Int)
    (size_class : Int → Int)
    (ATOP : Int)
    (bv_unsigned : word → Int)
    (RAS_STACK : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h3 : (req + 4) ≤ (16 * (size_class sc)))
    (h4 : ATOP ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - (RAS_STACK sc))) :
    (UNIT * (size_class sc)) = ((size_class sc) * UNIT) := by
  fail_if_success lia
  sorry

/-! Signs of products: Rocq's `lia` also uses products of hypotheses, e.g. `0 < x`, `0 < y` and
`x * y ≤ 0` are contradictory. -/

-- leptonica/grayquant_fuzzer: lib/O15/O15LeptDithBinSpec.v (assert)
example
    (wpl_of : Int → Int → Int)
    (w : Int)
    (h_1 : Int)
    (h1 : (0 ≤ w ∧ w < (2 ^ (31 : Nat))))
    (h2 : (0 ≤ h_1 ∧ h_1 < (2 ^ (31 : Nat))))
    (h3 : 0 < (4 * ((wpl_of w 1) * h_1)))
    (h4 : 0 < (4 * ((wpl_of w 8) * h_1))) :
    0 < (4 * (wpl_of w 8)) := by
  fail_if_success lia
  sorry

-- leptonica/grayquant_fuzzer: lib/O15/O15LeptDith2Spec.v (assert)
example
    (wpl_of : Int → Int → Int)
    (w : Int)
    (h_1 : Int)
    (h1 : (0 ≤ w ∧ w < (2 ^ (31 : Nat))))
    (h2 : (0 ≤ h_1 ∧ h_1 < (2 ^ (31 : Nat))))
    (h3 : 0 < (4 * ((wpl_of w 2) * h_1)))
    (h4 : 0 < (4 * ((wpl_of w 8) * h_1))) :
    0 < (4 * (wpl_of w 8)) := by
  fail_if_success lia
  sorry

-- openssl/bignum: lib/Spec/BgInvSpec.v (replace)
example
    (B : Int)
    (B1 : Int)
    (sh1 : Int)
    (Zpow : Int → Int → Int)
    (sh2 : Int)
    (Z_odd : Int → Bool)
    (A1 : Int)
    (N_1 : Int)
    (Z_gcd : Int → Int → Int)
    (X1 : Int)
    (a : Int)
    (h1 : 0 < (Zpow 2 sh1))
    (h2 : 0 < (Zpow 2 sh2))
    (h3 : (Z_odd B1) = true)
    (h4 : (Z_odd A1) = true)
    (h5 : (0 < B1 ∧ B1 ≤ N_1))
    (h6 : ((Zpow 2 sh1) * B1) ≤ 0)
    (h7 : (0 < A1 ∧ A1 ≤ N_1))
    (h8 : ((Zpow 2 sh2) * A1) ≤ 0)
    (h9 : (Z_gcd (Zpow 2 sh1) N_1) = 1)
    (h10 : (Z_gcd (Zpow 2 sh2) N_1) = 1)
    (h11 : (Int.fmod (X1 * a) N_1) = (Int.fmod B1 N_1)) :
    B = (B1 * (Zpow 2 sh1)) := by
  fail_if_success lia
  sorry

-- openssl/bignum: lib/Spec/BgInvSpec.v (replace)
example
    (sh2 : Int)
    (Zpow : Int → Int → Int)
    (Y1 : Int)
    (a : Int)
    (A : Int)
    (A1 : Int)
    (sh1 : Int)
    (Z_odd : Int → Bool)
    (B1 : Int)
    (N_1 : Int)
    (Z_gcd : Int → Int → Int)
    (X1 : Int)
    (h1 : 0 < (Zpow 2 sh1))
    (h2 : 0 < (Zpow 2 sh2))
    (h3 : (Z_odd B1) = true)
    (h4 : (Z_odd A1) = true)
    (h5 : (0 < B1 ∧ B1 ≤ N_1))
    (h6 : ((Zpow 2 sh1) * B1) ≤ 0)
    (h7 : (0 < A1 ∧ A1 ≤ N_1))
    (h8 : ((Zpow 2 sh2) * A1) ≤ 0)
    (h9 : (Z_gcd (Zpow 2 sh1) N_1) = 1)
    (h10 : (Z_gcd (Zpow 2 sh2) N_1) = 1)
    (h11 : (Int.fmod (X1 * a) N_1) = (Int.fmod B1 N_1))
    (h12 : (Int.fmod ((Y1 * a) + A1) N_1) = 0)
    (h13 : (Int.fmod (((Y1 * a) + A1) * (Zpow 2 sh2)) N_1) = (Int.fmod (0 * (Zpow 2 sh2)) N_1)) :
    ((((Zpow 2 sh2) * Y1) * a) + A) = (((Y1 * a) + A1) * (Zpow 2 sh2)) := by
  fail_if_success lia
  sorry

-- openssl/bignum: lib/Spec/BgInvSpec.v (assert)
example
    (sh1 : Int)
    (Zpow : Int → Int → Int)
    (X1 : Int)
    (A : Int)
    (sh2 : Int)
    (Y1 : Int)
    (B : Int)
    (N_1 : Int)
    (Z_odd : Int → Bool)
    (B1 : Int)
    (A1 : Int)
    (Z_gcd : Int → Int → Int)
    (a : Int)
    (X : Int)
    (Y : Int)
    (h1 : 0 < (Zpow 2 sh1))
    (h2 : 0 < (Zpow 2 sh2))
    (h3 : (Z_odd B1) = true)
    (h4 : (Z_odd A1) = true)
    (h5 : (0 < B1 ∧ B1 ≤ N_1))
    (h6 : ((Zpow 2 sh1) * B1) ≤ 0)
    (h7 : (0 < A1 ∧ A1 ≤ N_1))
    (h8 : ((Zpow 2 sh2) * A1) ≤ 0)
    (h9 : (Z_gcd (Zpow 2 sh1) N_1) = 1)
    (h10 : (Z_gcd (Zpow 2 sh2) N_1) = 1)
    (h11 : (Int.fmod (X1 * a) N_1) = (Int.fmod B1 N_1))
    (h12 : (Int.fmod ((Y1 * a) + A1) N_1) = 0)
    (h13 : (Int.fmod (((Y1 * a) + A1) * (Zpow 2 sh2)) N_1) = (Int.fmod (0 * (Zpow 2 sh2)) N_1))
    (h14 : ((X1 * A1) + (Y1 * B1)) ≤ (N_1 * N_1))
    (h15 : ((Zpow 2 (sh1 + sh2)) * ((X1 * A1) + (Y1 * B1))) = ((((Zpow 2 sh1) * X1) * A) + (((Zpow 2 sh2) * Y1) * B)))
    (h16 : 0 < (Zpow 2 (sh1 + sh2)))
    (h17 : (((Zpow 2 sh1) * X1) * A) ≤ ((X + (N_1 * ((Zpow 2 sh1) - 1))) * A))
    (h18 : (((Zpow 2 sh2) * Y1) * B) ≤ ((Y + (N_1 * ((Zpow 2 sh2) - 1))) * B))
    (h19 : ((N_1 * ((Zpow 2 sh1) - 1)) * A) ≤ ((N_1 * ((Zpow 2 sh1) - 1)) * N_1))
    (h20 : ((N_1 * ((Zpow 2 sh2) - 1)) * B) ≤ ((N_1 * ((Zpow 2 sh2) - 1)) * N_1))
    (h21 : ((X + (N_1 * ((Zpow 2 sh1) - 1))) * A) = ((X * A) + ((N_1 * ((Zpow 2 sh1) - 1)) * A)))
    (h22 : ((Y + (N_1 * ((Zpow 2 sh2) - 1))) * B) = ((Y * B) + ((N_1 * ((Zpow 2 sh2) - 1)) * B)))
    (h23 : ((N_1 * N_1) * (((Zpow 2 sh1) + (Zpow 2 sh2)) - 1)) = (((N_1 * N_1) + ((N_1 * ((Zpow 2 sh1) - 1)) * N_1)) + ((N_1 * ((Zpow 2 sh2) - 1)) * N_1))) :
    ((((Zpow 2 sh1) * X1) * A) + (((Zpow 2 sh2) * Y1) * B)) ≤ ((N_1 * N_1) * (((Zpow 2 sh1) + (Zpow 2 sh2)) - 1)) := by
  fail_if_success lia
  sorry

/-! Case splits: `lia` stops at its case-split limit (`splits := 9`) on this goal. -/

-- yajl-ruby/json_fuzzer: lib/B/BI_pcommon.v (assert)
example
    {list_Z : Type}
    (q : Int)
    (lo : Int)
    (A : Int)
    (AQ : Int)
    (SB : Int)
    (c : Int)
    (NF : Nat)
    (SA : Int)
    (zs : list_Z)
    (NA : Nat)
    (zlength : list_Z → Int)
    (fmt : list_Z)
    (shw_hi : Int → Int → Int → Int)
    (shw_lo : Int → Int → Int)
    (alloc_ceiling : Int)
    (h1 : (c = 115 ∨ (c = 100 ∨ c = 117)))
    (h2 : (zlength fmt) ≤ 63)
    (h3 : (65536 ≤ A ∧ (A + 64) ≤ 200704))
    (h4 : ((NF : Nat) : Int) = ((shw_hi SB A ((zlength fmt) + 1)) - (shw_lo SB A)))
    (h5 : alloc_ceiling ≤ lo)
    (h6 : lo ≤ (q - 2320))
    (h7 : q < (2 ^ (47 : Nat)))
    (h8 : ((AQ + 8) ≤ lo ∨ q ≤ AQ))
    (h9 : (0 < AQ ∧ (AQ + 8) < (2 ^ (47 : Nat))))
    (h10 : ((SB + 17592186044416) ≤ SA ∧ (((SA + (zlength zs)) + 1) < (2 ^ (47 : Nat)) ∧ ((zlength zs) + 1) < (2 ^ (40 : Nat)))))
    (h11 : (((SA + (zlength zs)) + 1) ≤ lo ∨ q ≤ SA))
    (h12 : ((NA : Nat) : Int) = ((shw_hi SB SA ((zlength zs) + 1)) - (shw_lo SB SA))) :
    ((0 < c ∧ c < 256) ∧ (c ≠ 37 ∧ (c ≠ 42 ∧ (c ≠ 46 ∧ (c ≠ 108 ∧ (c ≠ 104 ∧ (c ≠ 109 ∧ (c ≠ 110 ∧ 9 < (c - 48))))))))) := by
  fail_if_success lia
  sorry
