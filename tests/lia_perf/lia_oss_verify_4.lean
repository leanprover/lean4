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

Part 4 of 4. `lia_oss_verify_failing.lean` has the goals that `lia` does not prove yet.
-/

set_option linter.unusedVariables false

-- simdjson/fuzz_parser: lib/SegT/B1G_mcb.v (replace)
example
    {T1 T2 T3 : Type}
    (sp : Int)
    (T : Int)
    (bv_unsigned : T1 → Int)
    (SHD : T1)
    (MB_SHOFF : Int)
    (edenot : T2 → T3 → T1)
    (E : T2)
    (MB_dst : T3)
    (h1 : (0 ≤ T ∧ T < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ sp ∧ sp < (2 ^ (64 : Nat))))
    (h3 : (8 * (bv_unsigned SHD)) = ((T - 8192) + (8 * MB_SHOFF)))
    (h4 : (Int.fmod ((8 * (bv_unsigned SHD)) - T) (2 ^ (64 : Nat))) = ((8 * 2147450880) - 8192))
    (h5 : (Int.fdiv ((8 * (bv_unsigned SHD)) - T) (2 ^ (64 : Nat))) = (-1))
    (h6 : (Int.fdiv ((8 * (bv_unsigned SHD)) - T) (2 ^ (64 : Nat))) = 0)
    (h7 : (T % 16) = 0)
    (h8 : (400 ≤ (T - sp) ∧ (T - sp) ≤ 8192))
    (h9 : (Int.fdiv (T - sp) (2 ^ (64 : Nat))) = (-1))
    (h10 : (bv_unsigned (edenot E MB_dst)) = (T - 400)) :
    (sp - 2224) = (sp + (-2224)) := by
  lia

-- simdjson/fuzz_parser: lib/SegT/B1G_mcb.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (T : Int)
    (sp : Int)
    (bv_unsigned : T1 → Int)
    (SHD : T1)
    (MB_SHOFF : Int)
    (edenot : T2 → T3 → T1)
    (E : T2)
    (MB_dst : T3)
    (ctab_bytes : T4)
    (length : T4 → Nat)
    (Z_to_bv : Int → Int → T1)
    (RLO2 : Int)
    (ASHOFF : Int)
    (h1 : (0 ≤ T ∧ T < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ sp ∧ sp < (2 ^ (64 : Nat))))
    (h3 : (8 * (bv_unsigned SHD)) = ((T - 8192) + (8 * MB_SHOFF)))
    (h4 : (Int.fmod ((8 * (bv_unsigned SHD)) - T) (2 ^ (64 : Nat))) = ((8 * 2147450880) - 8192))
    (h5 : (Int.fdiv ((8 * (bv_unsigned SHD)) - T) (2 ^ (64 : Nat))) = (-1))
    (h6 : (Int.fdiv ((8 * (bv_unsigned SHD)) - T) (2 ^ (64 : Nat))) = 0)
    (h7 : (T % 16) = 0)
    (h8 : (400 ≤ (T - sp) ∧ (T - sp) ≤ 8192))
    (h9 : (Int.fdiv (T - sp) (2 ^ (64 : Nat))) = (-1))
    (h10 : (bv_unsigned (edenot E MB_dst)) = (T - 400))
    (h11 : (length ctab_bytes) = (Int.toNat (bv_unsigned (Z_to_bv 64 256))))
    (h12 : (((T - 463) ≤ RLO2 ∧ RLO2 ≤ (T - 400)) ∧ (RLO2 % 64) = 0))
    (h13 : ((RLO2 + 320) / 8) = ((RLO2 / 8) + 40))
    (h14 : ((bv_unsigned SHD) ≤ (ASHOFF + (RLO2 / 8)) ∧ ((ASHOFF + (RLO2 / 8)) + 40) ≤ ((bv_unsigned SHD) + 1024)))
    (h15 : (((length ctab_bytes) : Nat) : Int) = 256) :
    (T - 400) = (T + (-400)) := by
  lia

-- simdjson/fuzz_print_json: lib/A/Pj_lftoi3A.v (replace)
example
    {T1 T2 : Type}
    (f : Int)
    (shad : Int → Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (S1 : Int)
    (lo : Int)
    (sa_buf : T2 → Int)
    (st' : T2)
    (sa_cap : T2 → Int)
    (sa_heap : T2 → Bool)
    (sa_size : T2 → Int)
    (h1 : (shad (f + 1024)) = ((shad f) + 128))
    (h2 : 0 ≤ (f / 8))
    (h3 : (bv_unsigned (Z_to_bv 64 S1)) = S1)
    (h4 : (lo + 64) ≤ S1)
    (h5 : (0 < (sa_buf st') ∧ (((sa_buf st') + (sa_cap st')) ≤ lo ∧ (((sa_heap st') = true → ((f + 1024) ≤ (sa_buf st') ∨ ((sa_buf st') + (sa_cap st')) ≤ f)) ∧ ((sa_heap st') = false → (sa_buf st') = (f + 32))))))
    (h6 : (((sa_buf st') + (sa_cap st')) ≤ (f + 272) ∨ ((f + 272) + 288) ≤ (sa_buf st')))
    (h7 : ((0 ≤ (sa_buf st') ∧ (sa_buf st') < (2 ^ (64 : Nat))) ∧ ((0 ≤ (sa_size st') ∧ (sa_size st') < (2 ^ (64 : Nat))) ∧ (0 ≤ (sa_cap st') ∧ (sa_cap st') < (2 ^ (64 : Nat)))))) :
    (f + 96) = ((f + 32) + ((64 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_print_json: lib/A/Pj_topA.v (replace)
example (f : Int) :
    (((f / 8) + 2147450880) + 80) = (((f / 8) + 2147450880) + ((80 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_print_json: lib/A/Pj_topA.v (replace)
example
    {T1 : Type}
    (f : Int)
    (Z_to_bv : Int → Int → T1)
    (d : Int)
    (bv_unsigned : T1 → Int)
    (sp' : Int)
    (shad : Int → Int)
    (fs_size : Int → Int)
    (h1 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h2 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h3 : (shad (f + 1024)) = ((shad f) + 128))
    (h4 : 0 ≤ (f / 8))
    (h5 : (shad (f + (fs_size 4))) = (((f / 8) + 2147450880) + 128)) :
    (f + 184) = ((f + 160) + ((24 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_print_json: lib/A/Pj_topA.v (replace)
example
    {T1 : Type}
    (sp' : Int)
    (Z_to_bv : Int → Int → T1)
    (d : Int)
    (bv_unsigned : T1 → Int)
    (shad : Int → Int)
    (f : Int)
    (fs_size : Int → Int)
    (h1 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h2 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h3 : (shad (f + 1024)) = ((shad f) + 128))
    (h4 : 0 ≤ (f / 8))
    (h5 : (shad (f + (fs_size 4))) = (((f / 8) + 2147450880) + 128)) :
    (sp' + 24) = (sp' + ((24 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_print_json: lib/A/R_getfrom.v (replace)
example
    {word list_word T3 : Type}
    (sp : word)
    (ACEIL : Int)
    (SB : Int)
    (c : Int)
    (R : Int)
    (CH : Int)
    (n : Int)
    (nfree' : Int)
    (lo : Int)
    (ws : list_word)
    (chs : list_word)
    (rinfo : T3 → Int → Int)
    (RIS_of : Int → T3)
    (length : list_word → Nat)
    (kHighShadowEnd : Int)
    (bv_unsigned : word → Int)
    (h1 : (1 ≤ c ∧ c ≤ 31))
    (h2 : R = (rinfo (RIS_of SB) c))
    (h3 : (1 ≤ n ∧ n ≤ 16))
    (h4 : 0 ≤ nfree')
    (h5 : ((4 * (nfree' + n)) ≤ (4 * (((length ws) : Nat) : Int)) ∧ (4 * (((length ws) : Nat) : Int)) ≤ (2 ^ (29 : Nat))))
    (h6 : (length chs) = 16)
    (h7 : (0 < CH ∧ ((CH + 64) ≤ ACEIL ∧ ((CH + 64) ≤ SB ∨ ((SB + (2 ^ (37 : Nat))) + 4096) ≤ CH))))
    (h8 : ACEIL ≤ lo)
    (h9 : (kHighShadowEnd + 8) ≤ lo)
    (h10 : lo ≤ ((bv_unsigned sp) - 128))
    (h11 : (bv_unsigned sp) ≤ (2 ^ (47 : Nat))) :
    (CH + (4 * n)) = (CH + (n * 4)) := by
  lia

-- simdjson/fuzz_print_json: lib/A/R_qmerge3.v (replace)
example
    {T1 T2 : Type}
    (length : T1 → Nat)
    (X : T1)
    (qlast : T1 → Int)
    (b : Int)
    (b' : Int)
    (FROM : Int)
    (TO : Int)
    (fst : T2 → Int)
    (x : T2)
    (h1 : ((((length X) : Nat) : Int) ≠ 0 → ((0 < (qlast X) ∧ ((qlast X) + 8192) ≤ (2 ^ (47 : Nat))) ∧ ((((qlast X) + 8192) ≤ b ∨ (b + 8192) ≤ (qlast X)) ∧ ((((qlast X) + 8192) ≤ b' ∨ (b' + 8192) ≤ (qlast X)) ∧ (((FROM + 32) ≤ (qlast X) ∨ ((qlast X) + 8192) ≤ FROM) ∧ ((TO + 32) ≤ (qlast X) ∨ ((qlast X) + 8192) ≤ TO)))))))
    (h2 : ((((fst x) + 8192) ≤ b ∨ (b + 8192) ≤ (fst x)) ∧ (((fst x) + 8192) ≤ b' ∨ (b' + 8192) ≤ (fst x)))) :
    ((((length X) : Nat) : Int) + 1) = ((((length X) + 1) : Nat) : Int) := by
  lia

-- simdjson/fuzz_print_json: lib/A/R_secalloc_p2.v (replace)
example
    (P : Int)
    (SZ : Int)
    (sa_msz : Int → Int)
    (h1 : (0 < SZ ∧ ((SZ % 8) = 0 ∧ (SZ + 16384) ≤ (2 ^ (47 : Nat)))))
    (h2 : (P % 4096) = 0)
    (h3 : (SZ % 4096) = 0)
    (h4 : ((P + (sa_msz SZ)) % 4096) = 0) :
    P = ((P + 4096) + (-4096)) := by
  lia

-- simdjson/fuzz_print_json: lib/A/Sj_num_wrap2.v (assert)
example
    {nwenv T2 : Type}
    (E : nwenv)
    (bv_unsigned : T2 → Int)
    (c : T2)
    (w_stop : nwenv → Int)
    (w_TL : nwenv → Int)
    (w_n : nwenv → Int)
    (cur : Int)
    (numchar : Int → Bool)
    (h1 : (w_stop E) < (w_TL E))
    (h2 : ((w_n E) - 7) ≤ (8 * ((w_n E) / 8)))
    (h3 : (0 ≤ (bv_unsigned c) ∧ (bv_unsigned c) < 256))
    (h4 : (cur = (w_stop E) → (numchar (bv_unsigned c)) = false))
    (h5 : (numchar (bv_unsigned c)) = true)
    (h6 : cur ≠ (w_stop E))
    (h7 : (43 ≤ (bv_unsigned c) ∧ (bv_unsigned c) ≤ 101))
    (h8 : (¬ (48 ≤ (bv_unsigned c) ∧ (bv_unsigned c) ≤ 57)))
    (h9 : cur = (w_stop E)) :
    (43 ≤ (bv_unsigned c) ∧ (bv_unsigned c) ≤ 101) := by
  lia

-- simdjson/fuzz_print_json: lib/A/Sj_num_wrap2.v (assert)
example
    {nwenv T2 : Type}
    (E : nwenv)
    (bv_unsigned : T2 → Int)
    (c : T2)
    (w_stop : nwenv → Int)
    (w_TL : nwenv → Int)
    (w_n : nwenv → Int)
    (cur : Int)
    (numchar : Int → Bool)
    (h1 : (w_stop E) < (w_TL E))
    (h2 : ((w_n E) - 7) ≤ (8 * ((w_n E) / 8)))
    (h3 : (0 ≤ (bv_unsigned c) ∧ (bv_unsigned c) < 256))
    (h4 : (cur = (w_stop E) → (numchar (bv_unsigned c)) = false))
    (h5 : (numchar (bv_unsigned c)) = true)
    (h6 : cur ≠ (w_stop E))
    (h7 : (43 ≤ (bv_unsigned c) ∧ (bv_unsigned c) ≤ 101))
    (h8 : (¬ (48 ≤ (bv_unsigned c) ∧ (bv_unsigned c) ≤ 57)))
    (h9 : cur = (w_stop E)) :
    (¬ (48 ≤ (bv_unsigned c) ∧ (bv_unsigned c) ≤ 57)) := by
  lia

-- simdjson/fuzz_print_json: lib/B/F_memcmp.v (replace)
example
    {list_byte T2 : Type}
    (p : Int)
    (q : Int)
    (bp : list_byte)
    (bq : list_byte)
    (i : Int)
    (length : list_byte → Nat)
    (bv_unsigned : T2 → Int)
    (Z_to_bv : Int → Int → T2)
    (BP : Int → T2)
    (BQ : Int → T2)
    (h1 : (length bq) = (length bp))
    (h2 : 0 ≤ p)
    (h3 : 0 ≤ q)
    (h4 : (p + (((length bp) : Nat) : Int)) < (2 ^ (63 : Nat)))
    (h5 : (q + (((length bp) : Nat) : Int)) < (2 ^ (63 : Nat)))
    (h6 : (bv_unsigned (Z_to_bv 64 (p + i))) = (p + i))
    (h7 : (bv_unsigned (Z_to_bv 64 (q + i))) = (q + i))
    (h8 : (bv_unsigned (Z_to_bv 64 ((((length bp) : Nat) : Int) - i))) = ((((length bp) : Nat) : Int) - i))
    (h9 : (0 ≤ (bv_unsigned (BP i)) ∧ (bv_unsigned (BP i)) < 256))
    (h10 : (0 ≤ (bv_unsigned (BQ i)) ∧ (bv_unsigned (BQ i)) < 256))
    (h11 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned (BP i)) - (bv_unsigned (BQ i))))) = 0)
    (h12 : (bv_unsigned (Z_to_bv 64 (((((length bp) : Nat) : Int) - i) + (-1)))) = (((((length bp) : Nat) : Int) - i) + (-1))) :
    (p + (i + 1)) = ((p + i) + 1) := by
  lia

-- simdjson/fuzz_print_json: lib/B/Pj_dboxB.v (replace)
example {T1 : Type} (d_f : T1 → Int) (I : T1) :
    (((d_f I) / 8) + 2147450884) = ((((d_f I) / 8) + 2147450880) + ((4 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_print_json: lib/B/Pj_os_put3A.v (replace)
example
    {T1 : Type}
    (OS : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (f : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 f)) = f)
    (h2 : (bv_unsigned (Z_to_bv 64 (OS + 160))) = (OS + 160))
    (h3 : (bv_unsigned (Z_to_bv 64 ((f / 8) + 2147450880))) = ((f / 8) + 2147450880)) :
    (OS + 160) = ((OS + 136) + 24) := by
  lia

-- simdjson/fuzz_print_json: lib/B/Pj_os_xsputnA.v (replace)
example
    {T1 T2 : Type}
    (done : Int)
    (kz : Int)
    (lo : Int)
    (q : Int)
    (bv_unsigned : T1 → Int)
    (wz : Int → T1)
    (length : T2 → Nat)
    (bs : T2)
    (CAP : Int)
    (pp : Int)
    (ep : Int)
    (b : T1)
    (sub : T2)
    (h1 : lo ≤ (q - 64))
    (h2 : 0 ≤ (q - 64))
    (h3 : (bv_unsigned (wz q)) = q)
    (h4 : (bv_unsigned (wz (q + (-64)))) = (q + (-64)))
    (h5 : (length bs) = (Int.toNat CAP))
    (h6 : (((length bs) : Nat) : Int) = CAP)
    (h7 : ((0 ≤ pp ∧ pp < (2 ^ (62 : Nat))) ∧ (0 ≤ ep ∧ ep < (2 ^ (62 : Nat)))))
    (h8 : (0 ≤ (bv_unsigned b) ∧ (bv_unsigned b) < 256))
    (h9 : (((length sub) : Nat) : Int) = kz) :
    (done + kz) = (kz + done) := by
  lia

-- simdjson/fuzz_print_json: lib/B/Pj_ser_objA.v (replace)
example (b : Int) :
    240 = (Int.toNat ((b + 248) - (b + 8))) := by
  lia

-- simdjson/fuzz_print_json: lib/B/Sj_stage2_objb.v (replace)
example {T1 T2 : Type} (e_OC : T1 → Int) (E : T1) (depth : T2 → Int) (s : T2) :
    ((e_OC E) + (8 * ((depth s) + 1))) = ((e_OC E) + (4 * (2 * ((depth s) + 1)))) := by
  lia

-- simdjson/fuzz_print_json: lib/B/Sj_stage2_pro.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (h1 : (((bv_unsigned sp) % 32) = 0 ∨ ((bv_unsigned sp) % 32) = 16)) :
    ((bv_unsigned sp) + (-432)) = (((bv_unsigned sp) + (-416)) - 16) := by
  lia

-- simdjson/fuzz_print_json: lib/Sj/SjNumber.v (replace)
example (k : Int) (h1 : (0 ≤ k ∧ k < 8192)) :
    ((8 * k) * 281474976710656) = (k * 2251799813685248) := by
  lia

-- simdjson/fuzz_print_json: lib/Sj/SjNumber.v (replace)
example
    (s : Int)
    (d : Int)
    (n : Int)
    (h1 : (0 ≤ s ∧ s < d))
    (h2 : (d + n) ≤ 18446744073709551616)
    (h3 : (0 ≤ n ∧ n < 4611686018427387904))
    (h4 : ((s - (n + d)) % 18446744073709551616) ≤ ((-(2 * n)) % 18446744073709551616))
    (h5 : ((-(2 * n)) % 18446744073709551616) = (18446744073709551616 - (2 * n)))
    (h6 : ((s - (n + d)) % 18446744073709551616) = ((s - (n + d)) + 18446744073709551616)) :
    (((s - (n + d)) + 18446744073709551616) + ((-1) * 18446744073709551616)) = (s - (n + d)) := by
  lia

-- simdjson/fuzz_utf8: lib/AsanW/F_rip.v (replace)
example
    {word : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (lo : Int)
    (AB : Int)
    (AE : Int)
    (shad : Int → Int)
    (bv_unsigned : word → Int)
    (KHIGH : Int)
    (h1 : lo ≤ ((bv_unsigned sp) - 80))
    (h2 : KHIGH ≤ lo)
    (h3 : (bv_unsigned a1) ≤ (2 ^ (40 : Nat)))
    (h4 : (bv_unsigned a1) ≠ 0)
    (h5 : 0 ≤ lo)
    (h6 : (((bv_unsigned a0) ≤ AB ∧ AB ≤ ((bv_unsigned a0) + 7)) ∧ (AB % 8) = 0))
    (h7 : (((((bv_unsigned a0) + (bv_unsigned a1)) - 7) ≤ AE ∧ AE ≤ ((bv_unsigned a0) + (bv_unsigned a1))) ∧ (AE % 8) = 0))
    (h8 : (2147450880 ≤ (shad (bv_unsigned a0)) ∧ ((shad (bv_unsigned a0)) ≤ (shad AB) ∧ ((shad AB) ≤ ((shad (((bv_unsigned a0) + (bv_unsigned a1)) - 1)) + 1) ∧ (2147450880 ≤ (shad AE) ∧ ((shad AE) ≤ ((shad (((bv_unsigned a0) + (bv_unsigned a1)) - 1)) + 1) ∧ ((shad (((bv_unsigned a0) + (bv_unsigned a1)) - 1)) + 1) ≤ 17594333495296))))))
    (h9 : AB ≤ AE)
    (h10 : ((shad AE) - (shad AB)) ≤ (2 ^ (40 : Nat))) :
    (shad AE) = ((shad AB) + ((shad AE) - (shad AB))) := by
  lia

-- simdjson/fuzz_utf8: lib/BothW/AD_main_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (bs : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (DATA : T1)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (LEN : Int)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : ((1 ≤ CNT ∧ CNT ≤ 65536) ∧ CNT ≤ ((rd_cap st1) - (((length DATA) : Nat) : Int))))
    (h3 : LEN = (((length DATA) : Nat) : Int))
    (h4 : 0 ≤ LEN) :
    (length bs) = (Int.toNat (((length bs) : Nat) : Int)) := by
  lia

-- simdjson/fuzz_utf8: lib/BothW/AD_main_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (LEN : Int)
    (length : T1 → Nat)
    (bs : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (DATA : T1)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : ((1 ≤ CNT ∧ CNT ≤ 65536) ∧ CNT ≤ ((rd_cap st1) - (((length DATA) : Nat) : Int))))
    (h3 : LEN = (((length DATA) : Nat) : Int))
    (h4 : 0 ≤ LEN) :
    (LEN + (((length bs) : Nat) : Int)) = ((((length bs) : Nat) : Int) + LEN) := by
  lia

-- simdjson/fuzz_utf8: lib/BothW/AU_fuzz_A.v (replace)
example (SPA : Int) :
    (SPA + 32) = ((SPA + 80) - 48) := by
  lia

-- simdjson/fuzz_utf8: lib/BothW/F_printf_core_xloop.v (replace)
example
    {region list_Z T3 : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (rstk : region)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (j : Int)
    (zlength : list_Z → Int)
    (hex_digits : T3 → Int → list_Z)
    (l : T3)
    (x : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (KHIGH : Int)
    (r_lo : region → Int)
    (r_hi : region → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 1486848)
    (h5 : ((1523816 ≤ Fp ∧ (Fp + 232) ≤ 1552504) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((7142224 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : KHIGH ≤ lo)
    (h12 : ((r_lo rstk) ≤ lo ∧ q ≤ (r_hi rstk)))
    (h13 : (x / 16) < 1152921504606846976)
    (h14 : 1 ≤ (zlength (hex_digits l x)))
    (h15 : (zlength (hex_digits l x)) = ((zlength (hex_digits l (x / 16))) + 1)) :
    (Int.toNat (j - ((zlength (hex_digits l (x / 16))) + 1))) = (Int.toNat ((j - 1) - (zlength (hex_digits l (x / 16))))) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/AsanMainLib.v (replace)
example (b : Int) :
    (((b + 128) - 256) + (1 * 256)) = (b + 128) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/AsanMainLib.v (replace)
example (b : Int) (h1 : 128 ≤ b) :
    (((b - 256) + (2 ^ (64 : Nat))) + ((-1) * (2 ^ (64 : Nat)))) = (b - 256) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/AsanNodesArgSound.v (replace)
example
    {list_Segment atable argtab bv_32 T5 T6 T7 T8 word T10 : Type}
    (SEGS : list_Segment)
    (A : atable)
    (G : argtab)
    (wi0 : bv_32)
    (wi1 : bv_32)
    (wi2 : bv_32)
    (wi3 : bv_32)
    (wi4 : bv_32)
    (wi5 : bv_32)
    (wi6 : bv_32)
    (usp : Int)
    (STR0 : Int)
    (TOP : Int)
    (argc : Int)
    (E : T5)
    (M : T6)
    (allkn : T7)
    (k : T7)
    (b : T8)
    (off : Int)
    (n : Int)
    (bv_unsigned : word → Int)
    (edenot : T5 → T8 → word)
    (wb : T8)
    (wk : Int)
    (g_istrlen : argtab → Int)
    (Z_to_bv : Int → Int → word)
    (is_ecall : bv_32 → Bool)
    (L0 : Int)
    (STR1 : Int)
    (L1 : Int)
    (img_lo : atable → Int)
    (g_ro_lo : argtab → Int)
    (g_ro_hi : argtab → Int)
    (img_hi : atable → Int)
    (kwritable : T7 → T7 → T8 → Int → Int → Bool)
    (elenZ : T5 → T10 → Int)
    (wn : T10)
    (store_ok : list_Segment → T6 → word → Nat → Bool)
    (h1 : (0 ≤ (g_istrlen G) ∧ ((g_istrlen G) + 28) < (2 ^ (64 : Nat))))
    (h2 : ((is_ecall wi0) = false ∧ ((is_ecall wi1) = false ∧ ((is_ecall wi2) = false ∧ ((is_ecall wi3) = false ∧ ((is_ecall wi4) = false ∧ ((is_ecall wi5) = false ∧ (is_ecall wi6) = false)))))))
    (h3 : (140735340871680 ≤ usp ∧ ((usp + 176) ≤ STR0 ∧ (((STR0 + L0) + 1) ≤ TOP ∧ ((2 ≤ argc → ((STR1 + L1) + 1) ≤ TOP) ∧ ((TOP % 8) = 0 ∧ ((TOP + 16) ≤ (2 ^ (47 : Nat)) ∧ (L0 ≤ 131071 ∧ (L1 ≤ 131071 ∧ (1 ≤ argc ∧ argc ≤ 1024))))))))))
    (h4 : ((img_lo A) ≤ (g_ro_lo G) ∧ (g_ro_hi G) ≤ (img_hi A)))
    (h5 : (kwritable allkn k b off n) = true)
    (h6 : 0 ≤ n)
    (h7 : (((bv_unsigned (edenot E wb)) + wk) ≤ ((bv_unsigned (edenot E b)) + off) → ((((bv_unsigned (edenot E b)) + off) + n) ≤ (((bv_unsigned (edenot E wb)) + wk) + (elenZ E wn)) → ((store_ok SEGS M (Z_to_bv 64 ((bv_unsigned (edenot E b)) + off)) (Int.toNat n)) = true ∧ (0 ≤ ((bv_unsigned (edenot E b)) + off) ∧ (((bv_unsigned (edenot E b)) + off) + n) ≤ (2 ^ (64 : Nat))))))) :
    (((bv_unsigned (edenot E wb)) + wk) + (((bv_unsigned (edenot E b)) + off) - ((bv_unsigned (edenot E wb)) + wk))) = ((bv_unsigned (edenot E b)) + off) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/AsanNodesArgSound.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 : Type}
    (bv_unsigned : T1 → Int)
    (a : T1)
    (d : Int)
    (LEN : T2 → Int)
    (i : T2)
    (elenZ : T3 → T4 → Int)
    (E : T3)
    (len_e : T2 → T4)
    (edenot : T3 → T5 → T1)
    (reg : T6 → Int → T5)
    (cs : T6)
    (estart : T3 → T7 → Int)
    (SA : T8 → T9 → T7)
    (db : T8)
    (dk : T9)
    (Z_to_bv : Int → Int → T1)
    (M2 : T10)
    (length : T11 → Nat)
    (ARG : T2 → T11)
    (SEGS : T12)
    (store_ok : T12 → T10 → T1 → Nat → Bool)
    (hid : T13 → T14 → T3 → T6 → T15 → T1 → Bool)
    (A : T13)
    (argH : T14)
    (model : T15)
    (x : T1)
    (H2 : T1 → Bool)
    (h1 : 0 ≤ (LEN i))
    (h2 : (elenZ E (len_e i)) = (LEN i))
    (h3 : (bv_unsigned (edenot E (reg cs 10))) = (estart E (SA db dk)))
    (h4 : (store_ok SEGS M2 (Z_to_bv 64 d) (length (ARG i))) = true)
    (h5 : (H2 x) = false)
    (h6 : (hid A argH E cs model x) = false)
    (h7 : ((bv_unsigned a) < d ∨ (d + (((length (ARG i)) : Nat) : Int)) ≤ (bv_unsigned a))) :
    (bv_unsigned a) = (d + ((bv_unsigned a) - d)) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/AsanPlanSound.v (replace)
example
    {T1 T2 T3 T4 word T6 T7 : Type}
    (E : T1)
    (k : T2)
    (b : T3)
    (o : Int)
    (n : T4)
    (bv_unsigned : word → Int)
    (edenot : T1 → T3 → word)
    (wb : T3)
    (wk : Int)
    (d : Int)
    (kflat_h : T2 → T6 → Bool)
    (KWr : T7 → T4 → T6)
    (SA : T3 → Int → T7)
    (kwritable_x : T2 → T2 → T3 → Int → T4 → Bool)
    (h1 : (kflat_h k (KWr (SA b o) n)) = true)
    (h2 : (kwritable_x k k b o n) = true) :
    (((bv_unsigned (edenot E wb)) + wk) + ((((bv_unsigned (edenot E b)) + o) + d) - ((bv_unsigned (edenot E wb)) + wk))) = (((bv_unsigned (edenot E b)) + o) + d) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/AxSymExec3B.v (replace)
example (lo : Int) :
    1 = (Int.toNat ((lo - lo) + 1)) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/AxSymExec3Sound.v (replace)
example (v : Int) (P : Int) (r : Int) (q : Int) (h1 : 0 ≤ v) (h2 : 0 < P) :
    ((P - r) + (((-q) - 1) * P)) = (-((P * q) + r)) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/AxSymExec3Sound.v (replace)
example
    {T1 : Type}
    (n : Nat)
    (bs : T1)
    (z : Int)
    (M : Int)
    (q : Int)
    (length : T1 → Nat)
    (Zpow : Int → Int → Int)
    (h1 : (length bs) = n)
    (h2 : 1 ≤ n)
    (h3 : n ≤ 8)
    (h4 : (Zpow 2 (8 * ((n : Nat) : Int))) ≤ (2 ^ (64 : Nat)))
    (h5 : 0 < (Zpow 2 (8 * ((n : Nat) : Int)))) :
    ((Int.fmod z M) + (q * M)) = ((Int.fmod z M) + (M * q)) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/MallocNodes2Sound.v (replace)
example
    {T1 T2 : Type}
    (w_maplen : T1 → Int)
    (W : T1)
    (stl : T2)
    (shi : Int)
    (MN2_sbound : T2 → Int → Int)
    (Shi : Int)
    (slo : Int)
    (Slo : Int)
    (Sm : Int)
    (slot_stride : Int → Int → Int → Int)
    (st : Int)
    (w_lastidx : T1 → Int)
    (w_sizeclass : T1 → Int)
    (h1 : shi = (MN2_sbound stl Shi))
    (h2 : slo = (MN2_sbound stl Slo))
    (h3 : (Slo ≤ Sm ∧ Sm ≤ Shi))
    (h4 : ((slo ≤ st ∧ st ≤ shi) ∧ (16 ≤ st ∧ st < (2 ^ (31 : Nat)))))
    (h5 : st = (slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)))
    (h6 : (((w_maplen W) = 0 ∨ (w_lastidx W) ≠ 0) → (w_sizeclass W) < 48))
    (h7 : (st % 16) = 0) :
    ((((w_maplen W) * 256) - 1) * 16) = (((w_maplen W) * 4096) - 16) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/MallocNodes2Sound.v (replace)
example
    {T1 T2 : Type}
    (Sm : Int)
    (stl : T1)
    (si : Int)
    (MN2_si_of : T1 → Int → Int)
    (idx : Int)
    (shi : Int)
    (MN2_sbound : T1 → Int → Int)
    (Shi : Int)
    (slo : Int)
    (Slo : Int)
    (slot_stride : Int → Int → Int → Int)
    (st : Int)
    (w_maplen : T2 → Int)
    (W : T2)
    (w_lastidx : T2 → Int)
    (w_sizeclass : T2 → Int)
    (h1 : si = (MN2_si_of stl idx))
    (h2 : shi = (MN2_sbound stl Shi))
    (h3 : slo = (MN2_sbound stl Slo))
    (h4 : (Slo ≤ Sm ∧ Sm ≤ Shi))
    (h5 : ((slo ≤ st ∧ st ≤ shi) ∧ (16 ≤ st ∧ st < (2 ^ (31 : Nat)))))
    (h6 : st = (slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)))
    (h7 : (((w_maplen W) = 0 ∨ (w_lastidx W) ≠ 0) → (w_sizeclass W) < 48))
    (h8 : (st % 16) = 0)
    (h9 : (si = (st * idx) ∧ (0 ≤ si ∧ (si % 16) = 0)))
    (h10 : si = (st * idx)) :
    (((4096 * Sm) - 16) + (1 * (2 ^ (64 : Nat)))) = ((4096 * Sm) + ((2 ^ (64 : Nat)) - 16)) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/MallocNodes2Sound.v (replace)
example
    {T1 T2 : Type}
    (st : Int)
    (stl : T1)
    (si : Int)
    (MN2_si_of : T1 → Int → Int)
    (idx : Int)
    (shi : Int)
    (MN2_sbound : T1 → Int → Int)
    (Shi : Int)
    (slo : Int)
    (Slo : Int)
    (Sm : Int)
    (slot_stride : Int → Int → Int → Int)
    (w_maplen : T2 → Int)
    (W : T2)
    (w_lastidx : T2 → Int)
    (w_sizeclass : T2 → Int)
    (h1 : si = (MN2_si_of stl idx))
    (h2 : shi = (MN2_sbound stl Shi))
    (h3 : slo = (MN2_sbound stl Slo))
    (h4 : (Slo ≤ Sm ∧ Sm ≤ Shi))
    (h5 : ((slo ≤ st ∧ st ≤ shi) ∧ (16 ≤ st ∧ st < (2 ^ (31 : Nat)))))
    (h6 : st = (slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)))
    (h7 : (((w_maplen W) = 0 ∨ (w_lastidx W) ≠ 0) → (w_sizeclass W) < 48))
    (h8 : (st % 16) = 0)
    (h9 : (si = (st * idx) ∧ (0 ≤ si ∧ (si % 16) = 0)))
    (h10 : si = (st * idx)) :
    ((st - 1) + (1 * (2 ^ (64 : Nat)))) = (st + ((2 ^ (64 : Nat)) - 1)) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/SlotProp.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (E : T1)
    (us : Int)
    (bv_unsigned : T2 → Int)
    (edenot : T1 → T3 → T2)
    (sd : T3)
    (idx : T3)
    (alu64 : T4 → T2 → T2 → T2)
    (ALU_ADD : T4)
    (start : T3)
    (ELit : Int → T3)
    (h1 : 0 ≤ ((bv_unsigned (edenot E sd)) * (bv_unsigned (edenot E idx))))
    (h2 : (bv_unsigned (alu64 ALU_ADD (edenot E start) (edenot E (ELit (-4))))) = (us - 4)) :
    ((us - 4) + (1 * (2 ^ (64 : Nat)))) = (us + ((2 ^ (64 : Nat)) - 4)) := by
  lia

-- simdjson/fuzz_utf8: lib/Common/Stage1Ghost.v (replace)
example
    {T1 T2 : Type}
    (E : T1)
    (buf : Int)
    (len : Int)
    (e : T2)
    (m : Int)
    (j : Int)
    (two64 : Int)
    (xt_den : T1 → T2 → Int)
    (h1 : 0 ≤ buf)
    (h2 : ((buf + len) + 64) < two64)
    (h3 : 0 ≤ len)
    (h4 : (xt_den E e) = (buf + len))
    (h5 : (len ≤ j ∧ j < (len + m)))
    (h6 : j < (len + 64)) :
    (buf + j) = (buf + (((Int.toNat j) : Nat) : Int)) := by
  lia

-- skcms/iccprofile_info: lib/AsLib/AsSymExecSound.v (replace)
example
    {T1 T2 T3 : Type}
    (estart : T1 → T2 → Int)
    (E : T1)
    (SA : T3 → Int → T2)
    (kb : T3)
    (kk : Int)
    (d : Int)
    (j : Nat)
    (rb : T3)
    (rk : Int)
    (h1 : (estart E (SA rb rk)) = ((estart E (SA rb kk)) + (rk - kk)))
    (h2 : d = ((estart E (SA rb rk)) - (estart E (SA kb kk)))) :
    ((estart E (SA kb kk)) + (d + ((j : Nat) : Int))) = ((estart E (SA rb rk)) + ((j : Nat) : Int)) := by
  lia

-- skcms/iccprofile_info: lib/AsLib/BoLibGetTag.v (replace)
example
    {word list_byte T3 T4 : Type}
    (ceil : Int)
    (sp : word)
    (P : word)
    (T : word)
    (tc : Int)
    (sig : Int)
    (len : Int)
    (bs : list_byte)
    (i : Int)
    (bv_unsigned : word → Int)
    (Z_to_bv : Nat → Int → word)
    (length : list_byte → Nat)
    (store_ok : T3 → T4 → word → Nat → Bool)
    (SEGS : T3)
    (mem : T4)
    (AS_STKLO : Int)
    (h1 : (0 ≤ sig ∧ sig < (2 ^ (32 : Nat))))
    (h2 : (0 ≤ len ∧ len < (2 ^ (26 : Nat))))
    (h3 : (((length bs) : Nat) : Int) = len)
    (h4 : (0 ≤ tc ∧ tc < (2 ^ (32 : Nat))))
    (h5 : ((bv_unsigned P) % 8) = 0)
    (h6 : ((bv_unsigned T) % 8) = 0)
    (h7 : (ceil ≤ (bv_unsigned T) ∧ ((bv_unsigned T) + 24) ≤ (2 ^ (47 : Nat))))
    (h8 : (store_ok SEGS mem (Z_to_bv 64 (bv_unsigned T)) (Int.toNat 24)) = true)
    (h9 : (((bv_unsigned T) + 24) ≤ ((bv_unsigned sp) - 16) ∨ (bv_unsigned sp) ≤ (bv_unsigned T)))
    (h10 : ((AS_STKLO ≤ ceil ∧ (ceil + 16) ≤ (bv_unsigned sp)) ∧ (bv_unsigned sp) ≤ (2 ^ (47 : Nat))))
    (h11 : (0 ≤ i ∧ i < tc)) :
    ((bv_unsigned sp) - 8) = (((bv_unsigned sp) - 16) + 8) := by
  lia

-- skcms/iccprofile_info: lib/AsLib/BoLibParseC2.v (replace)
example
    {word : Type}
    (P : word)
    (c : Int)
    (sz : Int)
    (bv_unsigned : word → Int)
    (h1 : (0 ≤ sz ∧ sz < (2 ^ (32 : Nat))))
    (h2 : (c = ((bv_unsigned P) + 24) ∨ (c = ((bv_unsigned P) + 56) ∨ c = ((bv_unsigned P) + 88))))
    (h3 : (c % 8) = 0) :
    ((bv_unsigned P) + (c - (bv_unsigned P))) = c := by
  lia

-- skcms/iccprofile_info: lib/AsLib/BoLibReadCurveC.v (replace)
example
    {word : Type}
    (ceil : Int)
    (data : word)
    (len : Int)
    (sp : word)
    (C : word)
    (size : Int)
    (sp1 : word)
    (X : word)
    (RAW : word)
    (vc : Int)
    (bv_unsigned : word → Int)
    (AS_STKLO : Int)
    (h1 : (0 ≤ size ∧ size < (2 ^ (32 : Nat))))
    (h2 : ((bv_unsigned C) % 8) = 0)
    (h3 : ((AS_STKLO ≤ ceil ∧ (ceil + 2208) ≤ (bv_unsigned sp)) ∧ (bv_unsigned sp) ≤ (2 ^ (47 : Nat))))
    (h4 : ((bv_unsigned sp) % 16) = 0)
    (h5 : (((bv_unsigned data) + len) ≤ (bv_unsigned C) ∨ ((bv_unsigned C) + 32) ≤ (bv_unsigned data)))
    (h6 : (bv_unsigned sp1) = ((bv_unsigned sp) - 80))
    (h7 : (Int.fmod (bv_unsigned X) (2 ^ (32 : Nat))) = vc)
    (h8 : ((bv_unsigned RAW) = 0 ↔ vc = 0))
    (h9 : (12 + (2 * vc)) ≤ size)
    (h10 : 0 ≤ vc) :
    ((bv_unsigned sp) - 64) = ((bv_unsigned sp1) + 16) := by
  lia

-- skcms/iccprofile_info: lib/Asan/AsanNodesFactSoundCfg.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (E : T1)
    (k : T2)
    (bb : T3)
    (bk : Int)
    (N_1 : T4)
    (K : T5)
    (bv_unsigned : T6 → Int)
    (edenot : T1 → T3 → T6)
    (zb : T3)
    (zk : Int)
    (i : Int)
    (zone_covers_sym : T2 → T3 → Int → T4 → T5 → Bool)
    (h1 : (zone_covers_sym k bb bk N_1 K) = true) :
    (((bv_unsigned (edenot E zb)) + zk) + ((((bv_unsigned (edenot E bb)) + bk) + i) - ((bv_unsigned (edenot E zb)) + zk))) = (((bv_unsigned (edenot E bb)) + bk) + i) := by
  lia

-- skcms/iccprofile_info: lib/Asan/AsanNodesRPSoundCfg.v (replace)
example
    {list_Segment T2 T3 T4 T5 T6 word : Type}
    (SEGS : list_Segment)
    (E : T2)
    (k : T3)
    (begE : T4)
    (enE : T4)
    (words : T5)
    (kmax : T6)
    (bz : Int)
    (ez : Int)
    (RPN_SB : Int)
    (q : Int)
    (n : Int)
    (bv_unsigned : word → Int)
    (RPN_sh_alloc : list_Segment → T3 → T4 → T4 → T5 → T6 → Bool)
    (edenot : T2 → T4 → word)
    (nE : T4)
    (Hs : Int)
    (P : Int)
    (h1 : (RPN_sh_alloc SEGS k begE enE words kmax) = true)
    (h2 : (bv_unsigned (edenot E begE)) = bz)
    (h3 : (bv_unsigned (edenot E enE)) = ez)
    (h4 : (bv_unsigned (edenot E nE)) = n)
    (h5 : (bz / 8) = q)
    (h6 : (0 ≤ (n / 8) ∧ (n / 8) ≤ n))
    (h7 : Hs = (RPN_SB + q))
    (h8 : ((ez - 1) / 8) = (q + ((n - 1) / 8)))
    (h9 : P = ((RPN_SB + q) + (n / 8)))
    (h10 : ((n - 1) / 8) = ((n / 8) - 1))
    (h11 : ((n - 1) / 8) = (n / 8)) :
    ((RPN_SB + q) + (n / 8)) = (RPN_SB + (q + (n / 8))) := by
  lia

-- skcms/iccprofile_info: lib/Asan/AsanNodesRPSoundCfg.v (replace)
example
    {list_Segment T2 T3 T4 T5 T6 T7 word : Type}
    (SEGS : list_Segment)
    (E : T2)
    (k : T3)
    (begE : T4)
    (enE : T4)
    (words : T5)
    (kmax : T6)
    (bz : Int)
    (ez : Int)
    (ealign : T3 → T7 → Int)
    (lb : T7)
    (bv_unsigned : word → Int)
    (RPN_sh_alloc : list_Segment → T3 → T4 → T4 → T5 → T6 → Bool)
    (edenot : T2 → T4 → word)
    (nE : T4)
    (n : Int)
    (q : Int)
    (Hs : Int)
    (RPN_SB : Int)
    (P : Int)
    (h1 : (RPN_sh_alloc SEGS k begE enE words kmax) = true)
    (h2 : (bv_unsigned (edenot E begE)) = bz)
    (h3 : (bv_unsigned (edenot E enE)) = ez)
    (h4 : (bv_unsigned (edenot E nE)) = n)
    (h5 : (bz / 8) = q)
    (h6 : (0 ≤ (n / 8) ∧ (n / 8) ≤ n))
    (h7 : Hs = (RPN_SB + q))
    (h8 : ((ez - 1) / 8) = (q + ((n - 1) / 8)))
    (h9 : P = ((RPN_SB + q) + (n / 8)))
    (h10 : ((n - 1) / 8) = ((n / 8) - 1))
    (h11 : ((n - 1) / 8) = (n / 8))
    (h12 : ((ez - 1) % 8) = ((n % 8) - 1)) :
    (((ealign k lb) - 3) + 3) = (ealign k lb) := by
  lia

-- skcms/iccprofile_info: lib/Asan/AsanNodesRPSoundCfg.v (replace)
example
    {T1 word : Type}
    (nxt : T1 → Nat)
    (cs : T1)
    (bv_unsigned : word → Int)
    (beg : Int)
    (en : Int)
    (bv_signed : word → Int)
    (kb : word)
    (h1 : (beg / 8) ≤ ((en - 1) / 8))
    (h2 : (bv_signed kb) = (bv_unsigned kb))
    (h3 : ((bv_signed kb) = 0 ∨ ((en - 1) % 8) < (bv_signed kb))) :
    ((((nxt cs) + 1) + 1) + 1) = ((nxt cs) + 3) := by
  lia

-- skcms/iccprofile_info: lib/Asan/DepotPut.v (replace)
example
    {word T2 T3 T4 T5 : Type}
    (sp : Int)
    (tr : Int)
    (s : Int)
    (b17 : Int)
    (N_1 : Int)
    (h_1 : word)
    (v : Int)
    (Z_to_bv : Int → Int → word)
    (ACEILZ : Int)
    (store_ok : T2 → T3 → word → Int → Bool)
    (ASEGS : T2)
    (M : T3)
    (bv_unsigned : word → Int)
    (bkt : word → Int)
    (bh : Int)
    (D : Int)
    (edenot : T4 → T5 → word)
    (E : T4)
    (ELit : Int → T5)
    (h1 : (sp % 16) = 0)
    (h2 : ACEILZ ≤ (sp - 272))
    (h3 : sp ≤ (2 ^ (47 : Nat)))
    (h4 : (tr % 8) = 0)
    (h5 : ACEILZ ≤ tr)
    (h6 : (tr + 16) ≤ (2 ^ (47 : Nat)))
    (h7 : (s = 1 ∨ s = 2))
    (h8 : (store_ok ASEGS M (Z_to_bv 64 (sp - 272)) 272) = true)
    (h9 : (store_ok ASEGS M (Z_to_bv 64 tr) 16) = true)
    (h10 : ((tr + 16) ≤ (sp - 272) ∨ sp ≤ tr))
    (h11 : (0 ≤ v ∧ v ≤ N_1))
    (h12 : (bkt h_1) = ((4 * bh) + D))
    (h13 : (0 ≤ bh ∧ bh < (2 ^ (20 : Nat))))
    (h14 : (bv_unsigned (edenot E (ELit 0))) = 0) :
    ((b17 + (16 * (N_1 + 1))) + 8) = ((b17 + (16 * N_1)) + 24) := by
  lia

-- skcms/iccprofile_info: lib/Asan/DepotPut.v (replace)
example
    {word T2 T3 T4 T5 : Type}
    (sp : Int)
    (tr : Int)
    (s : Int)
    (b17 : Int)
    (b18 : Int)
    (N_1 : Int)
    (T : Int)
    (h_1 : word)
    (v : Int)
    (Z_to_bv : Int → Int → word)
    (ACEILZ : Int)
    (store_ok : T2 → T3 → word → Int → Bool)
    (ASEGS : T2)
    (M : T3)
    (bv_unsigned : word → Int)
    (bkt : word → Int)
    (bh : Int)
    (D : Int)
    (edenot : T4 → T5 → word)
    (E : T4)
    (ELit : Int → T5)
    (h1 : (sp % 16) = 0)
    (h2 : ACEILZ ≤ (sp - 272))
    (h3 : sp ≤ (2 ^ (47 : Nat)))
    (h4 : (tr % 8) = 0)
    (h5 : ACEILZ ≤ tr)
    (h6 : (tr + 16) ≤ (2 ^ (47 : Nat)))
    (h7 : (s = 1 ∨ s = 2))
    (h8 : (store_ok ASEGS M (Z_to_bv 64 (sp - 272)) 272) = true)
    (h9 : (store_ok ASEGS M (Z_to_bv 64 tr) 16) = true)
    (h10 : ((tr + 16) ≤ (sp - 272) ∨ sp ≤ tr))
    (h11 : (0 ≤ v ∧ v ≤ N_1))
    (h12 : (bkt h_1) = ((4 * bh) + D))
    (h13 : (0 ≤ bh ∧ bh < (2 ^ (20 : Nat))))
    (h14 : (bv_unsigned (edenot E (ELit 0))) = 0)
    (h15 : (0 ≤ (b17 + (16 * N_1)) ∧ (b17 + (16 * N_1)) < (2 ^ (64 : Nat))))
    (h16 : (0 ≤ (b18 + (8 * T)) ∧ (b18 + (8 * T)) < (2 ^ (64 : Nat)))) :
    (T + (s + 1)) = ((T + s) + 1) := by
  lia

-- skcms/iccprofile_info: lib/Info/FpuFacts.v (replace)
example
    {T1 : Type}
    (m : T1)
    (e : Int)
    (SpecFloat_bounded : Int → Int → T1 → Int → Bool)
    (Zpos : T1 → Int)
    (digits2_pos : T1 → T1)
    (h1 : (SpecFloat_bounded 24 128 m e) = true)
    (h2 : e = (-149))
    (h3 : (Zpos m) < (2 ^ (23 : Nat)))
    (h4 : (Zpos (digits2_pos m)) = 24)
    (h5 : ((2 ^ (23 : Nat)) ≤ (Zpos m) ∧ (Zpos m) < (2 ^ (24 : Nat))))
    (h6 : ((-149) ≤ e ∧ e ≤ 104)) :
    e = ((e + 150) - 150) := by
  lia

-- skcms/iccprofile_info: lib/Info/FpuFacts.v (assert)
example
    {T1 T2 : Type}
    (es : Int)
    (D : Int)
    (radix2 : T1)
    (M1 : T2)
    (Zdigits : T1 → Int → Int)
    (e1 : Int)
    (n1 : Int)
    (q : Int)
    (Z_pos : T2 → Int)
    (Zpow : Int → Int → Int)
    (q' : Int)
    (K : Int)
    (h1 : D ≤ 127)
    (h2 : es = (max (D - 24) (-149)))
    (h3 : e1 = es)
    (h4 : 0 ≤ n1)
    (h5 : q < (2 ^ (24 : Nat)))
    (h6 : (Zdigits radix2 (Z_pos M1)) ≤ (24 + n1))
    (h7 : (Z_pos M1) < (Zpow 2 (24 + n1)))
    (h8 : (es = (D - 24) → (2 ^ (23 : Nat)) ≤ q))
    (h9 : ((Zdigits radix2 (Z_pos M1)) - 1) = (23 + n1))
    (h10 : q < K)
    (h11 : K < (q + 1))
    (h12 : (0 ≤ q' ∧ q' < (2 ^ (24 : Nat)))) :
    es = (-149) := by
  lia

-- skcms/iccprofile_info: lib/Info/FpuFacts.v (replace)
example (ea : Int) (eb : Int) :
    ea = ((min ea eb) + (ea - (min ea eb))) := by
  lia

-- skcms/iccprofile_info: lib/Info/LibEvalCurveS1W.v (replace)
example
    {word list_byte : Type}
    (c : word)
    (data : word)
    (t8 : word)
    (t16 : word)
    (n : Int)
    (len : Int)
    (bs : list_byte)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : ((bv_unsigned c) + 24) ≤ (2 ^ (64 : Nat)))
    (h2 : (0 ≤ len ∧ len < (2 ^ (26 : Nat))))
    (h3 : (((length bs) : Nat) : Int) = len)
    (h4 : ((bv_unsigned data) + len) < (2 ^ (64 : Nat)))
    (h5 : (2 ≤ n ∧ n ≤ (2 ^ (24 : Nat))))
    (h6 : ((bv_unsigned t8) ≠ 0 → ((bv_unsigned data) ≤ (bv_unsigned t8) ∧ ((bv_unsigned t8) + n) ≤ ((bv_unsigned data) + len))))
    (h7 : ((bv_unsigned t16) ≠ 0 → ((bv_unsigned data) ≤ (bv_unsigned t16) ∧ ((bv_unsigned t16) + (2 * n)) ≤ ((bv_unsigned data) + len))))
    (h8 : ((bv_unsigned t8) ≠ 0 ∨ (bv_unsigned t16) ≠ 0)) :
    ((n - 1) + (1 * (2 ^ (64 : Nat)))) = (n + ((2 ^ (64 : Nat)) - 1)) := by
  lia

-- skcms/iccprofile_info: lib/Info/LibReadA2BUbh.v (replace)
example
    {word : Type}
    (A : word)
    (ic : Int)
    (c : Nat)
    (bv_unsigned : word → Int)
    (i : Int)
    (h1 : ((c : Nat) : Int) = ic) :
    (((bv_unsigned A) + 148) + i) = ((bv_unsigned A) + (148 + i)) := by
  lia

-- skcms/iccprofile_info: lib/Info/LibReadCurveS1.v (replace)
example
    {word : Type}
    (data : word)
    (len : Int)
    (sp : word)
    (C : word)
    (size : Int)
    (bv_unsigned : word → Int)
    (h1 : (0 ≤ size ∧ size < (2 ^ (32 : Nat))))
    (h2 : ((bv_unsigned C) % 8) = 0)
    (h3 : ((bv_unsigned sp) % 16) = 0)
    (h4 : (((bv_unsigned data) + len) ≤ (bv_unsigned C) ∨ ((bv_unsigned C) + 32) ≤ (bv_unsigned data)))
    (h5 : ((bv_unsigned sp) ≤ (bv_unsigned C) ∨ ((bv_unsigned C) + 32) ≤ ((bv_unsigned sp) - 64)))
    (h6 : (((bv_unsigned data) + len) ≤ ((bv_unsigned sp) - 64) ∨ (bv_unsigned sp) ≤ (bv_unsigned data))) :
    ((bv_unsigned sp) - 64) = ((bv_unsigned sp) + (-64)) := by
  lia

-- skcms/iccprofile_info: lib/Info/RefEnframe.v (replace)
example (n : Int) (stride : Int) :
    ((stride - 4) - n) = ((stride - n) + (-4)) := by
  lia

-- skcms/iccprofile_info: lib/Info/RefReadBig.v (replace)
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
    (h1 : 33554432 ≤ L)
    (h2 : 335872 ≤ (bv_unsigned mb))
    (h3 : ((bv_unsigned mb) + 8192) ≤ 140735332483072)
    (h4 : ((bv_unsigned mb) % 4096) = 0)
    (h5 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ 140737488355328))
    (h6 : (length vals) = 41)
    (h7 : ((bv_unsigned B) + 33558528) ≤ ((bv_unsigned sp0) - 8388608))
    (h8 : (length (pref 16777216 (dropz 16777216 content))) = (Int.toNat 16777216))
    (h9 : 335872 ≤ (bv_unsigned B'))
    (h10 : (((bv_unsigned B') + 67112960) ≤ (bv_unsigned B) ∨ ((bv_unsigned B) + 33558528) ≤ (bv_unsigned B')))
    (h11 : (((bv_unsigned B') + 67112960) ≤ ((bv_unsigned mb) + 4096) ∨ ((bv_unsigned mb) + 8192) ≤ (bv_unsigned B'))) :
    ((bv_unsigned B') + 13) = (((bv_unsigned B') + 16) - 3) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X015.v (replace)
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
    (j : Int)
    (zlength : list_Z → Int)
    (W' : list_Z)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (x : Int)
    (dec_digits : Int → list_Z)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 1011712)
    (h5 : ((1049936 ≤ Fp ∧ (Fp + 232) ≤ 1061376) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6655200 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 6664192)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (x / 10) < 1844674407370955162)
    (h12 : 2 ≤ (zlength (dec_digits x))) :
    (Int.toNat (j - ((zlength W') + 1))) = (Int.toNat ((j - 1) - (zlength W'))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X06m.v (assert)
example
    {bits_st_ptr list_word : Type}
    (A : Int)
    (D : Int)
    (STEREO : Int)
    (usp : Int)
    (lo : Int)
    (b : bits_st_ptr)
    (sws : list_word)
    (uv : bits_st_ptr → Int → Int)
    (ub : bits_st_ptr → Int → bits_st_ptr)
    (IMG_TOP_B : Int)
    (BITS_SIZEOF : Int)
    (sb_buf_size : bits_st_ptr → Int)
    (STEREOH_DEPTH : Int)
    (SH_HI : Int)
    (length : list_word → Nat)
    (bs0 : list_word)
    (bs1 : list_word)
    (bs2 : list_word)
    (bs3 : list_word)
    (h1 : (STEREO % 4) = 0)
    (h2 : IMG_TOP_B ≤ A)
    (h3 : IMG_TOP_B ≤ STEREO)
    (h4 : (A + BITS_SIZEOF) ≤ lo)
    (h5 : (D + (sb_buf_size b)) ≤ lo)
    (h6 : (STEREO + 8) ≤ lo)
    (h7 : lo ≤ (usp - STEREOH_DEPTH))
    (h8 : SH_HI ≤ lo)
    (h9 : usp < (2 ^ (63 : Nat)))
    (h10 : (length sws) = 2)
    (h11 : (((length bs0) : Nat) : Int) = (sb_buf_size b))
    (h12 : (((length bs1) : Nat) : Int) = (sb_buf_size b))
    (h13 : (((length bs2) : Nat) : Int) = (sb_buf_size b))
    (h14 : ((uv b 1) = 0 ∨ (uv b 1) = 1))
    (h15 : (((length bs3) : Nat) : Int) = (sb_buf_size b))
    (h16 : ((145248 % 8) : Int) = 0)
    (h17 : ((uv (ub (ub b 1) 5) 2) = 0 ∨ ((uv (ub (ub b 1) 5) 2) = 1 ∨ ((uv (ub (ub b 1) 5) 2) = 2 ∨ (uv (ub (ub b 1) 5) 2) = 3)))) :
    ((uv (ub (ub b 1) 5) 2) = 0 ∨ ((uv (ub (ub b 1) 5) 2) = 1 ∨ ((uv (ub (ub b 1) 5) 2) = 2 ∨ (uv (ub (ub b 1) 5) 2) = 3))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X06m.v (assert)
example
    {bits_st_ptr list_word : Type}
    (A : Int)
    (D : Int)
    (STEREO : Int)
    (usp : Int)
    (lo : Int)
    (b : bits_st_ptr)
    (sws : list_word)
    (uv : bits_st_ptr → Int → Int)
    (ub : bits_st_ptr → Int → bits_st_ptr)
    (IMG_TOP : Int)
    (BITS_SIZEOF : Int)
    (sb_buf_size : bits_st_ptr → Int)
    (STEREOH_DEPTH : Int)
    (SH_HI : Int)
    (length : list_word → Nat)
    (bs0 : list_word)
    (bs1 : list_word)
    (bs2 : list_word)
    (bs3 : list_word)
    (h1 : (STEREO % 4) = 0)
    (h2 : IMG_TOP ≤ A)
    (h3 : IMG_TOP ≤ STEREO)
    (h4 : (A + BITS_SIZEOF) ≤ lo)
    (h5 : (D + (sb_buf_size b)) ≤ lo)
    (h6 : (STEREO + 8) ≤ lo)
    (h7 : lo ≤ (usp - STEREOH_DEPTH))
    (h8 : SH_HI ≤ lo)
    (h9 : usp < (2 ^ (63 : Nat)))
    (h10 : (length sws) = 2)
    (h11 : (((length bs0) : Nat) : Int) = (sb_buf_size b))
    (h12 : (((length bs1) : Nat) : Int) = (sb_buf_size b))
    (h13 : ((uv b 1) = 0 ∨ (uv b 1) = 1))
    (h14 : (((length bs2) : Nat) : Int) = (sb_buf_size b))
    (h15 : (((length bs3) : Nat) : Int) = (sb_buf_size b))
    (h16 : ((145184 % 8) : Int) = 0)
    (h17 : ((uv (ub (ub b 1) 5) 2) = 0 ∨ ((uv (ub (ub b 1) 5) 2) = 1 ∨ ((uv (ub (ub b 1) 5) 2) = 2 ∨ (uv (ub (ub b 1) 5) 2) = 3)))) :
    ((uv (ub (ub b 1) 5) 2) = 0 ∨ ((uv (ub (ub b 1) 5) 2) = 1 ∨ ((uv (ub (ub b 1) 5) 2) = 2 ∨ (uv (ub (ub b 1) 5) 2) = 3))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X06p.v (replace)
example
    {hinv T2 T3 T4 T5 : Type}
    (X : hinv)
    (D' : Int)
    (sy_fill : T2 → Int)
    (h_oy : T3 → T2)
    (h_1 : T3)
    (sy_returned : T2 → Int)
    (i : Int)
    (x_S1 : hinv → Int)
    (h_bytes_remaining : T3 → Int)
    (ch_nbr : T3 → Int)
    (oy1 : T2)
    (sy_storage : T2 → Int)
    (x_size : hinv → Int)
    (length : T4 → Nat)
    (firstn : Nat → T5 → T4)
    (x_bs : hinv → T5)
    (h1 : (0 ≤ (x_S1 X) ∧ (x_S1 X) < (2 ^ (62 : Nat))))
    (h2 : (h_bytes_remaining h_1) ≤ 4096)
    (h3 : (0 < (ch_nbr h_1) ∧ (ch_nbr h_1) ≤ 200))
    (h4 : (ch_nbr h_1) ≤ (h_bytes_remaining h_1))
    (h5 : (0 ≤ ((sy_fill (h_oy h_1)) - (sy_returned (h_oy h_1))) ∧ ((sy_fill (h_oy h_1)) - (sy_returned (h_oy h_1))) ≤ 4096))
    (h6 : ((sy_fill oy1) + (ch_nbr h_1)) ≤ (sy_storage oy1))
    (h7 : 0 < (x_size X))
    (h8 : (((length (firstn (Int.toNat (ch_nbr h_1)) (x_bs X))) : Nat) : Int) = (ch_nbr h_1)) :
    (D' + (((sy_fill (h_oy h_1)) - (sy_returned (h_oy h_1))) + i)) = ((D' + ((sy_fill (h_oy h_1)) - (sy_returned (h_oy h_1)))) + i) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X06w.v (replace)
example
    {list_byte : Type}
    (F : Int)
    (base : Int)
    (o : Int)
    (n : Int)
    (sh : list_byte)
    (shad : Int → Int)
    (length : list_byte → Nat)
    (ushadow : Int → list_byte)
    (h1 : (F % 8) = 0)
    (h2 : 0 ≤ F)
    (h3 : (o % 8) = 0)
    (h4 : 0 ≤ base)
    (h5 : (8 * base) ≤ o)
    (h6 : 0 ≤ n)
    (h7 : ((Int.toNat ((o / 8) - base)) + (length (ushadow n))) ≤ (length sh))
    (h8 : base ≤ (o / 8)) :
    (((shad F) + base) + ((o / 8) - base)) = ((shad F) + (o / 8)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X06y.v (replace)
example (usp : Int) (S1 : Int) (h1 : ((S1 % 32) = 0 ∧ ((usp - 336) ≤ S1 ∧ S1 ≤ (usp - 320)))) :
    (usp + (-104)) = ((usp + (-320)) + ((216 : Nat) : Int)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X06z.v (replace)
example
    {T1 T2 T3 : Type}
    (pk_bytes : T1 → Int)
    (op : T1)
    (length : T2 → Nat)
    (os_body : T3 → T2)
    (os : T3)
    (pk_off : T1 → Int)
    (h1 : ((Int.toNat (pk_off op)) + (Int.toNat (pk_bytes op))) ≤ (length (os_body os))) :
    (Int.toNat (pk_bytes op)) = (min (Int.toNat (pk_bytes op)) ((length (os_body os)) - (Int.toNat (pk_off op)))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X07m.v (replace)
example (usp : Int) :
    ((usp + (-192)) + (((88 + 88) : Nat) : Int)) = (usp + (-16)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X07m.v (replace)
example
    {T1 T2 : Type}
    (f : Int)
    (low_mode : T1 → T1)
    (usp : Int)
    (init_dec : T1 → T2)
    (mo : T1)
    (init_stack : T1 → Int)
    (ctl_stack : T2 → Int)
    (init_nblocks : T1 → Int)
    (init_credit : T1 → Int)
    (mode_depth : T1 → Nat)
    (dec_depth : T2 → Nat)
    (SH_HI : Int)
    (lo : Int)
    (AL : Int)
    (h1 : (init_stack mo) = (192 + (max (init_stack (low_mode mo)) (ctl_stack (init_dec (low_mode mo))))))
    (h2 : (init_nblocks mo) = (9 + (init_nblocks (low_mode mo))))
    (h3 : (init_credit mo) = ((1 + (init_credit (low_mode mo))) + (2 * ((((mode_depth (low_mode mo)) : Nat) : Int) - 1))))
    (h4 : (mode_depth mo) = ((mode_depth (low_mode mo)) + 1))
    (h5 : (dec_depth (init_dec (low_mode mo))) = (mode_depth (low_mode mo)))
    (h6 : 0 ≤ (init_stack (low_mode mo)))
    (h7 : 1 ≤ (init_nblocks (low_mode mo)))
    (h8 : 0 ≤ (init_credit (low_mode mo)))
    (h9 : (1 ≤ (mode_depth (low_mode mo)) ∧ (mode_depth (low_mode mo)) ≤ 2))
    (h10 : SH_HI ≤ lo)
    (h11 : lo ≤ (usp + (-192)))
    (h12 : (0 < AL ∧ AL < (2 ^ (63 : Nat))))
    (h13 : (f % 8) = 0)
    (h14 : ((f + 32) % 4) = 0) :
    (f + 36) = ((f + 32) + 4) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X09a.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (x_st : T1 → Int)
    (X : T1)
    (sub : Int)
    (x_ff : T1 → Int)
    (SHB : Int)
    (x_sf : T1 → Int)
    (shad : Int → Int)
    (st : T2)
    (nb_isave_ptr : Int → T2 → Int)
    (x_out : T1 → Int)
    (x_nout : T1 → Nat)
    (length : T3 → Nat)
    (bs : T3)
    (sb_buf_size : T4 → Int)
    (bJ : T4)
    (x_D : T1 → Int)
    (x_lo : T1 → Int)
    (PD : Int)
    (ND : Int)
    (x_dsz : T1 → Int)
    (jF : T5)
    (owsF : T3)
    (j_exc : T5 → Int)
    (ex1 : T3)
    (exw : T3)
    (ex3 : T3)
    (SH_LO : Int)
    (SH_HI : Int)
    (h1 : (((x_ff X) / 8) + SHB) = (x_sf X))
    (h2 : (shad (x_ff X)) = (x_sf X))
    (h3 : (shad ((x_ff X) + 2048)) = ((x_sf X) + 256))
    (h4 : (0 ≤ (nb_isave_ptr (x_out X) st) ∧ (nb_isave_ptr (x_out X) st) < (2 ^ (63 : Nat))))
    (h5 : (((length bs) : Nat) : Int) = (sb_buf_size bJ))
    (h6 : ((x_D X) + (((length bs) : Nat) : Int)) ≤ (x_lo X))
    (h7 : ((x_D X) + (((length bs) : Nat) : Int)) ≤ (PD + ND))
    (h8 : (((length bs) : Nat) : Int) = (x_dsz X))
    (h9 : (length owsF) = (x_nout X))
    (h10 : (j_exc jF) = ((x_st X) + 1368))
    (h11 : (((length ex1) : Nat) : Int) = (334 + (40 * sub)))
    (h12 : (length exw) = 40)
    (h13 : (((length ex3) : Nat) : Int) = (126 - (40 * sub)))
    (h14 : (((((x_st X) + 1368) + (160 * sub)) + 160) ≤ SH_LO ∨ SH_HI ≤ (((x_st X) + 1368) + (160 * sub))))
    (h15 : (((((x_st X) + 1368) + (160 * sub)) + 160) ≤ (x_ff X) ∨ ((x_ff X) + 2048) ≤ (((x_st X) + 1368) + (160 * sub)))) :
    ((((x_st X) + 1368) + (160 * sub)) + 0) = (((x_st X) + 1368) + (160 * sub)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X09c.v (assert)
example
    {T1 : Type}
    (EXW : Int)
    (length : T1 → Nat)
    (dn : T1)
    (ST : Int)
    (h1 : ((EXW + (4 * (((length dn) : Nat) : Int))) + 4) ≤ (ST + 2032)) :
    EXW ≤ (EXW + (4 * (((length dn) : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0a1.v (replace)
example
    {T1 T2 T3 : Type}
    (H : Int)
    (i : Int)
    (zsum : T1 → Int)
    (zslice : Int → Int → T2 → T1)
    (ubytes : T3 → T2)
    (hs : T3)
    (znth : T2 → Int → Int)
    (lacing_of : T2 → T1)
    (v : Int)
    (acc : Int)
    (h1 : ((zsum (zslice 27 i (ubytes hs))) + (zsum (zslice (27 + i) ((znth (ubytes hs) 26) - i) (ubytes hs)))) = (zsum (lacing_of (ubytes hs))))
    (h2 : (zsum (zslice (27 + i) ((znth (ubytes hs) 26) - i) (ubytes hs))) = (v + (zsum (zslice ((27 + i) + 1) (((znth (ubytes hs) 26) - i) - 1) (ubytes hs)))))
    (h3 : v ≤ (zsum (zslice (27 + i) ((znth (ubytes hs) 26) - i) (ubytes hs))))
    (h4 : (acc + 255) = (zsum (zslice 27 (i + 1) (ubytes hs)))) :
    ((H + 27) + (i + 1)) = (((H + 27) + i) + 1) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0ae.v (replace)
example
    (x : Int)
    (y : Int)
    (h1 : ((-(2 ^ (31 : Nat))) ≤ y ∧ y < (2 ^ (31 : Nat))))
    (h2 : (Int.fmod y (2 ^ (32 : Nat))) = (Int.fmod x (2 ^ (32 : Nat)))) :
    x = ((x + (2 ^ (31 : Nat))) - (2 ^ (31 : Nat))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0an.v (replace)
example (e0 : Int) (EB : Int) (h1 : (((EB + (4 * e0)) - EB) % 4) = 0) :
    (e0 * 4) = ((EB + (4 * e0)) - EB) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0ap.v (assert)
example
    {T1 : Type}
    (G1 : Int)
    (X2 : Int)
    (HN : Int)
    (X1 : Int)
    (Y : Int)
    (length : T1 → Nat)
    (ys : T1)
    (G0 : Int)
    (IMG_TOP : Int)
    (h1 : (X1 % 4) = 0)
    (h2 : (X2 % 4) = 0)
    (h3 : ((Y + (4 * (((length ys) : Nat) : Int))) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ Y))
    (h4 : ((Y + (4 * (((length ys) : Nat) : Int))) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ Y))
    (h5 : ((G0 + 256) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ G0))
    (h6 : ((G1 + 256) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ G1))
    (h7 : IMG_TOP ≤ X1)
    (h8 : IMG_TOP ≤ X2)
    (h9 : ((Y + (16 * HN)) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ Y))
    (h10 : ((Y + (16 * HN)) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ Y)) :
    ((G1 + 256) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ G1) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0au.v (replace)
example (A : Int) (jz : Int) (h1 : (A % 8) = 0) :
    (A + (8 * (jz + 2))) = ((A + (8 * jz)) + 16) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0av.v (replace)
example (Y : Int) (h_1 : Int) :
    (Y + (16 * (h_1 + 1))) = (((((Y + (16 * h_1)) + 4) + 4) + 4) + 4) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0b8.v (replace)
example
    {list_word : Type}
    (ws : list_word)
    (i : Nat)
    (k : Nat)
    (length : list_word → Nat)
    (h1 : (i + k) ≤ (length ws)) :
    k = (min k ((length ws) - i)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0bm.v (replace)
example
    {T1 : Type}
    (INN : Int)
    (off : Int)
    (ssz : Int)
    (sbits : Int)
    (Zpow : Int → Int → Int)
    (iv : Int)
    (length : T1 → Nat)
    (irest : T1)
    (rest : T1)
    (firstn : Nat → T1 → T1)
    (skipn : Nat → T1 → T1)
    (h1 : (2 ≤ (Zpow 2 sbits) ∧ (Zpow 2 sbits) ≤ 256))
    (h2 : (0 ≤ (iv * ssz) ∧ ((iv * ssz) + ssz) ≤ ((Zpow 2 sbits) * ssz)))
    (h3 : 0 ≤ (ssz * (((length irest) : Nat) : Int)))
    (h4 : (Int.toNat ssz) ≤ (length rest))
    (h5 : (length (firstn (Int.toNat ssz) rest)) = (Int.toNat ssz))
    (h6 : (length (skipn (Int.toNat ssz) rest)) = ((length rest) - (Int.toNat ssz))) :
    (INN + (off + (4 * ssz))) = ((INN + off) + (4 * ssz)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/A/X0f2.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (n0 : Int)
    (p : Int)
    (M : Int)
    (n' : Int)
    (n : Int)
    (firstn : Nat → T2 → T3)
    (bs : T2)
    (length : T3 → Nat)
    (q : Int)
    (Z_to_bv : Int → Int → T1)
    (wr_trace : T4 → T5 → T3)
    (tr : T4)
    (tb : T5)
    (h1 : 1 ≤ n0)
    (h2 : p = (M + 16))
    (h3 : ((1 ≤ n' ∧ n' ≤ n) ∧ n' ≤ n0))
    (h4 : (((length (firstn (Int.toNat n') bs)) : Nat) : Int) = n')
    (h5 : (length (firstn (Int.toNat n') bs)) = (Int.toNat (min n n0)))
    (h6 : (((M + 16) + n') ≤ q ∨ (q + n') ≤ M))
    (h7 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-80)))) = ((bv_unsigned sp) + (-80)))
    (h8 : (length (wr_trace tr tb)) = 255) :
    ((bv_unsigned sp) + (-2136)) = (((bv_unsigned sp) + (-80)) + (-2056)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/AS/X0ll.v (replace)
example
    {T1 T2 T3 T4 word : Type}
    (E : T1)
    (b1 : T2)
    (o1 : T3)
    (n1 : T2)
    (b2 : T2)
    (o2 : T3)
    (n2 : T2)
    (estart : T1 → T4 → Int)
    (SA : T2 → T3 → T4)
    (i : Int)
    (bv_unsigned : word → Int)
    (edenot : T1 → T2 → word)
    (eadd : T2 → T2 → T2)
    (h1 : 0 ≤ (estart E (SA b1 o1)))
    (h2 : ((estart E (SA b1 o1)) + (bv_unsigned (edenot E (eadd n1 n2)))) ≤ (2 ^ (64 : Nat)))
    (h3 : (bv_unsigned (edenot E (eadd n1 n2))) = (Int.fmod ((bv_unsigned (edenot E n1)) + (bv_unsigned (edenot E n2))) (2 ^ (64 : Nat))))
    (h4 : (Int.fmod ((estart E (SA b1 o1)) + (bv_unsigned (edenot E n1))) (2 ^ (64 : Nat))) = (Int.fmod (estart E (SA b2 o2)) (2 ^ (64 : Nat))))
    (h5 : (bv_unsigned (edenot E (eadd n1 n2))) ≤ ((bv_unsigned (edenot E n1)) + (bv_unsigned (edenot E n2))))
    (h6 : ((estart E (SA b1 o1)) + (bv_unsigned (edenot E n1))) < (2 ^ (64 : Nat)))
    (h7 : ((estart E (SA b1 o1)) + (bv_unsigned (edenot E n1))) = (estart E (SA b2 o2))) :
    ((estart E (SA b2 o2)) + (i - (bv_unsigned (edenot E n1)))) = ((estart E (SA b1 o1)) + i) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/AS/X0ll.v (assert)
example
    {T1 T2 T3 word : Type}
    (E : T1)
    (k : T2)
    (a : T3)
    (e : T3)
    (bv_unsigned : word → Int)
    (edenot : T1 → T3 → word)
    (respell_ok : T2 → T3 → T3 → Bool)
    (h1 : (respell_ok k a e) = true)
    (h2 : (Int.fmod ((bv_unsigned (edenot E a)) - (bv_unsigned (edenot E e))) (2 ^ (64 : Nat))) = 0) :
    (Int.fmod ((bv_unsigned (edenot E a)) - (bv_unsigned (edenot E e))) (2 ^ (64 : Nat))) = 0 := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Agent/X0q5.v (replace)
example
    {mstate T2 T3 T4 T5 T6 T7 T8 : Type}
    (st : mstate)
    (blk : T2)
    (i : Int)
    (res : Int)
    (bm : T3)
    (m : T4)
    (blk_slot : T2 → T3)
    (snd : T3 → Int)
    (UNIT : Int)
    (get_stride : T5 → Int)
    (MR : mstate → T4 → T5)
    (q : Int)
    (off : Int)
    (m_maplen : T5 → Int)
    (round_up_pg : T6 → Int)
    (r_len : T7 → T6)
    (r : T7)
    (m_last_idx : T5 → Int)
    (c_secret : T8 → Int)
    (ctx : mstate → T8)
    (h1 : (snd (blk_slot blk)) = (((snd bm) + UNIT) + ((get_stride (MR st m)) * i)))
    (h2 : 0 ≤ ((get_stride (MR st m)) * i))
    (h3 : (16 * q) = (((get_stride (MR st m)) * i) + (UNIT * off)))
    (h4 : (((get_stride (MR st m)) * i) % 16) = 0)
    (h5 : ((m_maplen (MR st m)) ≠ 0 → ((snd bm) = 0 ∧ ((m_maplen (MR st m)) * 4096) = (round_up_pg (r_len r)))))
    (h6 : (((snd bm) + UNIT) + ((get_stride (MR st m)) * ((m_last_idx (MR st m)) + 1))) ≤ (round_up_pg (r_len r)))
    (h7 : (m_maplen (MR st m)) < (2 ^ (35 : Nat)))
    (h8 : 0 ≤ res)
    (h9 : (0 ≤ (c_secret (ctx st)) ∧ (c_secret (ctx st)) < (2 ^ (64 : Nat)))) :
    (i + ((min res 5) * 32)) = (i + (32 * (min res 5))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X0yd.v (replace)
example (pm : Int) (off : Int) (pden : Int) (h1 : (decide ((pden + off) < 1)) = false) :
    (pm + (off + 4)) = ((pm + off) + 4) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X0yd.v (replace)
example
    (py : Int)
    (i : Int)
    (px : Int)
    (h1 : (decide ((px + (4 * i)) < 1)) = false)
    (h2 : (decide ((py + (4 * i)) < 1)) = false) :
    (py + (4 * (i + 1))) = ((py + (4 * i)) + 4) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X0yd.v (replace)
example
    (py : Int)
    (Z_land : Int → Int → Int)
    (h1 : (decide (0 < py)) = true)
    (h2 : (decide ((Z_land py 3) < 1)) = true) :
    (py + (4 * 0)) = py := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X0yx.v (replace)
example
    (usp : Int)
    (IQ : Int)
    (AK : Int)
    (h1 : ((IQ + 40) ≤ (usp + (-384)) ∨ ((usp + (-384)) + 40) ≤ IQ))
    (h2 : ((usp + (-384)) % 4) = 0)
    (h3 : ((usp + (-384)) % 8) = 0)
    (h4 : ((usp + (-256)) % 8) = 0)
    (h5 : (((usp + (-384)) + 40) ≤ (usp + (-256)) ∨ ((usp + (-256)) + 88) ≤ (usp + (-384))))
    (h6 : ((AK + 40) ≤ (usp + (-256)) ∨ ((usp + (-256)) + 88) ≤ AK))
    (h7 : ((AK + 40) ≤ (usp + (-384)) ∨ ((usp + (-384)) + 40) ≤ AK)) :
    ((usp + (-384)) + (4 * 0)) = (usp + (-384)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X0z0.v (replace)
example (k : Int) (WP : Int) (h1 : ((WP + (4 * k)) % 4) = 0) :
    (22 - (k + 1)) = ((22 - k) + (-1)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X0za.v (replace)
example (i : Int) (EO : Int) (XB : Int) (h1 : ((EO + ((XB - EO) + (4 * i))) % 4) = 0) :
    (4 * (i + 1)) = ((4 * i) + 4) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X0za.v (replace)
example
    {list_word : Type}
    (EO : Int)
    (XB : Int)
    (I1 : Int)
    (I2 : Int)
    (NE : Int)
    (usp : Int)
    (lo : Int)
    (xw : list_word)
    (i1 : list_word)
    (i2 : list_word)
    (ns : list_word)
    (IMG_TOP_B : Int)
    (SH_LO : Int)
    (SH_HI : Int)
    (length : list_word → Nat)
    (h1 : I1 = (usp + (-896)))
    (h2 : I2 = (I1 + 320))
    (h3 : (EO ≤ XB ∧ (XB + 320) ≤ (EO + 2000)))
    (h4 : (EO % 4) = 0)
    (h5 : (XB % 4) = 0)
    (h6 : (I1 % 4) = 0)
    (h7 : (NE % 4) = 0)
    (h8 : ((NE + 320) ≤ EO ∨ (EO + 2000) ≤ NE))
    (h9 : ((NE + 320) ≤ I1 ∨ (I1 + 640) ≤ NE))
    (h10 : IMG_TOP_B ≤ NE)
    (h11 : ((NE + 320) ≤ SH_LO ∨ SH_HI ≤ NE))
    (h12 : 0 < EO)
    (h13 : (0 < NE ∧ (NE + 320) < (2 ^ (62 : Nat))))
    (h14 : (NE + 320) ≤ lo)
    (h15 : (XB + 320) ≤ lo)
    (h16 : (length xw) = 80)
    (h17 : (length i1) = 80)
    (h18 : (length i2) = 80)
    (h19 : (length ns) = 80)
    (h20 : lo ≤ (usp - 4320))
    (h21 : SH_HI ≤ lo)
    (h22 : usp < (2 ^ (63 : Nat)))
    (h23 : (EO ≤ XB ∧ ((XB + 320) ≤ (EO + 2000) ∧ ((XB - EO) % 4) = 0)))
    (h24 : 0 < I1) :
    ((I1 + 320) + (4 * 0)) = (I1 + 320) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X100.v (replace)
example
    {T1 : Type}
    (x_ff : T1 → Int)
    (X : T1)
    (SHB : Int)
    (x_sf : T1 → Int)
    (shad : Int → Int)
    (h1 : (((x_ff X) / 8) + SHB) = (x_sf X))
    (h2 : ((((x_ff X) + 2048) / 8) + SHB) = ((x_sf X) + 256))
    (h3 : (shad (x_ff X)) = (x_sf X))
    (h4 : (shad ((x_ff X) + 2048)) = ((x_sf X) + 256)) :
    ((x_ff X) + 280) = (((x_ff X) + 240) + 40) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X100.v (replace)
example
    {list_word T2 T3 T4 : Type}
    (oq : list_word)
    (qs : list_word)
    (sub : Int)
    (x_out : T2 → Int)
    (X : T2)
    (length : list_word → Nat)
    (x_ff : T2 → Int)
    (x_nout : T2 → Nat)
    (SHB : Int)
    (x_sf : T2 → Int)
    (shad : Int → Int)
    (ow1 : list_word)
    (ow3 : list_word)
    (firstn : Int → T3 → list_word)
    (skipn : Nat → T4 → T3)
    (ows : T4)
    (h1 : (0 ≤ sub ∧ sub < 4))
    (h2 : (length oq) = 10)
    (h3 : (length qs) = 10)
    (h4 : (((x_ff X) / 8) + SHB) = (x_sf X))
    (h5 : ((((x_ff X) + 2048) / 8) + SHB) = ((x_sf X) + 256))
    (h6 : (shad (x_ff X)) = (x_sf X))
    (h7 : (shad ((x_ff X) + 2048)) = ((x_sf X) + 256))
    (h8 : 160 ≤ (x_nout X))
    (h9 : (((length ow1) : Nat) : Int) = (40 * sub))
    (h10 : (((length ow3) : Nat) : Int) = (((((x_nout X) : Nat) : Int) - (40 * sub)) - 40))
    (h11 : (length (firstn 40 (skipn (Int.toNat (40 * sub)) ows))) = 40) :
    ((x_out X) + (160 * sub)) = ((x_out X) + (4 * (40 * sub))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X100.v (replace)
example
    {T1 T2 : Type}
    (x_st : T1 → Int)
    (X : T1)
    (length : T2 → Nat)
    (bsb : T2)
    (x_dsz : T1 → Int)
    (x_ff : T1 → Int)
    (SHB : Int)
    (x_sf : T1 → Int)
    (shad : Int → Int)
    (eb1 : T2)
    (eb2 : T2)
    (eb3 : T2)
    (h1 : (((length bsb) : Nat) : Int) = (x_dsz X))
    (h2 : (((x_ff X) / 8) + SHB) = (x_sf X))
    (h3 : ((((x_ff X) + 2048) / 8) + SHB) = ((x_sf X) + 256))
    (h4 : (shad (x_ff X)) = (x_sf X))
    (h5 : (shad ((x_ff X) + 2048)) = ((x_sf X) + 256))
    (h6 : (length eb1) = 294)
    (h7 : (length eb2) = 160)
    (h8 : (length eb3) = 46) :
    ((x_st X) + 1848) = ((((x_st X) + 32) + 1176) + 640) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X100.v (replace)
example
    {T1 T2 : Type}
    (x_st : T1 → Int)
    (X : T1)
    (length : T2 → Nat)
    (bsb : T2)
    (x_dsz : T1 → Int)
    (x_ff : T1 → Int)
    (SHB : Int)
    (x_sf : T1 → Int)
    (shad : Int → Int)
    (eb1 : T2)
    (eb2 : T2)
    (eb3 : T2)
    (ow1 : T2)
    (ow2 : T2)
    (x_nout : T1 → Nat)
    (bsx : T2)
    (oh1 : T2)
    (oh2 : T2)
    (h1 : (((length bsb) : Nat) : Int) = (x_dsz X))
    (h2 : (((x_ff X) / 8) + SHB) = (x_sf X))
    (h3 : ((((x_ff X) + 2048) / 8) + SHB) = ((x_sf X) + 256))
    (h4 : (shad (x_ff X)) = (x_sf X))
    (h5 : (shad ((x_ff X) + 2048)) = ((x_sf X) + 256))
    (h6 : (length eb1) = 294)
    (h7 : (length eb2) = 160)
    (h8 : (length eb3) = 46)
    (h9 : (length ow1) = 160)
    (h10 : (((length ow2) : Nat) : Int) = ((((x_nout X) : Nat) : Int) - 160))
    (h11 : (length bsx) = 640)
    (h12 : (length oh1) = 160)
    (h13 : (((length oh2) : Nat) : Int) = ((((x_nout X) : Nat) : Int) - 160)) :
    ((x_st X) + 1208) = (((x_st X) + 32) + (4 * ((294 : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X100.v (replace)
example
    {T1 T2 : Type}
    (x_st : T1 → Int)
    (X : T1)
    (length : T2 → Nat)
    (bsb : T2)
    (x_dsz : T1 → Int)
    (x_ff : T1 → Int)
    (SHB : Int)
    (x_sf : T1 → Int)
    (shad : Int → Int)
    (eb1 : T2)
    (eb2 : T2)
    (eb3 : T2)
    (ow1 : T2)
    (ow2 : T2)
    (x_nout : T1 → Nat)
    (bsx : T2)
    (oh1 : T2)
    (oh2 : T2)
    (o1a : T2)
    (o1b : T2)
    (h1 : (((length bsb) : Nat) : Int) = (x_dsz X))
    (h2 : (((x_ff X) / 8) + SHB) = (x_sf X))
    (h3 : ((((x_ff X) + 2048) / 8) + SHB) = ((x_sf X) + 256))
    (h4 : (shad (x_ff X)) = (x_sf X))
    (h5 : (shad ((x_ff X) + 2048)) = ((x_sf X) + 256))
    (h6 : (length eb1) = 294)
    (h7 : (length eb2) = 160)
    (h8 : (length eb3) = 46)
    (h9 : (length ow1) = 160)
    (h10 : (((length ow2) : Nat) : Int) = ((((x_nout X) : Nat) : Int) - 160))
    (h11 : (length bsx) = 640)
    (h12 : (length oh1) = 160)
    (h13 : (((length oh2) : Nat) : Int) = ((((x_nout X) : Nat) : Int) - 160))
    (h14 : (length o1a) = 80)
    (h15 : (length o1b) = 80) :
    ((x_st X) + 1208) = (((x_st X) + 32) + (4 * ((294 : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X100.v (replace)
example
    {T1 T2 : Type}
    (x_st : T1 → Int)
    (X : T1)
    (length : T2 → Nat)
    (bsb : T2)
    (x_dsz : T1 → Int)
    (x_ff : T1 → Int)
    (SHB : Int)
    (x_sf : T1 → Int)
    (shad : Int → Int)
    (eb1 : T2)
    (eb2 : T2)
    (eb3 : T2)
    (ow1 : T2)
    (ow2 : T2)
    (x_nout : T1 → Nat)
    (bsx : T2)
    (oh1 : T2)
    (oh2 : T2)
    (o1a : T2)
    (o1b : T2)
    (h1 : (((length bsb) : Nat) : Int) = (x_dsz X))
    (h2 : (((x_ff X) / 8) + SHB) = (x_sf X))
    (h3 : ((((x_ff X) + 2048) / 8) + SHB) = ((x_sf X) + 256))
    (h4 : (shad (x_ff X)) = (x_sf X))
    (h5 : (shad ((x_ff X) + 2048)) = ((x_sf X) + 256))
    (h6 : (length eb1) = 294)
    (h7 : (length eb2) = 160)
    (h8 : (length eb3) = 46)
    (h9 : (length ow1) = 160)
    (h10 : (((length ow2) : Nat) : Int) = ((((x_nout X) : Nat) : Int) - 160))
    (h11 : (length bsx) = 640)
    (h12 : (length oh1) = 160)
    (h13 : (((length oh2) : Nat) : Int) = ((((x_nout X) : Nat) : Int) - 160))
    (h14 : (length o1a) = 80)
    (h15 : (length o1b) = 80) :
    ((x_st X) + 20) = (((x_st X) + 16) + ((4 : Nat) : Int)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X11a.v (replace)
example
    {T1 : Type}
    (X1 : Int)
    (HN : Int)
    (X2 : Int)
    (Y : Int)
    (length : T1 → Nat)
    (ys : T1)
    (IMG_TOP_B : Int)
    (G0 : Int)
    (G1 : Int)
    (h1 : (X1 % 4) = 0)
    (h2 : (X2 % 4) = 0)
    (h3 : ((Y + (4 * (((length ys) : Nat) : Int))) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ Y))
    (h4 : ((Y + (4 * (((length ys) : Nat) : Int))) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ Y))
    (h5 : IMG_TOP_B ≤ X1)
    (h6 : IMG_TOP_B ≤ X2)
    (h7 : ((Y + (16 * HN)) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ Y))
    (h8 : ((Y + (16 * HN)) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ Y))
    (h9 : ((G0 + 256) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ G0))
    (h10 : ((G1 + 256) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ G1)) :
    ((X1 + (4 * (2 * HN))) + (4 * 0)) = (X1 + (8 * HN)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X11a.v (replace)
example
    {T1 : Type}
    (Y : Int)
    (X1 : Int)
    (X2 : Int)
    (length : T1 → Nat)
    (ys : T1)
    (HN : Int)
    (IMG_TOP_B : Int)
    (G0 : Int)
    (G1 : Int)
    (ys2 : T1)
    (h1 : (X1 % 4) = 0)
    (h2 : (X2 % 4) = 0)
    (h3 : ((Y + (4 * (((length ys) : Nat) : Int))) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ Y))
    (h4 : ((Y + (4 * (((length ys) : Nat) : Int))) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ Y))
    (h5 : IMG_TOP_B ≤ X1)
    (h6 : IMG_TOP_B ≤ X2)
    (h7 : ((Y + (16 * HN)) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ Y))
    (h8 : ((Y + (16 * HN)) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ Y))
    (h9 : ((G0 + 256) ≤ X1 ∨ (X1 + ((8 * HN) + 128)) ≤ G0))
    (h10 : ((G1 + 256) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ G1))
    (h11 : ((Y + (8 * HN)) % 4) = 0)
    (h12 : (((Y + (8 * HN)) + (4 * (((length ys2) : Nat) : Int))) ≤ X2 ∨ (X2 + ((8 * HN) + 128)) ≤ (Y + (8 * HN)))) :
    (Y + (16 * 0)) = Y := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X11b.v (replace)
example
    (i : Int)
    (Y : Int)
    (N2 : Int)
    (X : Int)
    (h1 : ((Y + (4 * ((N2 - 1) - i))) % 4) = 0)
    (h2 : ((X + (4 * i)) % 4) = 0) :
    (4 * (i + 1)) = ((4 * i) + 4) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/B/X11w.v (replace)
example
    (IQP : Int)
    (h1 : ((4 + IQP) % 4) = 0)
    (h2 : ((8 + IQP) % 4) = 0)
    (h3 : ((12 + IQP) % 4) = 0)
    (h4 : ((16 + IQP) % 4) = 0) :
    (IQP + (4 * 4)) = (IQP + 16) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1fe.v (replace)
example
    {T1 : Type}
    (buf : T1)
    (off : Nat)
    (i : Nat)
    (k : Nat)
    (length : T1 → Nat)
    (h1 : ((off + i) + k) ≤ (length buf)) :
    i = (min i (i + k)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1fn.v (assert)
example (pitch : Int) (i : Int) :
    (40 < ((pitch + 1) - i) ∨ (((pitch + 1) - i) = 40 ∨ ((((pitch + 1) - i) < 40 ∧ 40 < (((2 * pitch) + 1) - i)) ∨ (((2 * pitch) + 1) - i) ≤ 40))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1fx.v (replace)
example
    {T1 T2 : Type}
    (OUT : Int)
    (sbd_frame_size : T1 → Int)
    (s : T1)
    (sbd_subframeSize : T1 → Int)
    (a_g0 : T2 → Int)
    (a : T2)
    (alloc_ceiling : Int)
    (a_g1 : T2 → Int)
    (a_exc : T2 → Int)
    (a_oq : T2 → Int)
    (a_iq : T2 → Int)
    (a_pg : T2 → Int)
    (a_er : T2 → Int)
    (a_msp : T2 → Int)
    (h1 : (160 ≤ (sbd_frame_size s) ∧ (sbd_frame_size s) ≤ 320))
    (h2 : (40 ≤ (sbd_subframeSize s) ∧ (sbd_subframeSize s) ≤ 80))
    (h3 : (0 < (a_g0 a) ∧ ((a_g0 a) + 256) ≤ alloc_ceiling))
    (h4 : (0 < (a_g1 a) ∧ ((a_g1 a) + 256) ≤ alloc_ceiling))
    (h5 : (0 < (a_exc a) ∧ ((a_exc a) + (4 * (sbd_subframeSize s))) ≤ alloc_ceiling))
    (h6 : (0 < (a_oq a) ∧ ((a_oq a) + 32) ≤ alloc_ceiling))
    (h7 : (0 < (a_iq a) ∧ ((a_iq a) + 32) ≤ alloc_ceiling))
    (h8 : (0 < (a_pg a) ∧ ((a_pg a) + 16) ≤ alloc_ceiling))
    (h9 : (0 < (a_er a) ∧ ((a_er a) + 16) ≤ alloc_ceiling))
    (h10 : (0 < (a_msp a) ∧ ((a_msp a) + 64) ≤ alloc_ceiling)) :
    (OUT + (4 * (sbd_frame_size s))) = (OUT + (4 * (((Int.toNat (sbd_frame_size s)) : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1fx.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (OUT : Int)
    (sbd_frame_size : T1 → Int)
    (s : T1)
    (sbd_subframeSize : T1 → Int)
    (a_g0 : T2 → Int)
    (a : T2)
    (alloc_ceiling : Int)
    (a_g1 : T2 → Int)
    (a_exc : T2 → Int)
    (a_oq : T2 → Int)
    (a_iq : T2 → Int)
    (a_pg : T2 → Int)
    (a_er : T2 → Int)
    (a_msp : T2 → Int)
    (length : T3 → Nat)
    (owsA : T3)
    (owsB : T3)
    (owsC : T3)
    (firstn : Int → T4 → T3)
    (sj_msp : T5 → T4)
    (j : T5)
    (skipn : Int → T4 → T3)
    (h1 : (160 ≤ (sbd_frame_size s) ∧ (sbd_frame_size s) ≤ 320))
    (h2 : (40 ≤ (sbd_subframeSize s) ∧ (sbd_subframeSize s) ≤ 80))
    (h3 : (0 < (a_g0 a) ∧ ((a_g0 a) + 256) ≤ alloc_ceiling))
    (h4 : (0 < (a_g1 a) ∧ ((a_g1 a) + 256) ≤ alloc_ceiling))
    (h5 : (0 < (a_exc a) ∧ ((a_exc a) + (4 * (sbd_subframeSize s))) ≤ alloc_ceiling))
    (h6 : (0 < (a_oq a) ∧ ((a_oq a) + 32) ≤ alloc_ceiling))
    (h7 : (0 < (a_iq a) ∧ ((a_iq a) + 32) ≤ alloc_ceiling))
    (h8 : (0 < (a_pg a) ∧ ((a_pg a) + 16) ≤ alloc_ceiling))
    (h9 : (0 < (a_er a) ∧ ((a_er a) + 16) ≤ alloc_ceiling))
    (h10 : (0 < (a_msp a) ∧ ((a_msp a) + 64) ≤ alloc_ceiling))
    (h11 : (length owsA) = (Int.toNat (sbd_frame_size s)))
    (h12 : (length owsB) = (Int.toNat (sbd_frame_size s)))
    (h13 : (((length owsC) : Nat) : Int) = (2000 - (2 * (sbd_frame_size s))))
    (h14 : (length (firstn 8 (sj_msp j))) = 8)
    (h15 : (length (skipn 8 (sj_msp j))) = 8) :
    (OUT + (4 * (sbd_frame_size s))) = (OUT + (4 * (((Int.toNat (sbd_frame_size s)) : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1gn.v (replace)
example {T1 : Type} (usp : T1 → Int) (c : T1) :
    ((usp c) + (-6120)) = (((usp c) + (-152)) - 5968) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1h5.v (replace)
example
    {hcx T2 T3 : Type}
    (c : hcx)
    (h_1 : T2)
    (hd : T3)
    (ch2 : Int)
    (br0 : Int)
    (usp : hcx → Int)
    (h_bytes_remaining : T2 → Int)
    (h_eos : T2 → Int)
    (hd_extra_headers : T3 → Int)
    (h1 : (h_bytes_remaining h_1) = br0)
    (h2 : (0 ≤ (h_eos h_1) ∧ (h_eos h_1) ≤ 1))
    (h3 : ((-(2 ^ (31 : Nat))) ≤ ch2 ∧ ch2 < (2 ^ (31 : Nat))))
    (h4 : (hd_extra_headers hd) = 2147483647)
    (h5 : (hd_extra_headers hd) ≠ 2147483647) :
    ((usp c) + (-8756)) = (((usp c) + (-8760)) + ((4 : Nat) : Int)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1ii.v (replace)
example
    {list_byte : Type}
    (l : list_byte)
    (xs : list_byte)
    (p : Nat)
    (i : Nat)
    (n : Nat)
    (length : list_byte → Nat)
    (h1 : (i + (length xs)) ≤ n)
    (h2 : (p + n) ≤ (length l)) :
    i = (min i ((length l) - p)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1iy.v (replace)
example
    {T1 T2 : Type}
    (segptr : Int)
    (znth : T1 → Int → Int)
    (ubytes : T2 → T1)
    (hs : T2)
    (h1 : segptr = (znth (ubytes hs) 26)) :
    (27 + segptr) = (27 + segptr) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1j0.v (replace)
example :
    (21 : Int) = (((18 + 1) + 1) + 1) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1j2.v (replace)
example (Bd' : Int) (f : Nat) (n : Nat) :
    ((Bd' + ((f : Nat) : Int)) + (((n + 0) : Nat) : Int)) = ((Bd' + ((f : Nat) : Int)) + ((n : Nat) : Int)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1kd.v (replace)
example
    {word list_list_byte : Type}
    (sp0 : word)
    (argv : list_list_byte)
    (envp : list_list_byte)
    (rnd_addr : word → list_list_byte → list_list_byte → Int)
    (bv_unsigned : word → Int)
    (sp_window_lo : Int)
    (alloc_ceiling : Int)
    (h1 : sp_window_lo ≤ (bv_unsigned sp0))
    (h2 : alloc_ceiling = ((bv_unsigned sp0) - 8388608)) :
    ((rnd_addr sp0 argv envp) + ((8 : Nat) : Int)) = ((rnd_addr sp0 argv envp) + 8) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1l2.v (assert)
example
    {T1 T2 T3 : Type}
    (LEN : Int)
    (zlength : T1 → Int)
    (rd_content : T2 → T1)
    (st1 : T2)
    (length : T3 → Nat)
    (DATA : T3)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int)) :
    0 ≤ LEN := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1lq.v (replace)
example
    (E : Int)
    (mword : Int)
    (idx : Int)
    (rsv : Int)
    (stride : Int)
    (h1 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ idx ∧ idx < 32))
    (h3 : (0 ≤ rsv ∧ rsv < (2 ^ (32 : Nat))))
    (h4 : 0 ≤ (stride * idx)) :
    ((E + 4) + (-9)) = (E - 5) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1mk.v (replace)
example
    {sbinv T2 T3 T4 : Type}
    (X : sbinv)
    (s1 : T2)
    (sub : Int)
    (x_out : sbinv → Int)
    (length : T3 → Nat)
    (owsA : T3)
    (sbd_subframeSize : T4 → Int)
    (x_s : sbinv → T4)
    (sbd_frame_size : T2 → Int)
    (owsB : T3)
    (owsC : T3)
    (h1 : (sbd_subframeSize (x_s X)) = 40)
    (h2 : (sbd_frame_size s1) = (4 * (sbd_subframeSize (x_s X))))
    (h3 : (((length owsA) : Nat) : Int) = (320 + (80 * sub)))
    (h4 : (length owsB) = 80)
    (h5 : (((length owsC) : Nat) : Int) = ((2000 - 80) - (320 + (80 * sub)))) :
    ((((x_out X) + 1280) + (320 * sub)) + 320) = ((x_out X) + (4 * ((((length owsA) + (2 * 40)) : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1mm.v (replace)
example
    {sbinv T2 T3 T4 T5 T6 : Type}
    (X : sbinv)
    (s1 : T2)
    (x_out : sbinv → Int)
    (sbd_subframeSize : T3 → Int)
    (x_s : sbinv → T3)
    (sbd_frame_size : T2 → Int)
    (sbd_full_frame_size : T2 → Int)
    (j : T4)
    (length : T5 → Nat)
    (owsA : T5)
    (owsB : T5)
    (owsC : T5)
    (firstn : Int → T6 → T5)
    (sj_msp : T4 → T6)
    (skipn : Int → T6 → T5)
    (h1 : (sbd_subframeSize (x_s X)) = 40)
    (h2 : (sbd_frame_size s1) = (4 * (sbd_subframeSize (x_s X))))
    (h3 : (sbd_full_frame_size s1) = (8 * (sbd_subframeSize (x_s X))))
    (h4 : (length owsA) = 160)
    (h5 : (length owsB) = 160)
    (h6 : (length owsC) = ((2000 - 160) - 160))
    (h7 : (length (firstn 8 (sj_msp j))) = 8)
    (h8 : (length (skipn 8 (sj_msp j))) = 8) :
    ((x_out X) + 640) = ((x_out X) + (4 * ((160 : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1mm.v (replace)
example
    {sbinv T2 T3 T4 T5 T6 : Type}
    (X : sbinv)
    (s1 : T2)
    (x_out : sbinv → Int)
    (sbd_subframeSize : T3 → Int)
    (x_s : sbinv → T3)
    (sbd_frame_size : T2 → Int)
    (sbd_full_frame_size : T2 → Int)
    (j : T4)
    (length : T5 → Nat)
    (owsA : T5)
    (owsB : T5)
    (owsC : T5)
    (firstn : Int → T6 → T5)
    (sj_msp : T4 → T6)
    (skipn : Int → T6 → T5)
    (h1 : (sbd_subframeSize (x_s X)) = 40)
    (h2 : (sbd_frame_size s1) = (4 * (sbd_subframeSize (x_s X))))
    (h3 : (sbd_full_frame_size s1) = (8 * (sbd_subframeSize (x_s X))))
    (h4 : (length owsA) = 160)
    (h5 : (length owsB) = 160)
    (h6 : (length owsC) = ((2000 - 160) - 160))
    (h7 : (length (firstn 8 (sj_msp j))) = 8)
    (h8 : (length (skipn 8 (sj_msp j))) = 8) :
    ((x_out X) + 1280) = ((x_out X) + (4 * (((Int.toNat 320) : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1mn.v (replace)
example :
    ((Int.toNat 2560) : Nat) = (Int.toNat (4 * ((640 : Nat) : Int))) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1n5.v (replace)
example {T1 : Type} (P : Int) (ctl_depth : T1 → Int) (low : T1) (h1 : 64 ≤ (ctl_depth low)) :
    P = (P + ((0 : Nat) : Int)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Ref/X1na.v (replace)
example
    {T1 : Type}
    (OUT : Int)
    (k : Int)
    (ows : T1)
    (iws : T1)
    (mid : T1)
    (tail : T1)
    (length : T1 → Nat)
    (HOUT_BYTES : Int)
    (h1 : (length ows) = 160)
    (h2 : (((length mid) : Nat) : Int) = ((4 * k) - 640))
    (h3 : (length iws) = 160)
    (h4 : (((length tail) : Nat) : Int) = ((HOUT_BYTES - (4 * k)) - 640)) :
    (OUT + (4 * k)) = ((OUT + 640) + (((length mid) : Nat) : Int)) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Spec/X1nt.v (replace)
example (n : Int) :
    (max 0 n) = (((Int.toNat n) : Nat) : Int) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Spec/X1nt.v (replace)
example (charPtr : Int) (bitPtr : Int) (n : Int) :
    ((bitPtr + n) + (charPtr * 8)) = (((charPtr * 8) + bitPtr) + n) := by
  lia

-- speex/speex_decode_fuzzer_float: lib/Spec/X1qc.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (snd : T1 → Int)
    (p : T1)
    (bg : T1)
    (UNIT : Int)
    (MR : T2 → T3 → T4)
    (st1 : T2)
    (sstart : T4 → Int → Int)
    (g : T3)
    (idx : Int)
    (get_stride : T4 → Int)
    (size_class : T5 → Int)
    (j : T5)
    (k : Int)
    (size : Int)
    (h1 : ((snd p) % 16) = 0)
    (h2 : (sstart (MR st1 g) idx) = (((snd bg) + UNIT) + ((get_stride (MR st1 g)) * idx)))
    (h3 : (Int.fdiv (((snd p) - (snd bg)) - UNIT) UNIT) = ((size_class j) * idx))
    (h4 : (0 ≤ ((size_class j) * idx) ∧ ((size_class j) * idx) < (2 ^ (16 : Nat))))
    (h5 : 0 ≤ (k * size)) :
    ((snd p) - ((snd bg) + UNIT)) = (((snd p) - (snd bg)) - UNIT) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/Drv/S1RLoopN.v (replace)
example
    {list_byte : Type}
    (sp0 : Int)
    (p1 : Int)
    (path : list_byte)
    (len : Int)
    (cap_of : Nat → Int)
    (j : Nat)
    (length : list_byte → Nat)
    (alloc_ceiling : Int)
    (h1 : ((140735340871680 ≤ sp0 ∧ sp0 ≤ 140737488355328) ∧ (sp0 % 16) = 0))
    (h2 : (sp0 ≤ p1 ∧ ((p1 + (((length path) : Nat) : Int)) + 1) < (2 ^ (63 : Nat))))
    (h3 : alloc_ceiling = (sp0 - 8388608))
    (h4 : j = 10)
    (h5 : j < 10) :
    ((Int.toNat len) + (Int.toNat ((cap_of j) - len))) = (Int.toNat (cap_of j)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/Drv/S1TargetBlocks.v (replace)
example
    (sp0 : Int)
    (o : Int)
    (h1 : ((140735340871680 ≤ sp0 ∧ sp0 ≤ 140737488355328) ∧ (sp0 % 16) = 0))
    (h2 : o < 0)
    (h3 : ((o).natAbs : Int) ≤ sp0) :
    (sp0 - ((o).natAbs : Int)) = (sp0 + o) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/Drv/SymExecASound.v (assert)
example
    {T1 T2 : Type}
    (fk : T1)
    (a : T2)
    (m : Int)
    (aligned_dec : T1 → T2 → Int → Bool)
    (h1 : (m = 4 ∨ m = 8))
    (h2 : (aligned_dec fk a m) = true) :
    0 < m := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/Drv/U1TargetRun.v (replace)
example
    (sp0 : Int)
    (buf : Int)
    (cfglen : Int)
    (n : Int)
    (b2 : Int)
    (d : Int)
    (h1 : ((140735340871680 ≤ sp0 ∧ sp0 ≤ 140737488355328) ∧ (sp0 % 16) = 0))
    (h2 : (1196032 ≤ buf ∧ (buf + 3) ≤ (sp0 - 8388608)))
    (h3 : (0 ≤ cfglen ∧ cfglen < 32768))
    (h4 : (0 ≤ n ∧ n < (2 ^ (26 : Nat))))
    (h5 : (0 ≤ b2 ∧ b2 < 256)) :
    ((sp0 - 8388608) + d) = ((sp0 + (-8388608)) + d) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibCont/Lib_Str_Resize.v (replace)
example
    {T1 T2 : Type}
    (len : Int)
    (bytes_le_to_Z : T1 → Int)
    (bs7 : T1)
    (length : T2 → Nat)
    (cs : T2)
    (V : Int)
    (Z_land : Int → Int → Int)
    (h1 : (((length cs) : Nat) : Int) = len)
    (h2 : V = ((2 * len) + (256 * (bytes_le_to_Z bs7))))
    (h3 : (0 ≤ V ∧ V < (2 ^ (64 : Nat))))
    (h4 : (Z_land V 1) = 0) :
    ((len + (128 * (bytes_le_to_Z bs7))) * 2) = ((2 * len) + (256 * (bytes_le_to_Z bs7))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibCont/Lib_Str_Resize.v (replace)
example
    {T1 T2 : Type}
    (p : Int)
    (len : Int)
    (length : T1 → Nat)
    (cs : T1)
    (sp : Int)
    (dat : Int)
    (cap : Int)
    (ch : Int)
    (V : Int)
    (bytes_le_to_Z : T2 → Int)
    (bs7 : T2)
    (Z_land : Int → Int → Int)
    (h1 : (((length cs) : Nat) : Int) = len)
    (h2 : ((p + 24) ≤ (sp - 80) ∨ sp ≤ p))
    (h3 : (0 ≤ dat ∧ ((dat + cap) + 1) ≤ (2 ^ (63 : Nat))))
    (h4 : (((dat + cap) + 1) ≤ (sp - 80) ∨ sp ≤ dat))
    (h5 : (0 ≤ (ch % 256) ∧ (ch % 256) < 256))
    (h6 : V = ((2 * len) + (256 * (bytes_le_to_Z bs7))))
    (h7 : (0 ≤ V ∧ V < (2 ^ (64 : Nat))))
    (h8 : (Z_land V 1) = 0) :
    (p + (1 + len)) = ((p + 1) + len) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibCont/Lib_Vec32_PushBack_697a0.v (replace)
example
    {MallocIface_SEGS_Ly_L T2 : Type}
    (MI : MallocIface_SEGS_Ly_L)
    (b : Int)
    (Zlen : T2 → Int)
    (xs : T2)
    (MALLOC_STACK : MallocIface_SEGS_Ly_L → Int)
    (sp : Int)
    (cap : Int)
    (v : Int)
    (src : Int)
    (h1 : 0 ≤ (MALLOC_STACK MI))
    (h2 : (2 ^ (20 : Nat)) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))))
    (h3 : (0 ≤ cap ∧ cap < (2 ^ (40 : Nat))))
    (h4 : ((v + 24) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))) ∨ sp ≤ v))
    (h5 : ((src + 4) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))) ∨ sp ≤ src))
    (h6 : 0 ≤ b)
    (h7 : (b + (4 * cap)) ≤ (2 ^ (63 : Nat)))
    (h8 : b ≠ 0) :
    ((b + (4 * (Zlen xs))) + 4) = (b + (4 * ((Zlen xs) + 1))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibCont/Lib_Vec32_PushBack_697a0.v (replace)
example
    {MallocIface_SEGS_Ly_L T2 : Type}
    (MI : MallocIface_SEGS_Ly_L)
    (cap : Int)
    (MALLOC_STACK : MallocIface_SEGS_Ly_L → Int)
    (sp : Int)
    (v : Int)
    (src : Int)
    (b : Int)
    (Zlen : T2 → Int)
    (xs : T2)
    (h1 : 0 ≤ (MALLOC_STACK MI))
    (h2 : (2 ^ (20 : Nat)) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))))
    (h3 : (0 ≤ cap ∧ cap < (2 ^ (40 : Nat))))
    (h4 : ((v + 24) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))) ∨ sp ≤ v))
    (h5 : ((src + 4) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))) ∨ sp ≤ src))
    (h6 : 0 ≤ b)
    (h7 : (b + (4 * cap)) ≤ (2 ^ (63 : Nat)))
    (h8 : b ≠ 0)
    (h9 : (Zlen xs) = cap) :
    ((2 * cap) * 2) = (4 * cap) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibCont/Lib_Vec32_PushBack_697a0.v (replace)
example
    {MallocIface_SEGS_Ly_L T2 : Type}
    (MI : MallocIface_SEGS_Ly_L)
    (sp : Int)
    (MALLOC_STACK : MallocIface_SEGS_Ly_L → Int)
    (cap : Int)
    (v : Int)
    (src : Int)
    (b : Int)
    (Zlen : T2 → Int)
    (xs : T2)
    (vgrow : Int → Int)
    (h1 : 0 ≤ (MALLOC_STACK MI))
    (h2 : (2 ^ (20 : Nat)) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))))
    (h3 : (0 ≤ cap ∧ cap < (2 ^ (40 : Nat))))
    (h4 : ((v + 24) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))) ∨ sp ≤ v))
    (h5 : ((src + 4) ≤ (sp - (64 + (16 + (MALLOC_STACK MI)))) ∨ sp ≤ src))
    (h6 : 0 ≤ b)
    (h7 : (b + (4 * cap)) ≤ (2 ^ (63 : Nat)))
    (h8 : b ≠ 0)
    (h9 : (Zlen xs) = cap)
    (h10 : 4 ≤ (4 * (vgrow cap))) :
    (sp - (16 * 4)) = (sp - 64) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibCont/StrLib.v (assert)
example (i : Int) (n : Int) (h1 : (0 ≤ i ∧ i < n)) :
    (Int.toNat i) < (Int.toNat n) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibDiag/DoPutDefsU1.v (replace)
example (f : Int) (nc : Int) :
    ((f - 352) + nc) = (((f - 368) + 16) + nc) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibDiag/PutString.v (replace)
example
    {MallocIface_SEGS_Ly_L : Type}
    (MI : MallocIface_SEGS_Ly_L)
    (sp : Int)
    (XS_STK : MallocIface_SEGS_Ly_L → Int)
    (MALLOC_STACK : MallocIface_SEGS_Ly_L → Int)
    (h1 : (XS_STK MI) = (208 + (16 + (MALLOC_STACK MI)))) :
    16 = (sp - (sp - 16)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibPrs/PmBodyS1.v (replace)
example {T1 : Type} (iwc : Int) (c_widx : T1 → Int) (c : T1) :
    (iwc - 1) = (((c_widx c) + iwc) - ((c_widx c) + 1)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibPrs/PmCoreU1.v (replace)
example
    {T1 T2 T3 : Type}
    (sp0 : Int)
    (M1 : T1)
    (store_ok : T2 → T1 → T3 → Int → Bool)
    (SEGS : T2)
    (Z_to_bv : Int → Int → T3)
    (M2 : T1)
    (M3 : T1)
    (h1 : (store_ok SEGS M1 (Z_to_bv 64 ((sp0 + (-864)) + 752)) 8) = true)
    (h2 : (store_ok SEGS M2 (Z_to_bv 64 ((sp0 + (-864)) + 744)) 8) = true)
    (h3 : (store_ok SEGS M3 (Z_to_bv 64 ((sp0 + (-864)) + 736)) 8) = true) :
    (sp0 - 128) = ((sp0 + (-864)) + 736) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibPrs/PmExitDiagS1.v (replace)
example {T1 T2 : Type} (c_widx : T1 → Int) (c : T1) (i_io : T2 → Int) (I : T2) :
    ((c_widx c) - (i_io I)) = ((c_widx c) + ((-1) * (i_io I))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibPrs/PmExitS1.v (replace)
example
    {T1 : Type}
    (b3 : Int)
    (Zlen : T1 → Int)
    (xs : T1)
    (h1 : (0 ≤ b3 ∧ (b3 + (4 * (Zlen xs))) < (2 ^ (64 : Nat)))) :
    b3 = (b3 + (4 * 0)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/TablByValue.v (replace)
example
    {list_____Z_Z_Z T2 T3 T4 : Type}
    (K : list_____Z_Z_Z)
    (T : list_____Z_Z_Z)
    (f : Int)
    (c : Int)
    (j : Int)
    (byvalue_okb : list_____Z_Z_Z → list_____Z_Z_Z → Bool)
    (Zlen : list_____Z_Z_Z → Int)
    (sorted_adj : T2 → Bool)
    (map : T3 → T4 → T2)
    (v_value : T3)
    (zsub : Int → Int → list_____Z_Z_Z → T4)
    (h1 : (byvalue_okb K T) = true)
    (h2 : 0 ≤ f)
    (h3 : (f + c) ≤ (Zlen T))
    (h4 : (sorted_adj (map v_value (zsub f c T))) = true)
    (h5 : f ≤ j)
    (h6 : (j + 1) < (f + c)) :
    (Int.toNat j) = ((Int.toNat f) + (Int.toNat (j - f))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/TablRep.v (replace)
example
    {list_Segment tabl_img T3 : Type}
    (SEGS : list_Segment)
    (ti : tabl_img)
    (p : Int)
    (n : Int)
    (a : Int)
    (align_dn8 : Int → Int)
    (img_okb : list_Segment → tabl_img → Bool)
    (ti_ro_lo : tabl_img → Int)
    (ti_ro_hi : tabl_img → Int)
    (chk_cstr : list_Segment → tabl_img → Int → Int → Bool)
    (align_up8 : Int → Int)
    (length : T3 → Nat)
    (zs : T3)
    (nth : Nat → T3 → Int → Int)
    (j : Nat)
    (bv_unsigned : Int → Int)
    (bs : T3)
    (Z_to_bv : Int → Int → Int)
    (h1 : (img_okb SEGS ti) = true)
    (h2 : 65536 ≤ (ti_ro_lo ti))
    (h3 : (ti_ro_hi ti) ≤ (2 ^ (40 : Nat)))
    (h4 : (chk_cstr SEGS ti p n) = true)
    (h5 : ((align_dn8 p) ≤ p ∧ (p - 8) < (align_dn8 p)))
    (h6 : (((p + n) + 1) ≤ (align_up8 ((p + n) + 1)) ∧ (align_up8 ((p + n) + 1)) < (((p + n) + 1) + 8)))
    (h7 : (length zs) = (Int.toNat (n + 1)))
    (h8 : (nth j zs 1) = (bv_unsigned (nth j bs (Z_to_bv 8 0))))
    (h9 : (Int.toNat (a - (align_dn8 p))) < (Int.toNat ((align_up8 ((p + n) + 1)) - (align_dn8 p)))) :
    a = ((align_dn8 p) + (a - (align_dn8 p))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/Tabl_StrlenU1.v (lemma)
example (a : Int) (h1 : 0 ≤ a) :
    ((a % 8) = 0 ∨ (a % 8) ≠ 0) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/Tabl_StrlenU1.v (replace)
example
    (p : Int)
    (n : Int)
    (A : Int)
    (i : Nat)
    (dn8 : Int → Int)
    (up8 : Int → Int)
    (h1 : (dn8 p) ≤ A)
    (h2 : (A + 8) ≤ (up8 ((p + n) + 1))) :
    (A + ((i : Nat) : Int)) = (p + ((A + ((i : Nat) : Int)) - p)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/Tabl_TakeP1.v (replace)
example {T1 : Type} (length : T1 → Nat) (ys : T1) :
    (length ys) = (Int.toNat (((((length ys) + 1) : Nat) : Int) - 1)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/LibTabl/Tabl_TakeP1.v (replace)
example {T1 : Type} (b : Int) (Zlen : T1 → Int) (xs : T1) :
    ((b + (4 * (Zlen xs))) + (-4)) = (b + (4 * ((Zlen xs) - 1))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Drv/AsTail_rderr.v (replace)
example
    {word list_byte T3 T4 T5 T6 T7 : Type}
    (sp0 : word)
    (pp : word)
    (path : list_byte)
    (can : Int)
    (lo : Int)
    (hi : Int)
    (vals : list_byte)
    (bv_unsigned : word → Int)
    (RSEGS : T3)
    (length : list_byte → Nat)
    (AAPP_HI : Int)
    (ENV : list_byte → T4)
    (edenot : T4 → T5 → word)
    (EVar : Int → T5)
    (M' : T6)
    (store_ok : T3 → T6 → T7 → Nat → Bool)
    (dst : T7)
    (h1 : (0 ≤ can ∧ can < (2 ^ (64 : Nat))))
    (h2 : (bv_unsigned sp0) ≤ (bv_unsigned pp))
    (h3 : (((bv_unsigned pp) + (((length path) : Nat) : Int)) + 17) ≤ AAPP_HI)
    (h4 : (1 ≤ (((length path) : Nat) : Int) ∧ (((length path) : Nat) : Int) ≤ 61))
    (h5 : (lo ≤ (((length path) : Nat) : Int) ∧ (((length path) : Nat) : Int) ≤ hi))
    (h6 : (length vals) = 195)
    (h7 : (bv_unsigned (edenot (ENV vals) (EVar 141))) < (2 ^ (31 : Nat)))
    (h8 : (store_ok RSEGS M' dst (length path)) = true) :
    ((bv_unsigned sp0) + (-573)) = ((bv_unsigned sp0) - 573) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Drv/AsTargetRun.v (assert)
example (i : Int) (h1 : (0 ≤ i ∧ i < (2 ^ (64 : Nat)))) :
    (0 ≤ i ∧ i < (2 ^ (64 : Nat))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_NtG.v (replace)
example
    {list_type___Z___Z_____Z_Z_Z : Type}
    (S1 : Int)
    (obj : Int)
    (ents : list_type___Z___Z_____Z_Z_Z)
    (bc : Int)
    (lo : Int)
    (B : Int)
    (shi : Int)
    (BSEQ_LAST : Int)
    (aceil : Int)
    (ANT_STACK : Int)
    (Zlength : list_type___Z___Z_____Z_Z_Z → Int)
    (h1 : bc ≠ BSEQ_LAST)
    (h2 : (obj + 40) ≤ aceil)
    (h3 : aceil ≤ lo)
    (h4 : lo ≤ S1)
    (h5 : lo ≤ (S1 - ANT_STACK))
    (h6 : ((Zlength ents) + 1) < (2 ^ (24 : Nat)))
    (h7 : (S1 % 16) = 0)
    (h8 : (S1 + 1040) ≤ B)
    (h9 : B < (2 ^ (64 : Nat)))
    (h10 : (S1 + 1040) ≤ shi)
    (h11 : 3 ≤ bc)
    (h12 : (Zlength ents) = bc) :
    (bc + (-1)) = (bc - 1) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_PcXspS.v (replace)
example
    {asr word as_St_H T4 T5 : Type}
    (H : asr)
    (ra : word)
    (sp : word)
    (s : as_St_H)
    (lo : Int)
    (B : Int)
    (shi : Int)
    (len : Int)
    (n : Int)
    (si : as_St_H)
    (msi : T4)
    (ppi : Int)
    (bv_unsigned : word → Int)
    (aceil : Int)
    (XSP_STACK : Int)
    (DS_MAXLEN : Int)
    (ds_cost : Int → Int)
    (as_AL : asr → as_St_H → Int)
    (epof : T4 → Int)
    (c : Int)
    (PropExec_getr : T5 → Int → word)
    (R1 : T5)
    (ICM : Int → Int)
    (str_grow : T4 → Int)
    (blkof : T4 → Int)
    (h1 : (bv_unsigned sp) ≤ B)
    (h2 : B < (2 ^ (64 : Nat)))
    (h3 : ((bv_unsigned sp) % 16) = 0)
    (h4 : aceil ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - XSP_STACK))
    (h6 : ((bv_unsigned ra) % 2) = 0)
    (h7 : (bv_unsigned sp) ≤ shi)
    (h8 : 0 < n)
    (h9 : (len + n) ≤ DS_MAXLEN)
    (h10 : (ds_cost (len + n)) ≤ (as_AL H s))
    (h11 : (epof msi) ≤ ppi)
    (h12 : ppi = (epof msi))
    (h13 : (0 ≤ c ∧ c ≤ 255))
    (h14 : aceil ≤ (bv_unsigned sp))
    (h15 : (bv_unsigned (PropExec_getr R1 2)) = ((bv_unsigned sp) - 64))
    (h16 : ((ICM (str_grow msi)) ≤ (as_AL H si) ∧ ((8 * (blkof msi)) + (ICM (str_grow msi))) ≤ (8 * (str_grow msi)))) :
    (((bv_unsigned sp) - 64) + 64) = (((bv_unsigned sp) + (-64)) + (0 - (-64))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_PcXspS.v (replace)
example
    {asr word as_St_H T4 T5 : Type}
    (H : asr)
    (ra : word)
    (sp : word)
    (s : as_St_H)
    (lo : Int)
    (B : Int)
    (shi : Int)
    (len : Int)
    (n : Int)
    (si : as_St_H)
    (msi : T4)
    (ppi : Int)
    (bv_unsigned : word → Int)
    (aceil : Int)
    (XSP_STACK : Int)
    (DS_MAXLEN : Int)
    (ds_cost : Int → Int)
    (as_AL : asr → as_St_H → Int)
    (epof : T4 → Int)
    (c : Int)
    (PropExec_getr : T5 → Int → word)
    (R1 : T5)
    (ICM : Int → Int)
    (str_grow : T4 → Int)
    (blkof : T4 → Int)
    (h1 : (bv_unsigned sp) ≤ B)
    (h2 : B < (2 ^ (64 : Nat)))
    (h3 : ((bv_unsigned sp) % 16) = 0)
    (h4 : aceil ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - XSP_STACK))
    (h6 : ((bv_unsigned ra) % 2) = 0)
    (h7 : (bv_unsigned sp) ≤ shi)
    (h8 : 0 < n)
    (h9 : (len + n) ≤ DS_MAXLEN)
    (h10 : (ds_cost (len + n)) ≤ (as_AL H s))
    (h11 : (epof msi) ≤ ppi)
    (h12 : ppi = (epof msi))
    (h13 : (0 ≤ c ∧ c ≤ 255))
    (h14 : aceil ≤ (bv_unsigned sp))
    (h15 : (bv_unsigned (PropExec_getr R1 2)) = ((bv_unsigned sp) - 64))
    (h16 : ((ICM (str_grow msi)) ≤ (as_AL H si) ∧ ((8 * (blkof msi)) + (ICM (str_grow msi))) ≤ (8 * (str_grow msi)))) :
    ((bv_unsigned sp) - 64) = ((bv_unsigned sp) + (-64)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_PmCall.v (replace)
example
    (a : Int)
    (sh : Int → Int)
    (ff : Int)
    (hull_lo : Int → Int)
    (k : Int)
    (hull_hi : Int → Int)
    (n : Int)
    (AAPP_HI : Int)
    (h1 : ff ≤ (hull_lo (ff + k)))
    (h2 : ((ff + k) % 64) = (k % 64))
    (h3 : (hull_hi ((ff + k) + n)) ≤ (ff + 15616))
    (h4 : (((ff + k) + n) % 64) = ((k + n) % 64))
    (h5 : ((k + n) + ((64 - ((k + n) % 64)) % 64)) ≤ 15616)
    (h6 : (15616 : Int) = (244 * 64))
    (h7 : (hull_hi ((ff + k) + n)) ≤ AAPP_HI)
    (h8 : ((hull_hi ((ff + k) + n)) / 8) ≤ ((2 ^ (47 : Nat)) / 8))
    (h9 : (sh ff) ≤ (sh (hull_lo (ff + k))))
    (h10 : (sh (hull_hi ((ff + k) + n))) ≤ ((sh ff) + 1952))
    (h11 : (sh (hull_hi ((ff + k) + n))) ≤ (sh (ff + 15616)))
    (h12 : (sh (ff + 15616)) = ((sh ff) + 1952)) :
    a = ((sh ff) + (a - (sh ff))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_PmOwn.v (replace)
example
    {T1 : Type}
    (wa_ff : T1 → Int)
    (w : T1)
    (wa_cons : T1 → Int)
    (aceil : Int)
    (sh : Int → Int)
    (AIMG_TOP : Int)
    (h1 : ((wa_cons w) + 48) ≤ aceil)
    (h2 : (sh AIMG_TOP) ≤ (sh (wa_ff w))) :
    ((wa_ff w) + 0) = (wa_ff w) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_PmWG.v (replace)
example {T1 : Type} (wa_p : T1 → Int) (w : T1) (ho : Int) :
    24 = ((((wa_p w) + ho) + 24) - ((wa_p w) + ho)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_PmXv.v (replace)
example
    {T1 T2 T3 : Type}
    (wa_p : T1 → Int)
    (w : T1)
    (H : T2)
    (wa_ff : T1 → Int)
    (sh : Int → Int)
    (as_FSB : T2 → Int)
    (AFS_SIZE : Int)
    (wa_sp0 : T1 → Int)
    (blk_addr : T3 → Int)
    (b : T3)
    (a : Int)
    (blk_size : T3 → Int)
    (nsh : Int → Int)
    (fp : Int)
    (h1 : (sh ((wa_ff w) + 15616)) ≤ (sh ((as_FSB H) + AFS_SIZE)))
    (h2 : ((sh (wa_ff w)) + 1952) = (sh ((wa_ff w) + 15616)))
    (h3 : ((blk_addr b) ≤ a ∧ a < ((blk_addr b) + (blk_size b))))
    (h4 : ((sh (blk_addr b)) ≤ a ∧ a < ((sh (blk_addr b)) + (nsh (blk_size b)))))
    (h5 : (wa_sp0 w) ≤ fp) :
    ((wa_p w) + 0) = (wa_p w) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_TablLO.v (replace)
example
    {T1 T2 T3 : Type}
    (lo : Int)
    (a : Int)
    (i : Int)
    (E : T1)
    (bv_unsigned : T2 → Int)
    (edenot : T1 → T3 → T2)
    (EVar : Int → T3)
    (sp : Int)
    (h1 : (bv_unsigned (edenot E (EVar 34))) = sp) :
    (lo + ((a - lo) + i)) = (a + i) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_TablXPs.v (replace)
example {T1 T2 : Type} (x_ff : T1 → Int) (e : T1) (xs_src : T2 → Int) (s : T2) :
    (((x_ff e) + (xs_src s)) + 4) = (((x_ff e) + (xs_src s)) + 4) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Lib/LbA_WoSt2.v (replace)
example
    {T1 : Type}
    (wS1 : T1 → Int)
    (e : T1)
    (w_words : T1 → Int)
    (h1 : (0 ≤ (w_words e) ∧ (w_words e) < (2 ^ (64 : Nat)))) :
    ((wS1 e) + 288) = ((((wS1 e) + 240) + ((24 : Nat) : Int)) + ((24 : Nat) : Int)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Rt/AG_RecycleSec1.v (replace)
example (pa : Int) (nch : Int) :
    (pa + (8 * nch)) = ((pa + (8 * (nch - 1))) + (8 * (nch - (nch - 1)))) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Rt/AS_Refill1.v (replace)
example
    {word list_Z T3 : Type}
    (sp : word)
    (tp : word)
    (lo : Int)
    (sb : Int)
    (c : Int)
    (CA : Int)
    (TH : Int)
    (nf : Int)
    (mfa : Int)
    (au : Int)
    (mu : Int)
    (fl : list_Z)
    (R : Int)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (AHI_LO : Int)
    (kSpaceSize : Int)
    (kPageSize : Int)
    (AIMG_TOP : Int)
    (kFreeArraySize : Int)
    (kUserMapSize : Int)
    (kFreeArrayOffset : Int)
    (length : list_Z → Nat)
    (wlist : T3 → list_Z)
    (rev : list_Z → T3)
    (n : Int)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 640) ≤ (bv_unsigned sp))
    (h3 : ((bv_unsigned sp) + 16) ≤ (2 ^ (47 : Nat)))
    (h4 : (1 ≤ c ∧ c ≤ 30))
    (h5 : CA = (TH + 208))
    (h6 : (AHI_LO ≤ sb ∧ ((sb + kSpaceSize) + kPageSize) ≤ aceil))
    (h7 : (6755912 ≤ (bv_unsigned tp) ∧ ((bv_unsigned tp) + 4096) ≤ AIMG_TOP))
    (h8 : (0 ≤ nf ∧ ((4 * nf) ≤ mfa ∧ mfa ≤ kFreeArraySize)))
    (h9 : ((0 ≤ au ∧ au ≤ mu) ∧ (mu + kUserMapSize) ≤ kFreeArrayOffset))
    (h10 : (length fl) = (Int.toNat nf))
    (h11 : (((length (wlist (rev fl))) : Nat) : Int) = nf)
    (h12 : n ≤ nf) :
    (R + 16) = ((R + 8) + ((8 : Nat) : Int)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Rt/AS_Refill1.v (replace)
example
    {word list_Z T3 : Type}
    (sp : word)
    (tp : word)
    (lo : Int)
    (sb : Int)
    (c : Int)
    (CA : Int)
    (TH : Int)
    (nf : Int)
    (mfa : Int)
    (au : Int)
    (mu : Int)
    (fl : list_Z)
    (R : Int)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (AHI_LO : Int)
    (kSpaceSize : Int)
    (kPageSize : Int)
    (AIMG_TOP : Int)
    (kFreeArraySize : Int)
    (kUserMapSize : Int)
    (kFreeArrayOffset : Int)
    (length : list_Z → Nat)
    (wlist : T3 → list_Z)
    (rev : list_Z → T3)
    (n : Int)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 640) ≤ (bv_unsigned sp))
    (h3 : ((bv_unsigned sp) + 16) ≤ (2 ^ (47 : Nat)))
    (h4 : (1 ≤ c ∧ c ≤ 30))
    (h5 : CA = (TH + 208))
    (h6 : (AHI_LO ≤ sb ∧ ((sb + kSpaceSize) + kPageSize) ≤ aceil))
    (h7 : (6755912 ≤ (bv_unsigned tp) ∧ ((bv_unsigned tp) + 4096) ≤ AIMG_TOP))
    (h8 : (0 ≤ nf ∧ ((4 * nf) ≤ mfa ∧ mfa ≤ kFreeArraySize)))
    (h9 : ((0 ≤ au ∧ au ≤ mu) ∧ (mu + kUserMapSize) ≤ kFreeArrayOffset))
    (h10 : (length fl) = (Int.toNat nf))
    (h11 : (((length (wlist (rev fl))) : Nat) : Int) = nf)
    (h12 : n ≤ nf) :
    (R + 24) = (((R + 8) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Rt/AW_MallocRet.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (bv_unsigned : word → Int)
    (aceil : Int)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 2496) ≤ (bv_unsigned sp))
    (h3 : ((bv_unsigned sp) + 16) ≤ (2 ^ (47 : Nat))) :
    ((bv_unsigned sp) + (-64)) = (((bv_unsigned sp) + (-72)) + ((8 : Nat) : Int)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Rt/F_strlen.v (replace)
example
    {word list_byte : Type}
    (a0 : word)
    (str : list_byte)
    (slack : list_byte)
    (bv_unsigned : word → Int)
    (i : Int)
    (length : list_byte → Nat)
    (h1 : ((-(((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h2 : i = (((length str) : Nat) : Int)) :
    (((bv_unsigned a0) + (i + 1)) - 1) = ((((bv_unsigned a0) + i) - 1) + 1) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Rt/N6_imm.v (replace)
example (i : Int) :
    (Int.toNat ((i - 1) + 1)) = (Int.toNat i) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Rt/N6_imm.v (replace)
example
    {word list_byte : Type}
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (src : list_byte)
    (length : list_byte → Nat)
    (bv_unsigned : word → Int)
    (h1 : (length src) = (Int.toNat (bv_unsigned a2)))
    (h2 : (((bv_unsigned a1) + (bv_unsigned a2)) ≤ (bv_unsigned a0) ∨ ((bv_unsigned a0) + (bv_unsigned a2)) ≤ (bv_unsigned a1)))
    (h3 : (bv_unsigned a2) < (2 ^ (63 : Nat)))
    (h4 : (((bv_unsigned a0) + (bv_unsigned a2)) < (2 ^ (64 : Nat)) ∧ ((bv_unsigned a1) + (bv_unsigned a2)) < (2 ^ (64 : Nat)))) :
    (length src) = (Int.toNat (((bv_unsigned a2) - 1) + 1)) := by
  lia

-- spirv-tools/spvtools_binary_parser_fuzzer: lib/bpA/Start/AxSymExec3Sound.v (replace)
example
    {T1 T2 T3 : Type}
    (k : Int)
    (uE : T1 → T2 → Int)
    (E : T1)
    (a : T2)
    (c : Int)
    (tden : T1 → T3 → Int)
    (rest : T3) :
    ((k * (uE E a)) + (c + (tden E rest))) = (c + ((k * (uE E a)) + (tden E rest))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/A/Asan_memset_contract.v (replace)
example
    {T1 : Type}
    (UU : T1 → Int → Int)
    (rho : T1)
    (ACEIL : Int)
    (h1 : ((UU rho 53) % 8) = 0)
    (h2 : (ACEIL + 2304) ≤ (UU rho 10)) :
    ((((UU rho 10) + (UU rho 15)) - (2 ^ (64 : Nat))) + (1 * (2 ^ (64 : Nat)))) = ((UU rho 10) + (UU rho 15)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/A/Lib_handle_f_shx.v (replace)
example
    {T1 T2 T3 : Type}
    (off : Int)
    (len : Int)
    (p : Int)
    (sz : Int)
    (Sh : Int → Int)
    (bv_unsigned : T1 → Int)
    (rw : T2 → T3 → T1)
    (rho : T2)
    (g : T3)
    (pR : T3)
    (a : Int)
    (q : Int)
    (b : Int)
    (expected_sh : Int → Int → Int → Int)
    (h1 : ((p % 8) : Int) = 0)
    (h2 : ((sz % 8) : Int) = 0)
    (h3 : (((Sh p) % 8) : Int) = 0)
    (h4 : (((sz / 8) % 8) : Int) = 0)
    (h5 : ((0 : Int) ≤ p ∧ ((p + sz) : Int) ≤ (2 ^ (47 : Nat))))
    (h6 : ((bv_unsigned (rw rho g)) : Int) = (p / 8))
    (h7 : ((bv_unsigned (rw rho pR)) : Int) = p)
    (h8 : ((off + len) : Int) ≤ sz)
    (h9 : ((a / 8) : Int) = ((p / 8) + q))
    (h10 : (((off / 8) : Int) ≤ q ∧ (q : Int) < (((off + len) + 7) / 8)))
    (h11 : (((Sh p) : Int) ≤ (Sh a) ∧ ((Sh a) : Int) < ((Sh p) + (sz / 8))))
    (h12 : ((b : Int) = (expected_sh off len q) ∨ (b : Int) = 0))
    (h13 : ((Sh a) : Int) = ((Sh p) + q))
    (h14 : ((0 : Int) ≤ ((off + len) % 8) ∧ (((off + len) % 8) : Int) < 8))
    (h15 : (q : Int) = ((off + len) / 8)) :
    (((off + len) + p) : Int) = ((p + off) + len) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/A/Start6.v (replace)
example
    {T1 : Type}
    (G : Int)
    (x : Int)
    (LIMz : Int → Int)
    (x4 : Int)
    (topZ : Int → Int)
    (T : Int)
    (V79 : Int)
    (V80 : Int)
    (shx : Int → Int)
    (x8 : Int)
    (e12x : Int → Int)
    (r4 : Int)
    (q12x : Int → Int)
    (r5 : Int)
    (HPz : Int → Int)
    (PEz : Int → Int)
    (PBz : Int → Int)
    (PB : T1 → Int)
    (t : T1)
    (h1 : (x % 8) = 0)
    (h2 : (LIMz x) = (((512 * x4) + 2147450880) - 1048576))
    (h3 : (topZ x) = (4096 * T))
    (h4 : V79 = (32768 * (G - 256)))
    (h5 : V80 = (4096 * (G - 256)))
    (h6 : (shx x) = (x8 + 2147450880))
    (h7 : (e12x x) = (((shx x) - 9) - r4))
    (h8 : (q12x x) = (((shx x) - 131072) - r5))
    (h9 : (HPz x) = (V80 + 2147450880))
    (h10 : (PEz x) = (V80 + 2148499456))
    (h11 : (PBz x) = (V80 + (PB t)))
    (h12 : (T = x4 ∨ T = (x4 + 1)))
    (h13 : (V79 % 32768) = 0)
    (h14 : (V80 % 4096) = 0)
    (h15 : ((topZ x) % 4096) = 0)
    (h16 : ((HPz x) % 4096) = 0) :
    (((G - 256) + 524280) * 4096) = ((4096 * (G - 256)) + 2147450880) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/A/Start6.v (replace)
example
    {T1 : Type}
    (G : Int)
    (x : Int)
    (LIMz : Int → Int)
    (x4 : Int)
    (topZ : Int → Int)
    (T : Int)
    (V79 : Int)
    (V80 : Int)
    (shx : Int → Int)
    (x8 : Int)
    (e12x : Int → Int)
    (r4 : Int)
    (q12x : Int → Int)
    (r5 : Int)
    (HPz : Int → Int)
    (PEz : Int → Int)
    (PBz : Int → Int)
    (PB : T1 → Int)
    (t : T1)
    (h1 : (x % 8) = 0)
    (h2 : (LIMz x) = (((512 * x4) + 2147450880) - 1048576))
    (h3 : (topZ x) = (4096 * T))
    (h4 : V79 = (32768 * (G - 256)))
    (h5 : V80 = (4096 * (G - 256)))
    (h6 : (shx x) = (x8 + 2147450880))
    (h7 : (e12x x) = (((shx x) - 9) - r4))
    (h8 : (q12x x) = (((shx x) - 131072) - r5))
    (h9 : (HPz x) = (V80 + 2147450880))
    (h10 : (PEz x) = (V80 + 2148499456))
    (h11 : (PBz x) = (V80 + (PB t)))
    (h12 : (T = x4 ∨ T = (x4 + 1)))
    (h13 : (V79 % 32768) = 0)
    (h14 : (V80 % 4096) = 0)
    (h15 : ((topZ x) % 4096) = 0)
    (h16 : ((HPz x) % 4096) = 0)
    (h17 : ((PEz x) % 4096) = 0) :
    (((G - 256) + 524536) * 4096) = ((4096 * (G - 256)) + 2148499456) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/A/fv.v (replace)
example (k : Nat) (k1 : Nat) :
    0 = ((min k k1) - k1) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/B/Start7.v (replace)
example
    {T1 : Type}
    (te : Int)
    (tq : Int)
    (rho0 : T1)
    (x : Int)
    (n12 : T1 → Nat)
    (h1 : (17591917608960 ≤ (x / 8) ∧ (x / 8) ≤ 17592186044416))
    (h2 : (((n12 rho0) : Nat) : Int) = ((te - tq) + 1)) :
    ((te - tq) * 4096) = ((te * 4096) - (tq * 4096)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/B/StartHandoff.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (StartArgBytes_RNDo : T2 → Int)
    (inp : T2)
    (k : Int) :
    (((bv_unsigned sp) + (StartArgBytes_RNDo inp)) + k) = ((((bv_unsigned sp) + (StartArgBytes_RNDo inp)) + 8) + (k - 8)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/B/StartHandoff.v (replace)
example (q : Int) (XEz : Int) (h1 : (XEz / 8) = (8 * q)) :
    ((8 * q) * 8) = (64 * q) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/B/no.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (uval : T1 → T2 → Int)
    (rho : T1)
    (SVar : Int → T2)
    (vDp : T2)
    (bv_unsigned : T3 → Int)
    (rw : T1 → T4 → T3)
    (V_TOP : T4)
    (SAlu : T5 → T6 → T2 → T2)
    (ALU_ADD : T5)
    (spm : Int → T6)
    (h1 : ((uval rho (SVar 30)) : Int) = (bv_unsigned (rw rho V_TOP)))
    (h2 : ((uval rho (SAlu ALU_ADD (spm 64) vDp)) : Int) = (((uval rho (SVar 10)) - 64) + ((uval rho vDp) - (2 ^ (64 : Nat))))) :
    (((((uval rho (SVar 10)) - 64) + ((uval rho vDp) - (2 ^ (64 : Nat)))) + (1 * (2 ^ (64 : Nat)))) : Int) = (((uval rho (SVar 10)) - 64) + (uval rho vDp)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/B/o1.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (eval : T2 → T3 → T1)
    (rho : T2)
    (vK : T3)
    (vQ : T3)
    (uval : T2 → T3 → Int)
    (kb16 : T3 → T3)
    (vKn : T3)
    (q1 : T3)
    (h1 : (uval rho (kb16 vQ)) = (16 * (uval rho vQ)))
    (h2 : (uval rho (kb16 vK)) = (16 * (uval rho vK)))
    (h3 : (uval rho (kb16 vKn)) = (16 * (uval rho vKn)))
    (h4 : (uval rho q1) = ((uval rho vQ) + 1))
    (h5 : (uval rho (kb16 q1)) = ((16 * (uval rho vQ)) + 16)) :
    ((((16 * (bv_unsigned (eval rho vK))) - (16 * (bv_unsigned (eval rho vQ)))) - 16) + (1 * 18446744073709551616)) = (((16 * (bv_unsigned (eval rho vK))) - (16 * (bv_unsigned (eval rho vQ)))) + 18446744073709551600) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Fw3/SymSoundA.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (v : T1) :
    ((bv_unsigned v) + ((-1) * (2 ^ (64 : Nat)))) = (((bv_unsigned v) - (2 ^ (63 : Nat))) - (2 ^ (63 : Nat))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Fw3/SymSoundL.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (eval : T2 → T3 → T1)
    (rho : T2)
    (o : T3)
    (b : T3) :
    (bv_unsigned (eval rho o)) = (((bv_unsigned (eval rho b)) + (bv_unsigned (eval rho o))) - (bv_unsigned (eval rho b))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Fw3/SymSoundV.v (replace)
example (u : Int) (kx : Int) (ky : Int) :
    ((u + kx) - (u + ky)) = (kx - ky) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Fw3/SymSoundW.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (b : Int)
    (lo : Int)
    (esz : Int)
    (k : Int)
    (fst : T1 → Int)
    (f : T1)
    (j : Nat)
    (bv_unsigned : T2 → Int)
    (eval : T3 → T4 → T2)
    (rho : T3)
    (cnt : T4)
    (h1 : ((esz * k) + esz) ≤ (esz * (bv_unsigned (eval rho cnt))))
    (h2 : 0 ≤ (esz * k)) :
    (b + (((lo + (esz * k)) + (fst f)) + ((j : Nat) : Int))) = ((((b + lo) + (esz * k)) + (fst f)) + ((j : Nat) : Int)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Fw3A/StepA.v (replace)
example
    {T1 T2 T3 : Type}
    (U : T1 → T2 → Int)
    (rho : T1)
    (off : T2)
    (j : Nat)
    (k : Nat)
    (msz : T3 → Int)
    (sz : T3)
    (h1 : (((k : Nat) : Int) = (msz sz) ∧ (0 < (msz sz) ∧ (msz sz) ≤ 8))) :
    (((U rho off) + ((j : Nat) : Int)) * 8) = ((8 * (U rho off)) + (8 * ((j : Nat) : Int))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Fw3A/StepA.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (Wq : Int)
    (j : Nat)
    (U : T1 → T2 → Int)
    (rho : T1)
    (w : T2)
    (off : T2)
    (bv_unsigned : T3 → Int)
    (eval : T1 → T2 → T3)
    (SLit : Int → T2)
    (bz : Int)
    (lz : Int)
    (tz : Int)
    (a : Int)
    (ax_base : T4 → T2)
    (A : T4)
    (SAlu : T5 → T2 → T2 → T2)
    (ALU_ADD : T5)
    (b : T2)
    (l : T2)
    (ae : T2)
    (v : T3)
    (h1 : ((U rho w) / 8) = (U rho off))
    (h2 : (bv_unsigned (eval rho (SLit bz))) = (Int.fmod bz (2 ^ (64 : Nat))))
    (h3 : (bv_unsigned (eval rho (SLit lz))) = (Int.fmod lz (2 ^ (64 : Nat))))
    (h4 : (tz ≤ (a / 8) ∧ (a / 8) ≤ (tz + 7)))
    (h5 : (U rho (SLit tz)) = tz)
    (h6 : ((((bv_unsigned (eval rho (ax_base A))) + tz) / 8) * 8) = ((bv_unsigned (eval rho (ax_base A))) + tz))
    (h7 : ((((bv_unsigned (eval rho (ax_base A))) + (a / 8)) / 8) * 8) = ((bv_unsigned (eval rho (ax_base A))) + tz))
    (h8 : ((a / 8) / 8) = (tz / 8))
    (h9 : (U rho (SAlu ALU_ADD b l)) = ((U rho b) + (U rho l)))
    (h10 : (U rho b) ≤ (64 * Wq))
    (h11 : ((64 * Wq) + 64) ≤ (U rho (SAlu ALU_ADD b l)))
    (h12 : (bv_unsigned (eval rho ae)) = ((bv_unsigned (eval rho (ax_base A))) + (8 * Wq)))
    (h13 : (bv_unsigned v) = 0) :
    (((8 * Wq) + ((j : Nat) : Int)) * 8) = ((64 * Wq) + (8 * ((j : Nat) : Int))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Lib/InitLayout.v (replace)
example (a : Int) (b : Int) (c : Int) (M : Int) (h1 : M ≠ 0) :
    ((Int.fmod b M) + (a + c)) = ((a + (Int.fmod b M)) + c) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/LibB/TobjJAS.v (replace)
example
    {T1 T2 T3 : Type}
    (off : Int)
    (len : Int)
    (p : Int)
    (sz : Int)
    (Sh : Int → Int)
    (bv_unsigned : T1 → Int)
    (rw : T2 → T3 → T1)
    (rho : T2)
    (g : T3)
    (pR : T3)
    (a : Int)
    (q : Int)
    (h1 : ((p % 8) : Int) = 0)
    (h2 : ((sz % 8) : Int) = 0)
    (h3 : (((Sh p) % 8) : Int) = 0)
    (h4 : (((sz / 8) % 8) : Int) = 0)
    (h5 : ((0 : Int) ≤ p ∧ ((p + sz) : Int) ≤ (2 ^ (47 : Nat))))
    (h6 : ((bv_unsigned (rw rho g)) : Int) = (p / 8))
    (h7 : ((bv_unsigned (rw rho pR)) : Int) = p)
    (h8 : ((off + len) : Int) ≤ sz)
    (h9 : ((a / 8) : Int) = ((p / 8) + q))
    (h10 : (((off / 8) : Int) ≤ q ∧ (q : Int) < (((off + len) + 7) / 8)))
    (h11 : (((Sh p) : Int) ≤ (Sh a) ∧ ((Sh a) : Int) < ((Sh p) + (sz / 8))))
    (h12 : ((Sh a) : Int) = ((Sh p) + q))
    (h13 : ((0 : Int) ≤ ((off + len) % 8) ∧ (((off + len) % 8) : Int) < 8))
    (h14 : (q : Int) = ((off + len) / 8)) :
    (((off + len) + p) : Int) = ((p + off) + len) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Malloc/BlockView.v (replace)
example
    {T1 T2 : Type}
    (stride_of : T1 → Int)
    (am : T1)
    (am_last : T1 → Int)
    (zP : Int)
    (zMem : Int)
    (sti : Int)
    (fr_off : T2 → Int)
    (fr : T2)
    (h16 : Int)
    (am_maplen : T1 → Int)
    (st : Int)
    (h1 : zP = (((zMem + 16) + sti) + (16 * (fr_off fr))))
    (h2 : zMem = ((zP - (16 * h16)) - 16))
    (h3 : (am_maplen am) < (2 ^ (35 : Nat)))
    (h4 : (0 ≤ sti ∧ (sti + st) ≤ (st * ((am_last am) + 1)))) :
    (((stride_of am) * (am_last am)) + (stride_of am)) = ((stride_of am) * ((am_last am) + 1)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Malloc/SlotZone.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (stride_of : T1 → Int)
    (aq : T1)
    (j0 : Int)
    (j : Int)
    (am_last : T1 → Int)
    (addr_of : T2 → T3 → Int)
    (L : T2)
    (slot_start : T1 → Int → T3)
    (ly_reg : T2 → T4 → Int)
    (prid : T3 → T4)
    (am_mem : T1 → T3)
    (poff : T3 → Int)
    (am' : T1)
    (i : Int)
    (h1 : (0 ≤ ((stride_of aq) * j) ∧ (((stride_of aq) * j) + (stride_of aq)) ≤ ((stride_of aq) * ((am_last aq) + 1))))
    (h2 : (addr_of L (slot_start aq j)) = ((ly_reg L (prid (am_mem aq))) + (poff (slot_start aq j))))
    (h3 : (addr_of L (am_mem am')) = ((ly_reg L (prid (am_mem am'))) + (poff (am_mem am'))))
    (h4 : i ≠ j)
    (h5 : ((i + 1) ≤ j ∨ (j + 1) ≤ i))
    (h6 : ((stride_of aq) * (i + 1)) ≤ ((stride_of aq) * j))
    (h7 : ((stride_of aq) * (j + 1)) ≤ ((stride_of aq) * i))
    (h8 : j0 ≠ j)
    (h9 : (0 ≤ ((stride_of am') * i) ∧ (((stride_of am') * i) + (stride_of am')) ≤ ((stride_of am') * ((am_last am') + 1))))
    (h10 : ((((stride_of aq) * j0) + (stride_of aq)) ≤ ((stride_of aq) * j) ∨ (((stride_of aq) * j) + (stride_of aq)) ≤ ((stride_of aq) * j0)))
    (h11 : ((j0 + 1) ≤ j ∨ (j + 1) ≤ j0)) :
    ((stride_of aq) * (j0 + 1)) = (((stride_of aq) * j0) + (stride_of aq)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Malloc/SlotZone.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (stride_of : T1 → Int)
    (aq : T1)
    (j : Int)
    (am_last : T1 → Int)
    (addr_of : T2 → T3 → Int)
    (L : T2)
    (slot_start : T1 → Int → T3)
    (ly_reg : T2 → T4 → Int)
    (prid : T3 → T4)
    (am_mem : T1 → T3)
    (poff : T3 → Int)
    (am' : T1)
    (i : Int)
    (j0 : Int)
    (h1 : (0 ≤ ((stride_of aq) * j) ∧ (((stride_of aq) * j) + (stride_of aq)) ≤ ((stride_of aq) * ((am_last aq) + 1))))
    (h2 : (addr_of L (slot_start aq j)) = ((ly_reg L (prid (am_mem aq))) + (poff (slot_start aq j))))
    (h3 : (addr_of L (am_mem am')) = ((ly_reg L (prid (am_mem am'))) + (poff (am_mem am'))))
    (h4 : i ≠ j)
    (h5 : ((i + 1) ≤ j ∨ (j + 1) ≤ i))
    (h6 : ((stride_of aq) * (i + 1)) ≤ ((stride_of aq) * j))
    (h7 : ((stride_of aq) * (j + 1)) ≤ ((stride_of aq) * i))
    (h8 : j0 ≠ j)
    (h9 : (0 ≤ ((stride_of am') * i) ∧ (((stride_of am') * i) + (stride_of am')) ≤ ((stride_of am') * ((am_last am') + 1))))
    (h10 : ((((stride_of aq) * j0) + (stride_of aq)) ≤ ((stride_of aq) * j) ∨ (((stride_of aq) * j) + (stride_of aq)) ≤ ((stride_of aq) * j0)))
    (h11 : ((j0 + 1) ≤ j ∨ (j + 1) ≤ j0)) :
    ((stride_of aq) * (j + 1)) = (((stride_of aq) * j) + (stride_of aq)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Malloc/SlotZone.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (stride_of : T1 → Int)
    (am' : T1)
    (i : Int)
    (aq : T1)
    (j : Int)
    (am_last : T1 → Int)
    (addr_of : T2 → T3 → Int)
    (L : T2)
    (slot_start : T1 → Int → T3)
    (ly_reg : T2 → T4 → Int)
    (prid : T3 → T4)
    (am_mem : T1 → T3)
    (poff : T3 → Int)
    (j0 : Int)
    (J : Int)
    (h1 : (0 ≤ ((stride_of aq) * j) ∧ (((stride_of aq) * j) + (stride_of aq)) ≤ ((stride_of aq) * ((am_last aq) + 1))))
    (h2 : (addr_of L (slot_start aq j)) = ((ly_reg L (prid (am_mem aq))) + (poff (slot_start aq j))))
    (h3 : (addr_of L (am_mem am')) = ((ly_reg L (prid (am_mem am'))) + (poff (am_mem am'))))
    (h4 : i ≠ j)
    (h5 : ((i + 1) ≤ j ∨ (j + 1) ≤ i))
    (h6 : ((stride_of aq) * (i + 1)) ≤ ((stride_of aq) * j))
    (h7 : ((stride_of aq) * (j + 1)) ≤ ((stride_of aq) * i))
    (h8 : j0 ≠ j)
    (h9 : (0 ≤ ((stride_of am') * i) ∧ (((stride_of am') * i) + (stride_of am')) ≤ ((stride_of am') * ((am_last am') + 1))))
    (h10 : ((((stride_of aq) * j0) + (stride_of aq)) ≤ ((stride_of aq) * j) ∨ (((stride_of aq) * j) + (stride_of aq)) ≤ ((stride_of aq) * j0)))
    (h11 : ((j0 + 1) ≤ j ∨ (j + 1) ≤ j0))
    (h12 : i ≠ J)
    (h13 : (0 ≤ ((stride_of am') * J) ∧ (((stride_of am') * J) + (stride_of am')) ≤ ((stride_of am') * ((am_last am') + 1))))
    (h14 : ((((stride_of am') * i) + (stride_of am')) ≤ ((stride_of am') * J) ∨ (((stride_of am') * J) + (stride_of am')) ≤ ((stride_of am') * i)))
    (h15 : ((i + 1) ≤ J ∨ (J + 1) ≤ i)) :
    ((stride_of am') * (i + 1)) = (((stride_of am') * i) + (stride_of am')) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/Malloc/SlotZone.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (stride_of : T1 → Int)
    (am' : T1)
    (J : Int)
    (aq : T1)
    (j : Int)
    (am_last : T1 → Int)
    (addr_of : T2 → T3 → Int)
    (L : T2)
    (slot_start : T1 → Int → T3)
    (ly_reg : T2 → T4 → Int)
    (prid : T3 → T4)
    (am_mem : T1 → T3)
    (poff : T3 → Int)
    (i : Int)
    (j0 : Int)
    (h1 : (0 ≤ ((stride_of aq) * j) ∧ (((stride_of aq) * j) + (stride_of aq)) ≤ ((stride_of aq) * ((am_last aq) + 1))))
    (h2 : (addr_of L (slot_start aq j)) = ((ly_reg L (prid (am_mem aq))) + (poff (slot_start aq j))))
    (h3 : (addr_of L (am_mem am')) = ((ly_reg L (prid (am_mem am'))) + (poff (am_mem am'))))
    (h4 : i ≠ j)
    (h5 : ((i + 1) ≤ j ∨ (j + 1) ≤ i))
    (h6 : ((stride_of aq) * (i + 1)) ≤ ((stride_of aq) * j))
    (h7 : ((stride_of aq) * (j + 1)) ≤ ((stride_of aq) * i))
    (h8 : j0 ≠ j)
    (h9 : (0 ≤ ((stride_of am') * i) ∧ (((stride_of am') * i) + (stride_of am')) ≤ ((stride_of am') * ((am_last am') + 1))))
    (h10 : ((((stride_of aq) * j0) + (stride_of aq)) ≤ ((stride_of aq) * j) ∨ (((stride_of aq) * j) + (stride_of aq)) ≤ ((stride_of aq) * j0)))
    (h11 : ((j0 + 1) ≤ j ∨ (j + 1) ≤ j0))
    (h12 : i ≠ J)
    (h13 : (0 ≤ ((stride_of am') * J) ∧ (((stride_of am') * J) + (stride_of am')) ≤ ((stride_of am') * ((am_last am') + 1))))
    (h14 : ((((stride_of am') * i) + (stride_of am')) ≤ ((stride_of am') * J) ∨ (((stride_of am') * J) + (stride_of am')) ≤ ((stride_of am') * i)))
    (h15 : ((i + 1) ≤ J ∨ (J + 1) ≤ i)) :
    ((stride_of am') * (J + 1)) = (((stride_of am') * J) + (stride_of am')) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/F0A_instok.v (replace)
example
    {T1 T2 : Type}
    (ag_thread : T1 → Int)
    (aa_geom : T2 → T1)
    (A : T2)
    (p : Int)
    (h1 : (0 ≤ (Int.fdiv p (2 ^ (32 : Nat))) ∧ (Int.fdiv p (2 ^ (32 : Nat))) < (2 ^ (15 : Nat)))) :
    ((ag_thread (aa_geom A)) + 2784) = (((ag_thread (aa_geom A)) + 208) + 2576) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/F0A_rebuild.v (replace)
example
    {T1 T2 T3 : Type}
    (x : Int)
    (region_beg : T1 → Int → Int)
    (SB : T1)
    (qb_id : T2 → T3 → Int)
    (G : T2)
    (qb : T3)
    (h1 : ((16 * x) % 8192) = 0)
    (h2 : (qb_id G qb) = x) :
    (x * (2 ^ (4 : Nat))) = (((region_beg SB 24) + (16 * x)) - (region_beg SB 24)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/InvQ8.v (assert)
example (c' : Int) (c : Int) :
    ((c' + 1) ≤ c ∨ c ≤ c') := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/SegD_skel2.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (DEPOT : Int)
    (i : Int)
    (j : Nat)
    (blkN : Int)
    (G : T1)
    (bv_unsigned : T2 → Int)
    (eval : T3 → T4 → T2)
    (rhoE : T3)
    (nn_addr : T4)
    (dN : T1 → Int)
    (SegD_wf_node_addr : T1 → Int → Int)
    (bd_addr : T4)
    (STORE : Int)
    (b : Nat)
    (stc_addr : T4)
    (slotN_addr : T4)
    (MAP1 : Int)
    (sz : Int)
    (h1 : (bv_unsigned (eval rhoE nn_addr)) = (blkN + (16 * (((dN G) + 1) % 65536))))
    (h2 : (SegD_wf_node_addr G ((dN G) + 1)) = (blkN + (16 * (((dN G) + 1) % 65536))))
    (h3 : (bv_unsigned (eval rhoE bd_addr)) = (STORE + (16 * ((b : Nat) : Int))))
    (h4 : (bv_unsigned (eval rhoE stc_addr)) = (STORE + (16 * ((b : Nat) : Int))))
    (h5 : (bv_unsigned (eval rhoE slotN_addr)) = (MAP1 + (8 * (((dN G) + 1) / 65536))))
    (h6 : (0 ≤ (((dN G) + 1) / 65536) ∧ (((dN G) + 1) / 65536) < (2 ^ (15 : Nat))))
    (h7 : ((b : Nat) : Int) < 4096)
    (h8 : (1 ≤ sz ∧ sz ≤ 10)) :
    (((DEPOT + (4 * i)) + 0) + ((j : Nat) : Int)) = ((DEPOT + (4 * i)) + ((j : Nat) : Int)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/a0.v (replace)
example
    {T1 T2 T3 : Type}
    (dN : T1 → Int)
    (G : T1)
    (fblk : T2 → Int)
    (dF : T1 → T2)
    (b : Nat)
    (nth : Nat → T3 → Int → Int)
    (dNB : T1 → T3)
    (node_addr : T1 → Int → Int)
    (IMG_HI : Int)
    (h1 : (fblk (dF G)) < 4096)
    (h2 : ((b : Nat) : Int) < 4096)
    (h3 : (node_addr G ((dN G) + 1)) = ((nth (Int.toNat (((dN G) + 1) / 65536)) (dNB G) 0) + (16 * (((dN G) + 1) % 65536))))
    (h4 : (IMG_HI ≤ (node_addr G ((dN G) + 1)) ∧ ((node_addr G ((dN G) + 1)) + 16) ≤ 140737479966720)) :
    ((dN G) + 2) = (((dN G) + 1) + 1) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/ab.v (replace)
example (m : Int) (n : Int) (M64v : Int) :
    (((m + 8) + n) + (1 * M64v)) = (((m + 16) + n) + (M64v - 8)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/ac.v (replace)
example (t : Int) (q : Int) :
    (0 + (((1 + (128 * t)) + (32768 * q)) * 2)) = ((2 + (256 * t)) + (65536 * q)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/ac.v (replace)
example (t : Int) (q : Int) :
    (3 + ((t + (256 * q)) * (2 ^ (8 : Nat)))) = ((3 + (256 * t)) + (65536 * q)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/ad.v (replace)
example (q : Int) (k : Nat) :
    (q + (((k : Nat) : Int) * 4096)) = (q + (4096 * ((k : Nat) : Int))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/az.v (replace)
example
    {T1 T2 T3 : Type}
    (y : Int)
    (region_beg : T1 → Int → Int)
    (ag_spacebeg : T2 → T1)
    (aa_geom : T3 → T2)
    (A : T3)
    (x : Int)
    (h1 : x = y) :
    (y * (2 ^ (4 : Nat))) = (((region_beg (ag_spacebeg (aa_geom A)) 24) + (16 * y)) - (region_beg (ag_spacebeg (aa_geom A)) 24)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/b7.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (eval : T2 → T3 → T1)
    (rhoE : T2)
    (base : T3)
    (lo : Int) :
    (bv_unsigned (eval rhoE base)) = (((bv_unsigned (eval rhoE base)) + lo) - lo) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/b7.v (replace)
example :
    (1576584 : Int) = ((0 + 1576584) + ((0 : Nat) : Int)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/b9.v (replace)
example (sc : Int) (sn : Int) :
    ((sc + sn) + (-8192)) = ((sc + sn) - 8192) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/b9.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (qb_addr : T1 → Int)
    (n : T1)
    (j : Nat)
    (c : T1)
    (length : T2 → Nat)
    (qb_items : T1 → T2)
    (e : Bool)
    (last_addr : T3 → Int)
    (E : T3)
    (last : T3 → T4 → T1)
    (qb_dflt : T4)
    (h1 : (qb_addr c) ≠ (qb_addr n))
    (h2 : j < (length (qb_items n)))
    (h3 : (e = true → ((0 ≤ (last_addr E) ∧ (last_addr E) < ((2 ^ (62 : Nat)) - 24)) ∧ ((((last_addr E) + 8192) ≤ (qb_addr c) ∨ ((qb_addr c) + 8192) ≤ (last_addr E)) ∧ (((last_addr E) + 8192) ≤ (qb_addr n) ∨ ((qb_addr n) + 8192) ≤ (last_addr E))))))
    (h4 : (qb_addr (last E qb_dflt)) ≠ (qb_addr c))
    (h5 : (qb_addr (last E qb_dflt)) ≠ (qb_addr n)) :
    (((qb_addr n) + 24) + (8 * ((j : Nat) : Int))) = ((((qb_addr n) + 24) + (8 * ((j : Nat) : Int))) + 0) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/b9.v (replace)
example
    {T1 T2 : Type}
    (qb_addr : T1 → Int)
    (c : T1)
    (length : T2 → Nat)
    (qb_items : T1 → T2)
    (n : T1)
    (h1 : 0 < (length (qb_items n))) :
    (((qb_addr c) + ((((length (qb_items c)) : Nat) : Int) * (2 ^ (3 : Nat)))) + 24) = (((qb_addr c) + 24) + (8 * ((((length (qb_items c)) + 0) : Nat) : Int))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/be.v (replace)
example
    {T1 T2 T3 : Type}
    (it_ab : T1 → Int)
    (it : T1)
    (rz : Int → Int)
    (snd : T1 → Int)
    (ag_spacebeg : T2 → Int)
    (aa_geom : T3 → T2)
    (A : T3)
    (c : Int)
    (Size : Int → Int)
    (x : Int)
    (fst : T1 → Int)
    (h1 : (Int.fdiv (snd it) (2 ^ (32 : Nat))) = 0)
    (h2 : (Int.fmod (snd it) (2 ^ (32 : Nat))) = (snd it))
    (h3 : ((it_ab it) - ((ag_spacebeg (aa_geom A)) + (c * (2 ^ (32 : Nat))))) = ((Size c) * x))
    (h4 : 0 ≤ x)
    (h5 : (((fst it) - 16) % 16) = 0) :
    (((((it_ab it) / 16) + ((rz (snd it)) / 16)) - 1) * 16) = ((((16 * ((it_ab it) / 16)) + 0) + ((16 * ((rz (snd it)) / 16)) + 0)) - 16) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/be.v (replace)
example
    (t : Int)
    (h1 : (Int.fdiv ((3 + (256 * t)) + (65536 * 0)) (2 ^ (16 : Nat))) = 0)
    (h2 : (((3 + (256 * t)) + (65536 * 0)) % 256) = 3) :
    (3 + (t * 256)) = ((3 + (256 * t)) + (65536 * 0)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/bf.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (ag_thread : T1 → Int)
    (aa_geom : T2 → T1)
    (A : T2)
    (it_cls : T3 → Int)
    (it : T3)
    (vb : Bool)
    (rz : T4 → Int)
    (snd : T3 → T4)
    (fst : T3 → Int)
    (ag_spacebeg : T1 → Int)
    (it_id : T1 → T3 → Int)
    (h1 : (vb = true → (rz (snd it)) ≠ 16))
    (h2 : (vb = false → (rz (snd it)) = 16))
    (h3 : (0 ≤ ((((fst it) - (rz (snd it))) - ((ag_spacebeg (aa_geom A)) + ((it_cls it) * (2 ^ (32 : Nat))))) / 16) ∧ ((((fst it) - (rz (snd it))) - ((ag_spacebeg (aa_geom A)) + ((it_cls it) * (2 ^ (32 : Nat))))) / 16) < (2 ^ (32 : Nat))))
    (h4 : (it_id (aa_geom A) it) = ((((fst it) - (rz (snd it))) - ((ag_spacebeg (aa_geom A)) + ((it_cls it) * (2 ^ (32 : Nat))))) / 16)) :
    ((((ag_thread (aa_geom A)) + 208) + (80 * (it_cls it))) + 0) = (((ag_thread (aa_geom A)) + 208) + (80 * (it_cls it))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/bt.v (replace)
example (ua : Int) :
    (ua + (511 * 8)) = (ua + 4088) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/bv.v (assert)
example {T1 : Type} (sc_map_beg : T1 → Int) (lst : T1) (z : Int) :
    ((((sc_map_beg lst) + 24) ≤ z ∧ z < ((sc_map_beg lst) + 32)) ∨ (¬ (((sc_map_beg lst) + 24) ≤ z ∧ z < ((sc_map_beg lst) + 32)))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/bv.v (replace)
example
    {T1 T2 : Type}
    (z : Int)
    (PABu : Int)
    (nn : Int)
    (length : T1 → Nat)
    (aa_sec : T2 → T1)
    (A : T2)
    (i : Nat)
    (h1 : ((((length (aa_sec A)) - 1) : Nat) : Int) = (nn - 1))
    (h2 : ((length (aa_sec A)) - 1) ≠ i) :
    z = ((PABu + (8 * (nn - 1))) + (z - (PABu + (8 * (nn - 1))))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/c5.v (replace)
example
    {T1 T2 : Type}
    (c : Int)
    (length : T1 → Nat)
    (aa_sec : T2 → T1)
    (A : T2)
    (h1 : (c % 8) = 0)
    (h2 : (8 * (((length (aa_sec A)) : Nat) : Int)) = c)
    (h3 : (c + (2 ^ (17 : Nat))) ≤ (2 ^ (23 : Nat)))
    (h4 : (c % 4096) = 0) :
    (((2 ^ (5 : Nat)) * (Int.fdiv c (2 ^ (17 : Nat)))) * 4096) = ((2 ^ (17 : Nat)) * (Int.fdiv c (2 ^ (17 : Nat)))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocA/cc.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (VNS : Int)
    (MS : Int)
    (ua : Int)
    (nv : Int)
    (Sh : Int → Int)
    (bv_unsigned : T1 → Int)
    (eval : T2 → T3 → T1)
    (r : T2)
    (RUE : T4 → T3)
    (nx : T4)
    (a0e7 : T4 → T3)
    (BR : T4 → T3)
    (L3b : T3)
    (a2e7 : T4 → T3)
    (h1 : (VNS % 8) = 0)
    (h2 : (MS % 8) = 0)
    (h3 : (ua % 8) = 0)
    (h4 : (68609 ≤ VNS ∧ VNS ≤ (nv + 4103)))
    (h5 : ((VNS + 4096) ≤ MS ∧ MS ≤ (VNS + 8191)))
    (h6 : ((Sh ua) + (MS / 8)) < (2 ^ (45 : Nat)))
    (h7 : (bv_unsigned (eval r (RUE nx))) = ((ua + 2048) + VNS))
    (h8 : (bv_unsigned (eval r (a0e7 nx))) = (((Sh ua) + (VNS / 8)) + 256))
    (h9 : (bv_unsigned (eval r (BR nx))) = (((Sh ua) + (VNS / 8)) + 256))
    (h10 : (bv_unsigned (eval r L3b)) = (((MS / 8) - (VNS / 8)) - 256))
    (h11 : (bv_unsigned (eval r (a2e7 nx))) = (((MS / 8) - (VNS / 8)) - 256))
    (h12 : (((VNS + 4095) - ((VNS + 4095) % 4096)) + 4096) = MS) :
    ((VNS + 4096) - 1) = (VNS + 4095) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocB/RebuildM.v (replace)
example
    (SB : Int)
    (Sh : Int → Int)
    (SHADOW_OFF : Int)
    (h1 : (((Sh SB) + (2 ^ (34 : Nat))) + 512) ≤ (SHADOW_OFF + (140737479966720 / 8))) :
    (SB + (((2 ^ (34 : Nat)) + 512) * 8)) = ((SB + (2 ^ (37 : Nat))) + 4096) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocB/SegD_skel2.v (replace)
example (r : Int) :
    ((4 * r) * (2 ^ (42 : Nat))) = (r * (2 ^ (44 : Nat))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocB/SegD_skel2.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (blkN : Int)
    (dN : T1 → Int)
    (G : T1)
    (j : Nat)
    (bv_unsigned : T2 → Int)
    (eval : T3 → T4 → T2)
    (rhoE : T3)
    (nn_addr : T4)
    (SegD_wf_node_addr : T1 → Int → Int)
    (bd_addr : T4)
    (STORE : Int)
    (b : Nat)
    (stc_addr : T4)
    (slotN_addr : T4)
    (MAP1 : Int)
    (sz : Int)
    (KMAX : Int)
    (h1 : (bv_unsigned (eval rhoE nn_addr)) = (blkN + (16 * (((dN G) + 1) % 65536))))
    (h2 : (SegD_wf_node_addr G ((dN G) + 1)) = (blkN + (16 * (((dN G) + 1) % 65536))))
    (h3 : (bv_unsigned (eval rhoE bd_addr)) = (STORE + (16 * ((b : Nat) : Int))))
    (h4 : (bv_unsigned (eval rhoE stc_addr)) = (STORE + (16 * ((b : Nat) : Int))))
    (h5 : (bv_unsigned (eval rhoE slotN_addr)) = (MAP1 + (8 * (((dN G) + 1) / 65536))))
    (h6 : (0 ≤ (((dN G) + 1) / 65536) ∧ (((dN G) + 1) / 65536) < (2 ^ (15 : Nat))))
    (h7 : ((b : Nat) : Int) < 4096)
    (h8 : (1 ≤ sz ∧ sz ≤ 30))
    (h9 : (sz ≤ 10 ∨ (dN G) ≤ (KMAX + 1))) :
    (((blkN + (16 * (((dN G) + 1) % 65536))) + 0) + ((j : Nat) : Int)) = ((blkN + (16 * (((dN G) + 1) % 65536))) + ((j : Nat) : Int)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocB/SegQ3R_loop.v (replace)
example
    {T1 : Type}
    (qb_addr : T1 → Int)
    (nxt : T1)
    (prv : T1)
    (cur : T1)
    (h1 : (qb_addr cur) ≠ (qb_addr nxt))
    (h2 : (qb_addr nxt) ≠ (qb_addr prv)) :
    ((1024 * ((qb_addr nxt) / 8192)) * (2 ^ (3 : Nat))) = (8192 * ((qb_addr nxt) / 8192)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocB/SegQ3R_loop.v (replace)
example
    {T1 T2 : Type}
    (QG : Int)
    (cur : T1)
    (qb_size : T1 → Int)
    (qsize : T2 → Int)
    (rest' : T2)
    (kQuarantineMin : Int)
    (h1 : (8192 ≤ (qb_size cur) ∧ 0 ≤ (qsize rest')))
    (h2 : (qsize rest') ≤ kQuarantineMin) :
    (0 + (QG + 168)) = ((QG + 160) + 8) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocB/i6.v (replace)
example (qs : Int) (qr : Int) :
    (7 + ((qs - qr) * 8)) = (((qs - qr) * 8) + 7) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocB/jh.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (s : T1) (b : T1) :
    (bv_unsigned s) = (((bv_unsigned b) + (bv_unsigned s)) - (bv_unsigned b)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/MallocB/jt.v (replace)
example
    {T1 T2 T3 : Type}
    (a : Int)
    (nd : Nat)
    (rho3 : T1)
    (bv_unsigned : T2 → Int)
    (eval : T1 → T3 → T2)
    (vS7 : T3)
    (h1 : (bv_unsigned (eval rho3 vS7)) = ((a + 152) + (8 * ((nd : Nat) : Int)))) :
    ((a + 24) + (8 * ((nd : Nat) : Int))) = (((a + 152) + (8 * ((nd : Nat) : Int))) + (-128)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/P/Drv_rs.v (replace)
example (DRV_OPS : Int) (g : Int) :
    (((DRV_OPS - (2 * g)) - 1) - 1) = (DRV_OPS - (2 * (g + 1))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/P/Mal_agrp__G15.v (replace)
example
    {T1 T2 : Type}
    (a : Int)
    (wseg_addr : T1 → T2 → Bool)
    (segsP : T1)
    (Z_to_bv : Int → Int → T2)
    (k : Nat)
    (h1 : (wseg_addr segsP (Z_to_bv 64 a)) = true)
    (h2 : k < 8)
    (h3 : a = (165392 + ((k : Nat) : Int))) :
    (367760 + (a - 367760)) = a := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/P/Mal_free__G1.v (replace)
example {T1 : Type} (stride_of : T1 → Int) (am : T1) (am_last : T1 → Int) :
    (((stride_of am) * (am_last am)) + (stride_of am)) = ((stride_of am) * ((am_last am) + 1)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/P/Mal_free__G2.v (replace)
example {T1 T2 : Type} (x : Int) (zG : T1 → T2 → Int) (L : T1) (g : T2) :
    x = (((zG L g) + 28) + (x - ((zG L g) + 28))) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/P/Mal_mslow__G2.v (assert)
example (u : Int) (c : Int) :
    ((u + c) < (2 ^ (64 : Nat)) ∨ (2 ^ (64 : Nat)) ≤ (u + c)) := by
  lia

-- tinyobjloader/fuzz_tobj_c: lib/P/Mal_nt__G3.v (replace)
example
    {T1 T2 T3 : Type}
    (usage_of : T1 → T2 → Int)
    (s : T1)
    (am_sc : T3 → T2)
    (am : T3)
    (am_last : T3 → Int) :
    (((usage_of s (am_sc am)) - ((am_last am) + 1)) + (1 * (2 ^ (64 : Nat)))) = ((usage_of s (am_sc am)) + (((2 ^ (64 : Nat)) - 1) - (am_last am))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/R_sn2fc.v (replace)
example
    {T1 : Type}
    (k1 : Int)
    (N_1 : Int)
    (length : T1 → Nat)
    (p : T1)
    (h1 : 0 ≤ k1)
    (h2 : k1 = N_1)
    (h3 : k1 = (((length p) : Nat) : Int)) :
    (Int.toNat k1) = (Int.toNat (k1 + 0)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/R_sn2fc.v (replace)
example
    {list_byte : Type}
    (n : Nat)
    (w : list_byte)
    (bs : list_byte)
    (l : Int)
    (length : list_byte → Nat)
    (dl : Nat → list_byte → list_byte)
    (k : Int)
    (h1 : (length bs) = (Int.toNat l))
    (h2 : (0 ≤ l ∧ l < (2 ^ (63 : Nat)))) :
    (((((n : Nat) : Int) - 1) - (((length (dl n w)) : Nat) : Int)) - k) = ((((n : Nat) : Int) - 1) - ((((length (dl n w)) : Nat) : Int) + k)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/U_PHhwf.v (replace)
example
    {penv T2 : Type}
    (E : penv)
    (pe_sp : penv → Int)
    (h_sp : T2 → Int)
    (pe_H : penv → T2)
    (h_vc : T2 → Int)
    (h_wrk : T2 → Int)
    (h1 : (pe_sp E) = ((h_sp (pe_H E)) - 208))
    (h2 : (h_vc (pe_H E)) = ((h_sp (pe_H E)) + 1304))
    (h3 : (h_wrk (pe_H E)) = ((h_sp (pe_H E)) + 1120))
    (h4 : (((h_sp (pe_H E)) + 1304) % 8) = 0)
    (h5 : (((h_sp (pe_H E)) + 1120) % 8) = 0) :
    ((pe_sp E) - 48) = ((pe_sp E) + (-48)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/U_Parse.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (VEP : Int)
    (wa : Int)
    (E : T1)
    (pe_sp : T1 → Int)
    (h_sp : T2 → Int)
    (H : T2)
    (pe_e : T1 → Int)
    (DATA : Int)
    (length : T3 → Nat)
    (inp : T3)
    (vb_buf : T4 → Int)
    (vv1 : T4)
    (alloc_ceiling : Int)
    (MARK_STACK : Int)
    (h1 : VEP ≠ wa)
    (h2 : (pe_sp E) = ((h_sp H) - 208))
    (h3 : (pe_e E) = (DATA + (((length inp) : Nat) : Int)))
    (h4 : DATA ≠ (vb_buf vv1))
    (h5 : wa ≠ (vb_buf vv1))
    (h6 : VEP ≠ (vb_buf vv1))
    (h7 : alloc_ceiling ≤ (((h_sp H) + (-208)) - MARK_STACK)) :
    (18446744073709551615 - (VEP + 256)) = (((2 ^ (64 : Nat)) - 1) - (VEP + 256)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/U_VS4cn.v (replace)
example
    {T1 : Type}
    (lo : Int)
    (a : Int)
    (a2 : Int)
    (sp : Int)
    (W : Int)
    (cs1 : T1)
    (cs2 : T1)
    (i : Int)
    (cells_size : T1 → Nat)
    (alloc_ceiling : Int)
    (h1 : (a + (((cells_size cs1) : Nat) : Int)) = a2)
    (h2 : (a2 + (((cells_size cs2) : Nat) : Int)) = sp)
    (h3 : alloc_ceiling ≤ lo)
    (h4 : lo ≤ (sp - W))
    (h5 : (sp - W) ≤ a) :
    (a + (((sp - W) + i) - a)) = ((sp - W) + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/U_crc32.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (lo : Int)
    (a1 : word)
    (inp : list_byte)
    (tabs : list_byte)
    (length : list_byte → Nat)
    (i0 : Int)
    (blks : Int)
    (bv_unsigned : word → Int)
    (CRC_TABS_LEN : Int)
    (h1 : (lo + 112) ≤ (bv_unsigned sp))
    (h2 : (((length tabs) : Nat) : Int) = CRC_TABS_LEN)
    (h3 : ((bv_unsigned a1) + (((length inp) : Nat) : Int)) < (2 ^ (64 : Nat))) :
    (((((length inp) : Nat) : Int) - ((i0 + (20 * (blks - 1))) + 20)) + (blks * (2 ^ (64 : Nat)))) = ((blks * 18446744073709551596) + ((((length inp) : Nat) : Int) - i0)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/U_crc32.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a1 : word)
    (lo : Int)
    (inp : list_byte)
    (a2 : word)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : (lo + 112) ≤ (bv_unsigned sp))
    (h2 : (((bv_unsigned a1) + (((length inp) : Nat) : Int)) ≤ ((bv_unsigned sp) - 112) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h3 : ((bv_unsigned a1) + (((length inp) : Nat) : Int)) < (2 ^ (64 : Nat)))
    (h4 : (bv_unsigned a2) = (((length inp) : Nat) : Int)) :
    ((bv_unsigned sp) + (-112)) = ((bv_unsigned sp) - 112) := by
  lia

-- varnish/esi_parse_fuzzer: lib/U_veqq1.v (replace)
example
    {vsb_rec henv word AS T5 : Type}
    (VEP : Int)
    (vv : vsb_rec)
    (H : henv)
    (lo : Int)
    (ra : word)
    (sp : word)
    (A : AS)
    (until_1 : vsb_rec)
    (a3'' : Int)
    (bv_unsigned : word → Int)
    (v : T5 → Int)
    (Fflags : T5)
    (Flast_mark : T5)
    (Fattr_vsb : T5)
    (Fvsb : T5)
    (vb_buf : vsb_rec → Int)
    (vb_size : vsb_rec → Int)
    (vb_len : vsb_rec → Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (alloc_ceiling : Int)
    (DOINCL_STACK : Int)
    (h_sp : henv → Int)
    (h1 : (0 ≤ (v Fflags) ∧ (v Fflags) < 16))
    (h2 : (v Flast_mark) = 1)
    (h3 : (v Fattr_vsb) = 0)
    (h4 : VEP ≠ (v Fvsb))
    (h5 : VEP ≠ (vb_buf vv))
    (h6 : (vb_size vv) ≤ ((vb_len vv) + 4096))
    (h7 : ((a_nlive A) + 1) ≤ NLIVE_MAX)
    (h8 : ((bv_unsigned sp) % 16) = 0)
    (h9 : ((bv_unsigned ra) % 2) = 0)
    (h10 : alloc_ceiling ≤ lo)
    (h11 : (lo + DOINCL_STACK) ≤ (bv_unsigned sp))
    (h12 : (bv_unsigned sp) ≤ (h_sp H))
    (h13 : 0 ≤ a3'')
    (h14 : (a3'' + 1) ≤ ((vb_len until_1) + 8)) :
    (bv_unsigned sp) = (((bv_unsigned sp) + (-128)) + 128) := by
  lia

-- varnish/esi_parse_fuzzer: lib/V_AKit.v (replace)
example
    {T1 : Type}
    (lo : Int)
    (a : Int)
    (sp : Int)
    (W : Int)
    (cs : T1)
    (i : Int)
    (cells_size : T1 → Nat)
    (alloc_ceiling : Int)
    (h1 : (a + (((cells_size cs) : Nat) : Int)) = sp)
    (h2 : alloc_ceiling ≤ lo)
    (h3 : lo ≤ (sp - W))
    (h4 : (sp - W) ≤ a) :
    (a + (((sp - W) + i) - a)) = ((sp - W) + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/V_Stgw7.v (replace)
example (ns : Int) :
    (ns + ns) = (2 * ns) := by
  lia

-- varnish/esi_parse_fuzzer: lib/V_VEzrv.v (replace)
example
    {henv word : Type}
    (H : henv)
    (lo : Int)
    (ra : word)
    (sp : word)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (VEPFIN_STACK : Int)
    (h_sp : henv → Int)
    (h_bss : henv → Int)
    (h_vc : henv → Int)
    (h_wrk : henv → Int)
    (h_vsc : henv → Int)
    (h_cp : henv → Int)
    (h_ws : henv → Int)
    (h_wsbuf : henv → Int)
    (h1 : ((bv_unsigned sp) % 16) = 0)
    (h2 : ((bv_unsigned ra) % 2) = 0)
    (h3 : alloc_ceiling ≤ lo)
    (h4 : (lo + VEPFIN_STACK) ≤ (bv_unsigned sp))
    (h5 : (bv_unsigned sp) = (h_sp H))
    (h6 : (h_bss H) = 268336)
    (h7 : (h_vc H) = ((h_sp H) + 1304))
    (h8 : (h_wrk H) = ((h_sp H) + 1120))
    (h9 : (h_vsc H) = ((h_sp H) + 2240))
    (h10 : (h_cp H) = ((h_sp H) + 1488))
    (h11 : (h_ws H) = ((h_sp H) + 1080))
    (h12 : (h_wsbuf H) = ((h_sp H) + 16)) :
    ((bv_unsigned sp) + (-32)) = ((bv_unsigned sp) - 32) := by
  lia

-- varnish/esi_parse_fuzzer: lib/V_VEzrv.v (replace)
example
    {vsb_rec AS T3 : Type}
    (VEP : Int)
    (wa : Int)
    (N_1 : Int)
    (DATA : Int)
    (vv0 : vsb_rec)
    (A0 : AS)
    (v0 : T3 → Int)
    (Fver_p : T3)
    (Fvsb : T3)
    (a_livebytes : AS → Int)
    (FIN_LIVE : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (vb_buf : vsb_rec → Int)
    (h1 : 0 < N_1)
    (h2 : (DATA ≤ (v0 Fver_p) ∧ (v0 Fver_p) ≤ (DATA + N_1)))
    (h3 : DATA ≠ VEP)
    (h4 : DATA ≠ (v0 Fvsb))
    (h5 : ((a_livebytes A0) + (FIN_LIVE N_1)) ≤ LIVE_MAX)
    (h6 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h7 : ((VEP + 312) ≤ 65536 ∨ 405504 ≤ VEP))
    (h8 : wa ≠ (vb_buf vv0)) :
    (VEP + 232) = ((VEP + 224) + 8) := by
  lia

-- varnish/esi_parse_fuzzer: lib/V_crc32.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (a1 : word)
    (bv_unsigned : word → Int)
    (i : Int)
    (h1 : (lo + 96) ≤ (bv_unsigned sp)) :
    (((bv_unsigned a1) + (i + 1)) + 1) = (((bv_unsigned a1) + i) + 2) := by
  lia

-- varnish/esi_parse_fuzzer: lib/V_vejh3.v (replace)
example
    {word list_mentry list_byte T4 : Type}
    (ra : word)
    (sp : word)
    (a1 : word)
    (VEP : Int)
    (T : Int)
    (es : list_mentry)
    (inp : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (j : Nat)
    (VM_FRAME : Int)
    (cells_size : T4 → Nat)
    (mtab_cells : list_mentry → T4)
    (length : list_byte → Nat)
    (c : word)
    (c2 : word)
    (h1 : (lo + VM_FRAME) ≤ (bv_unsigned sp))
    (h2 : 0 < T)
    (h3 : ((VEP + 248) ≤ ((bv_unsigned sp) - VM_FRAME) ∨ (bv_unsigned sp) ≤ (VEP + 240)))
    (h4 : ((T + (((cells_size (mtab_cells es)) : Nat) : Int)) ≤ ((bv_unsigned sp) - VM_FRAME) ∨ (bv_unsigned sp) ≤ T))
    (h5 : (((bv_unsigned a1) + (((length inp) : Nat) : Int)) ≤ ((bv_unsigned sp) - VM_FRAME) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h6 : (0 ≤ (bv_unsigned a1) ∧ ((bv_unsigned a1) + (((length inp) : Nat) : Int)) < (2 ^ (64 : Nat))))
    (h7 : ((bv_unsigned ra) % 2) = 0)
    (h8 : (bv_unsigned c) ≠ 0)
    (h9 : (bv_unsigned c2) ≠ 0) :
    ((bv_unsigned a1) + (((j + 1) : Nat) : Int)) = (((bv_unsigned a1) + ((j : Nat) : Int)) + 1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yb/Asan18z.v (replace)
example
    {atable word T3 T4 T5 : Type}
    (A : atable)
    (ub : Int)
    (off : Int)
    (n : Int)
    (i : Int)
    (in_hull : atable → Int → Bool)
    (bv_unsigned : word → Int)
    (w : Nat)
    (adenot : T3 → T4 → word)
    (E : T3)
    (SA : T5 → Int → T4)
    (b : T5)
    (x : word)
    (h1 : (Int.toNat i) < w)
    (h2 : (bv_unsigned (adenot E (SA b off))) = (ub + off))
    (h3 : (bv_unsigned x) = ((ub + off) + i))
    (h4 : (in_hull A (bv_unsigned x)) = false) :
    ((ub + (off + n)) + (i - n)) = ((ub + off) + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yb/Asanii6.v (replace)
example
    {acs T2 T3 : Type}
    (cs : acs)
    (a : Int)
    (bs : T2)
    (i : Nat)
    (off : Int)
    (cell_okb : T3 → Int → T2 → Bool)
    (kn : acs → T3)
    (length : T2 → Nat)
    (h1 : (cell_okb (kn cs) a bs) = true)
    (h2 : 0 ≤ a)
    (h3 : (a + (((length bs) : Nat) : Int)) ≤ (2 ^ (64 : Nat)))
    (h4 : i < (length bs)) :
    (a + ((i : Nat) : Int)) = ((0 + off) + ((a + ((i : Nat) : Int)) - off)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yd/DA_Mwrv.v (replace)
example
    {env T2 T3 : Type}
    (E : env)
    (uE : env → T2 → Int)
    (snd : T3 → T2)
    (p : T3)
    (fst : T3 → T2) :
    (uE E (snd p)) = (((uE E (fst p)) + (uE E (snd p))) - (uE E (fst p))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yd/DA_Mwrv.v (replace)
example (pgv : Int → Int) :
    (((pgv 405) + 96) + 0) = ((pgv 405) + 96) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_PHhja.v (replace)
example
    {T1 : Type}
    (p : Int)
    (n : Int)
    (a : Int)
    (k : Int)
    (sh : Int → Int)
    (i0 : Int)
    (j : Nat)
    (shpat : Int → T1)
    (length : T1 → Nat)
    (i1 : Int)
    (shadow_off : Int)
    (h1 : (p % 8) = 0)
    (h2 : 0 ≤ p)
    (h3 : p ≤ a)
    (h4 : (a + k) ≤ (p + n))
    (h5 : 1 ≤ k)
    (h6 : 0 ≤ n)
    (h7 : (((length (shpat n)) : Nat) : Int) = ((n + 7) / 8))
    (h8 : ((0 ≤ i0 ∧ i0 ≤ i1) ∧ (i1 ≤ ((n - 1) / 8) ∧ (((n - 1) / 8) < ((n + 7) / 8) ∧ (((n - 1) / 8) ≤ (n / 8) ∧ ((sh p) + i0) = ((a / 8) + shadow_off))))))
    (h9 : (i1 < (n / 8) ∨ (i1 = (n / 8) ∧ ((n % 8) ≠ 0 ∧ ((((a + k) - 1) % 8) < (n % 8) ∧ (n % 8) ≤ 7))))) :
    ((sh p) + (((Int.toNat (i0 + ((j : Nat) : Int))) : Nat) : Int)) = (((sh p) + i0) + ((j : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_PHhja.v (replace)
example
    {T1 T2 : Type}
    (me_ptr : T1 → Int)
    (e : T1)
    (c : T2)
    (bv_unsigned : T2 → Int)
    (h1 : (bv_unsigned c) ≠ 0) :
    (((me_ptr e) + ((0 : Nat) : Int)) + 1) = ((me_ptr e) + 1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_WSmsm.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (sh : Int → Int)
    (h_ff : T2 → Int)
    (H : T2)
    (h1 : (sh ((h_ff H) + 2976)) = ((sh (h_ff H)) + 372))
    (h2 : (sh ((h_ff H) + 3152)) = ((sh (h_ff H)) + 394)) :
    8320 = ((bv_unsigned sp) - ((bv_unsigned sp) - 8320)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_World.v (replace)
example
    (ff : Int)
    (kk : Int)
    (Zpow : Int → Int → Int)
    (fsize : Int → Int)
    (sh : Int → Int)
    (h1 : ((ff + (fsize kk)) % 8) = 0)
    (h2 : ((sh ff) + ((fsize kk) / 8)) = (sh (ff + (fsize kk)))) :
    (((ff / 8) + (8 * (Zpow 2 kk))) * 8) = ((8 * (ff / 8)) + (64 * (Zpow 2 kk))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_crc32.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (lo : Int)
    (junk : list_byte)
    (B : Int)
    (inp : list_byte)
    (tab : list_byte)
    (tabb : list_byte)
    (P : Int)
    (NP : Int)
    (length : list_byte → Nat)
    (i : Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (h1 : (lo + 128) ≤ (bv_unsigned sp))
    (h2 : alloc_ceiling ≤ lo)
    (h3 : (length junk) = 24)
    (h4 : (((length tab) : Nat) : Int) = 1024)
    (h5 : (((length tabb) : Nat) : Int) = 4096)
    (h6 : ((P % 8) = 0 ∧ (0 ≤ P ∧ (P ≤ B ∧ ((B + (((length inp) : Nat) : Int)) ≤ (P + NP) ∧ (P + NP) ≤ alloc_ceiling)))))
    (h7 : (((length inp) : Nat) : Int) < (2 ^ (64 : Nat))) :
    ((((length inp) : Nat) : Int) - (i + 1)) = (((((length inp) : Nat) : Int) - i) + (-1)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_vemjo.v (replace)
example
    {word AS vsb_rec list_word list_byte : Type}
    (sp : word)
    (A0 : AS)
    (vr : vsb_rec)
    (VA : Int)
    (slots : list_word)
    (hs : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (length : list_word → Nat)
    (OUT : list_word → list_byte → list_word)
    (vb_size : vsb_rec → Int)
    (EXT_MAX : Int)
    (a_livebytes : AS → Int)
    (vsb_extendsize : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (a_seccred : AS → Int)
    (PRIM_ROOM : Int)
    (a_primcred : AS → Int)
    (alloc_ceiling : Int)
    (VPRINTF_STACK : Int)
    (h1 : (bv_unsigned sp) ≤ VA)
    (h2 : (VA + (8 * (((length slots) : Nat) : Int))) ≤ (2 ^ (47 : Nat)))
    (h3 : (((vb_size vr) + (((length (OUT slots hs)) : Nat) : Int)) + 1) ≤ EXT_MAX)
    (h4 : ((a_livebytes A0) + (vsb_extendsize (((vb_size vr) + (((length (OUT slots hs)) : Nat) : Int)) + 1))) ≤ LIVE_MAX)
    (h5 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h6 : 1 ≤ (a_seccred A0))
    (h7 : PRIM_ROOM ≤ (a_primcred A0))
    (h8 : ((bv_unsigned sp) % 16) = 0)
    (h9 : alloc_ceiling ≤ lo)
    (h10 : (lo + VPRINTF_STACK) ≤ (bv_unsigned sp))
    (h11 : ((bv_unsigned sp) + 64) ≤ (2 ^ (47 : Nat))) :
    (bv_unsigned sp) = (((bv_unsigned sp) + (-192)) + 192) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_vemjo.v (replace)
example
    {word AS vsb_rec list_byte T5 T6 : Type}
    (sp : word)
    (A0 : AS)
    (vr : vsb_rec)
    (hs : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (length : T5 → Nat)
    (OUT : T6 → list_byte → T5)
    (vb_size : vsb_rec → Int)
    (slots : T6)
    (EXT_MAX : Int)
    (a_livebytes : AS → Int)
    (vsb_extendsize : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (a_seccred : AS → Int)
    (PRIM_ROOM : Int)
    (a_primcred : AS → Int)
    (alloc_ceiling : Int)
    (PRINTF_STACK : Int)
    (h1 : (((vb_size vr) + (((length (OUT slots hs)) : Nat) : Int)) + 1) ≤ EXT_MAX)
    (h2 : ((a_livebytes A0) + (vsb_extendsize (((vb_size vr) + (((length (OUT slots hs)) : Nat) : Int)) + 1))) ≤ LIVE_MAX)
    (h3 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h4 : 1 ≤ (a_seccred A0))
    (h5 : PRIM_ROOM ≤ (a_primcred A0))
    (h6 : ((bv_unsigned sp) % 16) = 0)
    (h7 : alloc_ceiling ≤ lo)
    (h8 : (lo + PRINTF_STACK) ≤ (bv_unsigned sp))
    (h9 : ((bv_unsigned sp) + 64) ≤ (2 ^ (47 : Nat))) :
    ((bv_unsigned sp) + (-48)) = (((bv_unsigned sp) + (-128)) + 80) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_vemjo.v (replace)
example
    {vsb_rec AS T3 : Type}
    (VEP : Int)
    (vr : vsb_rec)
    (A0 : AS)
    (vv : T3 → Int)
    (Fflags : T3)
    (Flast_mark : T3)
    (Fattr_vsb : T3)
    (Fvsb : T3)
    (vb_buf : vsb_rec → Int)
    (vb_size : vsb_rec → Int)
    (vb_len : vsb_rec → Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (PRIM_ROOM : Int)
    (PPOT_CAP : Int)
    (vsb_ppot : vsb_rec → Int)
    (a_primcred : AS → Int)
    (h1 : (0 ≤ (vv Fflags) ∧ (vv Fflags) < 16))
    (h2 : (vv Flast_mark) = 1)
    (h3 : (vv Fattr_vsb) = 0)
    (h4 : VEP ≠ (vv Fvsb))
    (h5 : VEP ≠ (vb_buf vr))
    (h6 : (vb_size vr) ≤ ((vb_len vr) + 4096))
    (h7 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h8 : (PRIM_ROOM + (PPOT_CAP - (vsb_ppot vr))) ≤ (a_primcred A0)) :
    (VEP + 288) = ((VEP + 280) + 8) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_veqih.v (replace)
example
    {vsb_rec word AS T4 : Type}
    (VEP : Int)
    (N_1 : Int)
    (DATA : Int)
    (vv0 : vsb_rec)
    (lo : Int)
    (sp : word)
    (A0 : AS)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (VEPFIN_STACK : Int)
    (v0 : T4 → Int)
    (Fver_p : T4)
    (Fvsb : T4)
    (a_livebytes : AS → Int)
    (FIN_LIVE : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (FIN_CRED : Int → Int)
    (a_seccred : AS → Int)
    (PRIM_ROOM : Int)
    (PPOT_CAP : Int)
    (vsb_ppot : vsb_rec → Int)
    (a_primcred : AS → Int)
    (h1 : ((bv_unsigned sp) % 16) = 0)
    (h2 : alloc_ceiling ≤ lo)
    (h3 : (lo + VEPFIN_STACK) ≤ (bv_unsigned sp))
    (h4 : 0 < N_1)
    (h5 : (DATA ≤ (v0 Fver_p) ∧ (v0 Fver_p) ≤ (DATA + N_1)))
    (h6 : DATA ≠ VEP)
    (h7 : DATA ≠ (v0 Fvsb))
    (h8 : ((a_livebytes A0) + (FIN_LIVE N_1)) ≤ LIVE_MAX)
    (h9 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h10 : (FIN_CRED N_1) ≤ (a_seccred A0))
    (h11 : (PRIM_ROOM + (PPOT_CAP - (vsb_ppot vv0))) ≤ (a_primcred A0)) :
    ((bv_unsigned sp) + (-112)) = (((bv_unsigned sp) + (-64)) + (-48)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_veqih.v (replace)
example
    {vsb_rec word AS T4 : Type}
    (VEP : Int)
    (N_1 : Int)
    (DATA : Int)
    (vv0 : vsb_rec)
    (lo : Int)
    (sp : word)
    (A0 : AS)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (VEPFIN_STACK : Int)
    (v0 : T4 → Int)
    (Fver_p : T4)
    (Fvsb : T4)
    (a_livebytes : AS → Int)
    (FIN_LIVE : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (FIN_CRED : Int → Int)
    (a_seccred : AS → Int)
    (PRIM_ROOM : Int)
    (PPOT_CAP : Int)
    (vsb_ppot : vsb_rec → Int)
    (a_primcred : AS → Int)
    (h1 : ((bv_unsigned sp) % 16) = 0)
    (h2 : alloc_ceiling ≤ lo)
    (h3 : (lo + VEPFIN_STACK) ≤ (bv_unsigned sp))
    (h4 : 0 < N_1)
    (h5 : (DATA ≤ (v0 Fver_p) ∧ (v0 Fver_p) ≤ (DATA + N_1)))
    (h6 : DATA ≠ VEP)
    (h7 : DATA ≠ (v0 Fvsb))
    (h8 : ((a_livebytes A0) + (FIN_LIVE N_1)) ≤ LIVE_MAX)
    (h9 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h10 : (FIN_CRED N_1) ≤ (a_seccred A0))
    (h11 : (PRIM_ROOM + (PPOT_CAP - (vsb_ppot vv0))) ≤ (a_primcred A0)) :
    ((bv_unsigned sp) + (-64)) = (((bv_unsigned sp) + (-112)) + 48) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_veqih.v (replace)
example
    {vsb_rec AS T3 : Type}
    (VEP : Int)
    (wa : Int)
    (N_1 : Int)
    (DATA : Int)
    (vv0 : vsb_rec)
    (A0 : AS)
    (v0 : T3 → Int)
    (Fver_p : T3)
    (Fvsb : T3)
    (a_livebytes : AS → Int)
    (FIN_LIVE : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (FIN_CRED : Int → Int)
    (a_seccred : AS → Int)
    (PRIM_ROOM : Int)
    (PPOT_CAP : Int)
    (vsb_ppot : vsb_rec → Int)
    (a_primcred : AS → Int)
    (vb_buf : vsb_rec → Int)
    (h1 : 0 < N_1)
    (h2 : (DATA ≤ (v0 Fver_p) ∧ (v0 Fver_p) ≤ (DATA + N_1)))
    (h3 : DATA ≠ VEP)
    (h4 : DATA ≠ (v0 Fvsb))
    (h5 : ((a_livebytes A0) + (FIN_LIVE N_1)) ≤ LIVE_MAX)
    (h6 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h7 : (FIN_CRED N_1) ≤ (a_seccred A0))
    (h8 : (PRIM_ROOM + (PPOT_CAP - (vsb_ppot vv0))) ≤ (a_primcred A0))
    (h9 : wa ≠ (vb_buf vv0)) :
    (VEP + 232) = ((VEP + 224) + 8) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_vezat.v (replace)
example
    {vsb_rec word AS T4 : Type}
    (VEP : Int)
    (vr : vsb_rec)
    (l : Int)
    (c8 : Int)
    (c16 : Int)
    (c64 : Int)
    (lo : Int)
    (sp : word)
    (A0 : AS)
    (bv_unsigned : word → Int)
    (d : Int)
    (vv : T4 → Int)
    (Fvsb : T4)
    (vb_buf : vsb_rec → Int)
    (vb_size : vsb_rec → Int)
    (EXT_MAX : Int)
    (a_livebytes : AS → Int)
    (vsb_extendsize : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (a_seccred : AS → Int)
    (PRIM_ROOM : Int)
    (a_primcred : AS → Int)
    (alloc_ceiling : Int)
    (EMITLEN_STACK : Int)
    (h1 : (1 ≤ l ∧ l < (2 ^ (62 : Nat))))
    (h2 : (0 ≤ c8 ∧ c8 < 256))
    (h3 : (0 ≤ c16 ∧ c16 < 256))
    (h4 : (0 ≤ c64 ∧ c64 < 256))
    (h5 : VEP ≠ (vv Fvsb))
    (h6 : VEP ≠ (vb_buf vr))
    (h7 : ((vb_size vr) + 9) ≤ EXT_MAX)
    (h8 : ((a_livebytes A0) + (vsb_extendsize ((vb_size vr) + 9))) ≤ LIVE_MAX)
    (h9 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h10 : 1 ≤ (a_seccred A0))
    (h11 : PRIM_ROOM ≤ (a_primcred A0))
    (h12 : ((bv_unsigned sp) % 16) = 0)
    (h13 : alloc_ceiling ≤ lo)
    (h14 : (lo + EMITLEN_STACK) ≤ (bv_unsigned sp))
    (h15 : (((bv_unsigned sp) + (-128)) % 16) = 0)
    (h16 : (0 ≤ d ∧ d ≤ 16)) :
    (((bv_unsigned sp) + (-128)) - d) = (((((bv_unsigned sp) + (-128)) - d) + 32) - 32) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_vezat.v (replace)
example
    {vsb_rec word AS T4 : Type}
    (VEP : Int)
    (vr : vsb_rec)
    (l : Int)
    (lo : Int)
    (sp : word)
    (A0 : AS)
    (bv_unsigned : word → Int)
    (vv : T4 → Int)
    (Fo_total : T4)
    (Fdogzip : T4)
    (Fvsb : T4)
    (vb_buf : vsb_rec → Int)
    (vb_size : vsb_rec → Int)
    (EXT_MAX : Int)
    (a_livebytes : AS → Int)
    (vsb_extendsize : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (a_seccred : AS → Int)
    (PRIM_ROOM : Int)
    (a_primcred : AS → Int)
    (alloc_ceiling : Int)
    (EMITC_STACK : Int)
    (h1 : 0 ≤ l)
    (h2 : ((vv Fo_total) + l) < (2 ^ (62 : Nat)))
    (h3 : 0 ≤ (vv Fo_total))
    (h4 : (vv Fdogzip) = 0)
    (h5 : VEP ≠ (vv Fvsb))
    (h6 : VEP ≠ (vb_buf vr))
    (h7 : ((vb_size vr) + 9) ≤ EXT_MAX)
    (h8 : ((a_livebytes A0) + (vsb_extendsize ((vb_size vr) + 9))) ≤ LIVE_MAX)
    (h9 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h10 : 1 ≤ (a_seccred A0))
    (h11 : PRIM_ROOM ≤ (a_primcred A0))
    (h12 : ((bv_unsigned sp) % 16) = 0)
    (h13 : alloc_ceiling ≤ lo)
    (h14 : (lo + EMITC_STACK) ≤ (bv_unsigned sp)) :
    128 = ((bv_unsigned sp) - ((bv_unsigned sp) - 128)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yl/A_vezat.v (replace)
example
    {vsb_rec word AS T4 : Type}
    (VEP : Int)
    (vr : vsb_rec)
    (l : Int)
    (lo : Int)
    (sp : word)
    (A0 : AS)
    (bv_unsigned : word → Int)
    (d : Int)
    (vv : T4 → Int)
    (Fo_total : T4)
    (Fdogzip : T4)
    (Fvsb : T4)
    (vb_buf : vsb_rec → Int)
    (vb_size : vsb_rec → Int)
    (EXT_MAX : Int)
    (a_livebytes : AS → Int)
    (vsb_extendsize : Int → Int)
    (LIVE_MAX : Int)
    (a_nlive : AS → Int)
    (NLIVE_MAX : Int)
    (a_seccred : AS → Int)
    (PRIM_ROOM : Int)
    (a_primcred : AS → Int)
    (alloc_ceiling : Int)
    (EMITC_STACK : Int)
    (h1 : 0 ≤ l)
    (h2 : ((vv Fo_total) + l) < (2 ^ (62 : Nat)))
    (h3 : 0 ≤ (vv Fo_total))
    (h4 : (vv Fdogzip) = 0)
    (h5 : VEP ≠ (vv Fvsb))
    (h6 : VEP ≠ (vb_buf vr))
    (h7 : ((vb_size vr) + 9) ≤ EXT_MAX)
    (h8 : ((a_livebytes A0) + (vsb_extendsize ((vb_size vr) + 9))) ≤ LIVE_MAX)
    (h9 : ((a_nlive A0) + 1) ≤ NLIVE_MAX)
    (h10 : 1 ≤ (a_seccred A0))
    (h11 : PRIM_ROOM ≤ (a_primcred A0))
    (h12 : ((bv_unsigned sp) % 16) = 0)
    (h13 : alloc_ceiling ≤ lo)
    (h14 : (lo + EMITC_STACK) ≤ (bv_unsigned sp))
    (h15 : (((bv_unsigned sp) + (-128)) % 16) = 0)
    (h16 : (0 ≤ d ∧ d ≤ 16)) :
    (((bv_unsigned sp) + (-128)) - d) = (((((bv_unsigned sp) + (-128)) - d) + 32) - 32) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFre9ly.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (n0 : Int)
    (kQuarantineBatchClass : Int)
    (bv_unsigned : T1 → Int)
    (kw : T1)
    (kb : Int)
    (a_sb : T2 → Int)
    (A : T2)
    (b : Int)
    (p : Int)
    (alloc_ceiling : Int)
    (length : T3 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T3 → Int)
    (r : T3)
    (ba_entries : T4 → T3)
    (b0 : T4)
    (ebytes : T3 → Int)
    (es : T3)
    (a_qglobal : T2 → T3)
    (batch_addr : Int → T5 → Int)
    (b' : T5)
    (batch_bytes : T5 → Int)
    (qt' : T6)
    (qc_first : T2 → T6 → Int)
    (h1 : (1 ≤ kQuarantineBatchClass ∧ kQuarantineBatchClass ≤ 30))
    (h2 : (bv_unsigned kw) = (kb * 512))
    (h3 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h4 : (bv_unsigned kw) < (2 ^ (32 : Nat)))
    (h5 : (1 ≤ n0 ∧ n0 < (2 ^ (32 : Nat))))
    (h6 : (p + (8 * ((n0 + 7) / 8))) ≤ alloc_ceiling)
    (h7 : ((a_sb A) + (2 ^ (37 : Nat))) ≤ (2 ^ (47 : Nat)))
    (h8 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h9 : 0 ≤ (ebytes (ba_entries b0)))
    (h10 : 0 ≤ (ebytes es))
    (h11 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h12 : 0 ≤ (q_bytes (a_qglobal A)))
    (h13 : (((length (a_qglobal A)) : Nat) : Int) ≠ 0)
    (h14 : (batch_addr (a_sb A) b') = b)
    (h15 : (batch_bytes b') = (n0 + 8192))
    (h16 : (qc_first A qt') = b) :
    (0 + (n0 + 8192)) = ((n0 + 8192) + 0) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeG2c.v (replace)
example
    {T1 T2 T3 : Type}
    (p_thr : T1 → Int)
    (a_pl : T2 → T1)
    (A : T2)
    (i : Int)
    (kQuarantineBatchClass : Int)
    (kb : Int)
    (class_size : Int → Int)
    (kCompactPtrScale : Int)
    (bv_unsigned : T3 → Int)
    (kw : T3)
    (a_sb : T2 → Int)
    (b : Int)
    (kHighMemBeg : Int)
    (alloc_ceiling : Int)
    (h1 : (1 ≤ kQuarantineBatchClass ∧ kQuarantineBatchClass ≤ 30))
    (h2 : (Int.fdiv (kb * (class_size kQuarantineBatchClass)) kCompactPtrScale) = (kb * 512))
    (h3 : (bv_unsigned kw) = (kb * 512))
    (h4 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h5 : kHighMemBeg ≤ b)
    (h6 : (b + 8192) ≤ alloc_ceiling) :
    ((p_thr (a_pl A)) + (2784 + i)) = ((((p_thr (a_pl A)) + 208) + 2576) + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeG2c.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (p : Int)
    (kQuarantineBatchClass : Int)
    (kb : Int)
    (class_size : Int → Int)
    (kCompactPtrScale : Int)
    (bv_unsigned : T1 → Int)
    (kw : T1)
    (a_sb : T2 → Int)
    (A : T2)
    (b : Int)
    (n0 : Int)
    (kHighMemBeg : Int)
    (alloc_ceiling : Int)
    (length : T3 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T3 → Int)
    (r : T3)
    (ba_entries : T4 → T3)
    (b0 : T4)
    (ebytes : T3 → Int)
    (es : T3)
    (a_qglobal : T2 → T3)
    (batch_addr : Int → T5 → Int)
    (b' : T5)
    (batch_bytes : T5 → Int)
    (h1 : (1 ≤ kQuarantineBatchClass ∧ kQuarantineBatchClass ≤ 30))
    (h2 : (Int.fdiv (kb * (class_size kQuarantineBatchClass)) kCompactPtrScale) = (kb * 512))
    (h3 : (bv_unsigned kw) = (kb * 512))
    (h4 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h5 : kHighMemBeg ≤ b)
    (h6 : (b + 8192) ≤ alloc_ceiling)
    (h7 : (bv_unsigned kw) < (2 ^ (32 : Nat)))
    (h8 : (1 ≤ n0 ∧ n0 < (2 ^ (32 : Nat))))
    (h9 : (p + (8 * ((n0 + 7) / 8))) ≤ alloc_ceiling)
    (h10 : ((a_sb A) + (2 ^ (37 : Nat))) ≤ (2 ^ (47 : Nat)))
    (h11 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h12 : 0 ≤ (ebytes (ba_entries b0)))
    (h13 : 0 ≤ (ebytes es))
    (h14 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h15 : 0 ≤ (q_bytes (a_qglobal A)))
    (h16 : (((length (a_qglobal A)) : Nat) : Int) ≠ 0)
    (h17 : (batch_addr (a_sb A) b') = b)
    (h18 : (batch_bytes b') = (n0 + 8192)) :
    (p + (-16)) = (p - 16) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeG2c.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (p_thr : T1 → Int)
    (a_pl : T2 → T1)
    (A : T2)
    (kQuarantineBatchClass : Int)
    (kb : Int)
    (class_size : Int → Int)
    (kCompactPtrScale : Int)
    (bv_unsigned : T3 → Int)
    (kw : T3)
    (a_sb : T2 → Int)
    (b : Int)
    (p : Int)
    (n0 : Int)
    (kHighMemBeg : Int)
    (alloc_ceiling : Int)
    (length : T4 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T4 → Int)
    (r : T4)
    (ba_entries : T5 → T4)
    (b0 : T5)
    (ebytes : T4 → Int)
    (es : T4)
    (a_qglobal : T2 → T4)
    (batch_addr : Int → T6 → Int)
    (b' : T6)
    (batch_bytes : T6 → Int)
    (ks24 : T4)
    (h1 : (1 ≤ kQuarantineBatchClass ∧ kQuarantineBatchClass ≤ 30))
    (h2 : (Int.fdiv (kb * (class_size kQuarantineBatchClass)) kCompactPtrScale) = (kb * 512))
    (h3 : (bv_unsigned kw) = (kb * 512))
    (h4 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h5 : kHighMemBeg ≤ b)
    (h6 : (b + 8192) ≤ alloc_ceiling)
    (h7 : (bv_unsigned kw) < (2 ^ (32 : Nat)))
    (h8 : (1 ≤ n0 ∧ n0 < (2 ^ (32 : Nat))))
    (h9 : (p + (8 * ((n0 + 7) / 8))) ≤ alloc_ceiling)
    (h10 : ((a_sb A) + (2 ^ (37 : Nat))) ≤ (2 ^ (47 : Nat)))
    (h11 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h12 : 0 ≤ (ebytes (ba_entries b0)))
    (h13 : 0 ≤ (ebytes es))
    (h14 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h15 : 0 ≤ (q_bytes (a_qglobal A)))
    (h16 : (((length (a_qglobal A)) : Nat) : Int) ≠ 0)
    (h17 : (batch_addr (a_sb A) b') = b)
    (h18 : (batch_bytes b') = (n0 + 8192))
    (h19 : 1 ≤ (length ks24)) :
    (((p_thr (a_pl A)) + 208) + 1920) = (((p_thr (a_pl A)) + (208 + (80 * 24))) + 0) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeGDc.v (replace)
example
    {word : Type}
    (rac : word)
    (spd : word)
    (stkobj : Int)
    (lo : Int)
    (hi : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : lo ≤ ((bv_unsigned spd) - 4096))
    (h3 : (bv_unsigned spd) ≤ hi)
    (h4 : hi ≤ (2 ^ (47 : Nat)))
    (h5 : ((bv_unsigned spd) % 16) = 0)
    (h6 : ((bv_unsigned rac) % 2) = 0)
    (h7 : (bv_unsigned spd) ≤ stkobj)
    (h8 : (stkobj + 2064) ≤ hi) :
    lo = (hi - (hi - lo)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeH5e.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (lb : Int)
    (thr : Int)
    (ri : Int)
    (sb : Int)
    (w : T1)
    (h1 : ((lb + 8192) ≤ thr ∨ (thr + 4096) ≤ lb))
    (h2 : ((lb + 8192) ≤ ri ∨ (ri + 4096) ≤ lb))
    (h3 : ((lb + 8192) ≤ ((sb + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned w))) ∨ (((sb + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned w))) + 8192) ≤ lb)) :
    (((bv_unsigned sp) + (-64)) + (-32)) = (((((bv_unsigned sp) + 112) + (-128)) + (-48)) + (-32)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeKR.v (replace)
example
    (p : Int)
    (n0 : Int)
    (sh : Int → Int)
    (map_size : Int → Int)
    (h1 : (sh ((p - 6144) + (map_size n0))) = ((sh (p - 6144)) + ((map_size n0) / 8)))
    (h2 : ((p - 6144) / 8) = (512 * ((p - 6144) / 4096))) :
    ((512 * ((p - 6144) / 4096)) * 8) = (4096 * ((p - 6144) / 4096)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeKR.v (replace)
example
    {AState T2 T3 : Type}
    (A : AState)
    (length : T2 → Nat)
    (sr_chunks : T3 → T2)
    (a_sec : AState → T3) :
    ((length (sr_chunks (a_sec A))) - 1) = (Int.toNat ((((length (sr_chunks (a_sec A))) : Nat) : Int) - 1)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeR.v (replace)
example (b1 : Int) :
    ((0 + (256 * b1)) + (65536 * 0)) = (256 * b1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeRG3.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (region_beg : Int → Int → Int)
    (a_sb : T1 → Int)
    (A : T1)
    (kQuarantineBatchClass : Int)
    (b : Int)
    (i : Int)
    (qc_last : T1 → T2 → Int)
    (qt : T2)
    (lb : Int)
    (length : T2 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T2 → Int)
    (r : T2)
    (ba_entries : T3 → T4)
    (b0 : T3)
    (ebytes : T4 → Int)
    (es : T4)
    (a_qglobal : T1 → T2)
    (kb : Int)
    (class_size : Int → Int)
    (kCompactPtrScale : Int)
    (bv_unsigned : T5 → Int)
    (kw : T5)
    (kHighMemBeg : Int)
    (alloc_ceiling : Int)
    (h1 : (qc_last A qt) = lb)
    (h2 : (((length qt) : Nat) : Int) ≠ 0)
    (h3 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h4 : 0 ≤ (ebytes (ba_entries b0)))
    (h5 : 0 ≤ (ebytes es))
    (h6 : ((((length qt) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes qt))
    (h7 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h8 : 0 ≤ (q_bytes qt))
    (h9 : 0 ≤ (q_bytes (a_qglobal A)))
    (h10 : (1 ≤ kQuarantineBatchClass ∧ kQuarantineBatchClass ≤ 30))
    (h11 : (Int.fdiv (kb * (class_size kQuarantineBatchClass)) kCompactPtrScale) = (kb * 512))
    (h12 : (bv_unsigned kw) = (kb * 512))
    (h13 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h14 : kHighMemBeg ≤ b)
    (h15 : (b + 8192) ≤ alloc_ceiling) :
    ((region_beg (a_sb A) kQuarantineBatchClass) + ((b - (region_beg (a_sb A) kQuarantineBatchClass)) + i)) = (b + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeRG3.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (b : Int)
    (i : Int)
    (qc_last : T1 → T2 → Int)
    (A : T1)
    (qt : T2)
    (lb : Int)
    (length : T2 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T2 → Int)
    (r : T2)
    (ba_entries : T3 → T4)
    (b0 : T3)
    (ebytes : T4 → Int)
    (es : T4)
    (a_qglobal : T1 → T2)
    (kQuarantineBatchClass : Int)
    (kb : Int)
    (class_size : Int → Int)
    (kCompactPtrScale : Int)
    (bv_unsigned : T5 → Int)
    (kw : T5)
    (a_sb : T1 → Int)
    (kHighMemBeg : Int)
    (alloc_ceiling : Int)
    (h1 : (qc_last A qt) = lb)
    (h2 : (((length qt) : Nat) : Int) ≠ 0)
    (h3 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h4 : 0 ≤ (ebytes (ba_entries b0)))
    (h5 : 0 ≤ (ebytes es))
    (h6 : ((((length qt) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes qt))
    (h7 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h8 : 0 ≤ (q_bytes qt))
    (h9 : 0 ≤ (q_bytes (a_qglobal A)))
    (h10 : (1 ≤ kQuarantineBatchClass ∧ kQuarantineBatchClass ≤ 30))
    (h11 : (Int.fdiv (kb * (class_size kQuarantineBatchClass)) kCompactPtrScale) = (kb * 512))
    (h12 : (bv_unsigned kw) = (kb * 512))
    (h13 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h14 : kHighMemBeg ≤ b)
    (h15 : (b + 8192) ≤ alloc_ceiling) :
    (b + (8 + i)) = ((b + 8) + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeRK2.v (replace)
example
    {AState T2 : Type}
    (A : AState)
    (a : Int)
    (k : Int)
    (p_thr : T2 → Int)
    (a_pl : AState → T2)
    (i : Int)
    (a_cache_inited : AState → Bool)
    (h1 : (a_cache_inited A) = true)
    (h2 : (p_thr (a_pl A)) ≤ a)
    (h3 : (a + k) ≤ ((p_thr (a_pl A)) + 4096)) :
    ((p_thr (a_pl A)) + ((a - (p_thr (a_pl A))) + i)) = (a + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeRK2.v (replace)
example
    {T1 T2 T3 : Type}
    (h_1 : Nat)
    (A : T1)
    (free_array_of : T2 → T3 → Int)
    (a_sb : T1 → T2)
    (c : T3)
    (region_beg : T2 → T3 → Int)
    (kFreeArrayOffset : Int)
    (h1 : (free_array_of (a_sb A) c) = ((region_beg (a_sb A) c) + kFreeArrayOffset)) :
    (((4 * h_1) : Nat) : Int) = (4 * ((h_1 : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreeRK2.v (replace)
example (a : Int) (i : Nat) :
    ((a + 24) + (8 * ((i : Nat) : Int))) = (a + (24 + (8 * ((i : Nat) : Int)))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AFreldj.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (b : Int)
    (qc_last : T1 → T2 → Int)
    (A : T1)
    (qt : T2)
    (lb : Int)
    (length : T2 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T2 → Int)
    (r : T2)
    (ba_entries : T3 → T4)
    (b0 : T3)
    (ebytes : T4 → Int)
    (es : T4)
    (a_qglobal : T1 → T2)
    (kQuarantineBatchClass : Int)
    (bv_unsigned : T5 → Int)
    (kw : T5)
    (kb : Int)
    (a_sb : T1 → Int)
    (free_array_of : Int → Int → Int)
    (h1 : (qc_last A qt) = lb)
    (h2 : (((length qt) : Nat) : Int) ≠ 0)
    (h3 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h4 : 0 ≤ (ebytes (ba_entries b0)))
    (h5 : 0 ≤ (ebytes es))
    (h6 : ((((length qt) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes qt))
    (h7 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h8 : 0 ≤ (q_bytes qt))
    (h9 : 0 ≤ (q_bytes (a_qglobal A)))
    (h10 : (1 ≤ kQuarantineBatchClass ∧ kQuarantineBatchClass ≤ 30))
    (h11 : (bv_unsigned kw) = (kb * 512))
    (h12 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h13 : (lb + 8192) ≤ (free_array_of (a_sb A) 24)) :
    (b + 8) = (b + ((8 : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AIcp7wm.v (replace)
example (a : Int) (shadow_off : Int) :
    (((a / 8) + shadow_off) + ((0 : Nat) : Int)) = ((a / 8) + shadow_off) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AIcpm9j.v (lemma)
example
    (a : Int)
    (lo : Int)
    (hi : Int)
    (lo' : Int)
    (hi' : Int)
    (h1 : (¬ (lo' ≤ a ∧ a < hi')))
    (h2 : lo' ≤ lo)
    (h3 : hi ≤ hi') :
    (¬ (lo ≤ a ∧ a < hi)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AIcpnnp.v (replace)
example
    {T1 : Type}
    (i : Nat)
    (bv_unsigned : T1 → Int)
    (a0 : T1)
    (h1 : (0 ≤ (bv_unsigned a0) ∧ ((((bv_unsigned a0) + ((i : Nat) : Int)) + 1) + 8) ≤ 140737488355328)) :
    (((i : Nat) : Int) + (bv_unsigned a0)) = (((bv_unsigned a0) + (((i : Nat) : Int) + 1)) - 1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AIcpnnp.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (i : Nat)
    (bv_unsigned : T1 → Int)
    (a0 : T1)
    (sha : Int → Int)
    (length : T2 → Nat)
    (le8 : T3 → T2)
    (w1 : T3)
    (w2 : T3)
    (shadow_off : Int)
    (sbs : T2)
    (strchr_res : Int → T4 → T2 → Int)
    (c : T4)
    (str : T2)
    (h1 : (0 ≤ (bv_unsigned a0) ∧ ((((bv_unsigned a0) + ((i : Nat) : Int)) + 1) + 8) ≤ 140737488355328))
    (h2 : (((sha (bv_unsigned a0)) - ((sha (bv_unsigned a0)) % 8)) + (((length (le8 w1)) : Nat) : Int)) ≤ 17594333528064)
    (h3 : (((sha (((i : Nat) : Int) + (bv_unsigned a0))) - ((sha (((i : Nat) : Int) + (bv_unsigned a0))) % 8)) + (((length (le8 w2)) : Nat) : Int)) ≤ 17594333528064)
    (h4 : ((((bv_unsigned a0) / 8) + shadow_off) + (((length sbs) : Nat) : Int)) ≤ 17594333528064)
    (h5 : (((strchr_res (bv_unsigned a0) c str) = 0 ∧ i = (length str)) ∨ ((strchr_res (bv_unsigned a0) c str) = ((bv_unsigned a0) + ((i : Nat) : Int)) ∧ i < (length str)))) :
    ((i : Nat) : Int) = (((bv_unsigned a0) + ((i : Nat) : Int)) - (bv_unsigned a0)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AIcpnnp.v (replace)
example
    {T1 : Type}
    (i : Nat)
    (bv_unsigned : T1 → Int)
    (a0 : T1)
    (a1 : T1)
    (h1 : (0 ≤ (bv_unsigned a0) ∧ ((((bv_unsigned a0) + ((i : Nat) : Int)) + 1) + 8) ≤ 140737488355328))
    (h2 : (0 ≤ (bv_unsigned a1) ∧ ((((bv_unsigned a1) + ((i : Nat) : Int)) + 1) + 8) ≤ 140737488355328)) :
    (((i : Nat) : Int) + (bv_unsigned a0)) = (((bv_unsigned a0) + (((i : Nat) : Int) + 1)) - 1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AMalc5w.v (replace)
example
    {word : Type}
    (sp : word)
    (tp : word)
    (lo : Int)
    (n : Int)
    (c : Int)
    (sb : Int)
    (AB : Int)
    (cra : word)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (size_class : Int → Int)
    (needed_size : Int → Int)
    (kHighMemBeg : Int)
    (class_size : Int → Int)
    (rounded_size : Int → Int)
    (rz_size : Int → Int)
    (h1 : (alloc_ceiling ≤ lo ∧ lo ≤ ((bv_unsigned sp) - 1024)))
    (h2 : ((bv_unsigned sp) % 16) = 0)
    (h3 : ((bv_unsigned sp) + 65536) < (2 ^ (64 : Nat)))
    (h4 : (1 ≤ n ∧ n ≤ 64512))
    (h5 : ((bv_unsigned cra) % 2) = 0)
    (h6 : c = (size_class (needed_size n)))
    (h7 : ((65536 + 88) ≤ (bv_unsigned tp) ∧ ((bv_unsigned tp) + 64) ≤ 6332416))
    (h8 : (kHighMemBeg ≤ sb ∧ (sb + (2 ^ (37 : Nat))) ≤ alloc_ceiling))
    (h9 : (AB % 32) = 0)
    (h10 : (sb ≤ AB ∧ (AB + (class_size c)) ≤ (sb + (2 ^ (37 : Nat)))))
    (h11 : ((rounded_size n) + (rz_size n)) = (needed_size n))
    (h12 : (1 ≤ (needed_size n) ∧ (needed_size n) ≤ 65536))
    (h13 : 0 ≤ lo)
    (h14 : 32 ≤ (rz_size n)) :
    ((bv_unsigned tp) + 16) = (16 + (bv_unsigned tp)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/ANodl61.v (replace)
example (rb : Int) (mfa : Int) :
    ((rb + 3758096384) + mfa) = (mfa + (rb + 3758096384)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/APopT.v (replace)
example {word : Type} (spa : word) (lo : Int) (bv_unsigned : word → Int) (i : Int) :
    ((bv_unsigned spa) + ((lo + i) - (bv_unsigned spa))) = (lo + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/APopTE.v (replace)
example
    {word AState list_word T4 : Type}
    (rac : word)
    (spa : word)
    (A : AState)
    (n : Int)
    (stkobj : Int)
    (lo : Int)
    (hi : Int)
    (ums : Int)
    (fam : Int)
    (nc : Int)
    (ksc : list_word)
    (bv_unsigned : word → Int)
    (x : word)
    (a_ri : AState → Int)
    (class_of : Int → Int)
    (kMaxPrimaryUser : Int)
    (as_tinycred : AState → Int)
    (prim_cost : Int → Int)
    (as_primcred : AState → Int)
    (as_livebytes : AState → Int)
    (LIVE_MAX : Int)
    (as_nlive : AState → Int)
    (NLIVE_MAX : Int)
    (alloc_ceiling : Int)
    (kUserMapSize : Int)
    (rg_mapped_user : T4 → Int)
    (a_reg : AState → Int → T4)
    (rg_allocated_user : T4 → Int)
    (class_size : Int → Int)
    (length : list_word → Nat)
    (a_paid : AState → Int → list_word)
    (class_slack : Int → Int)
    (kFreeArrayMapSize : Int)
    (rg_mapped_fa : T4 → Int)
    (kFreeArraySize : Int)
    (rg_free : T4 → list_word)
    (refill_count : Int → Int)
    (h1 : (1 ≤ n ∧ n ≤ kMaxPrimaryUser))
    (h2 : (n < 16 → 1 ≤ (as_tinycred A)))
    (h3 : (prim_cost n) ≤ (as_primcred A))
    (h4 : ((as_livebytes A) + n) ≤ LIVE_MAX)
    (h5 : ((as_nlive A) + 1) ≤ NLIVE_MAX)
    (h6 : alloc_ceiling ≤ lo)
    (h7 : lo ≤ ((bv_unsigned spa) - 4096))
    (h8 : (bv_unsigned spa) ≤ hi)
    (h9 : hi ≤ (2 ^ (47 : Nat)))
    (h10 : ((bv_unsigned spa) % 16) = 0)
    (h11 : ((bv_unsigned rac) % 2) = 0)
    (h12 : (bv_unsigned spa) ≤ stkobj)
    (h13 : (stkobj + 2064) ≤ hi)
    (h14 : (0 ≤ ums ∧ ((Int.fmod ums kUserMapSize) = 0 ∧ (((rg_mapped_user (a_reg A (class_of n))) + ums) < (((rg_allocated_user (a_reg A (class_of n))) + (9 * (class_size (class_of n)))) + kUserMapSize) ∧ (rg_allocated_user (a_reg A (class_of n))) ≤ (((class_size (class_of n)) * ((((length (a_paid A (class_of n))) : Nat) : Int) + 7)) + (class_slack (class_of n)))))))
    (h15 : (0 ≤ fam ∧ ((Int.fmod fam kFreeArrayMapSize) = 0 ∧ (((rg_mapped_fa (a_reg A (class_of n))) + fam) ≤ ((4 * (Int.fdiv (rg_allocated_user (a_reg A (class_of n))) (class_size (class_of n)))) + kFreeArrayMapSize) ∧ ((rg_mapped_fa (a_reg A (class_of n))) + fam) ≤ kFreeArraySize))))
    (h16 : (0 ≤ nc ∧ (((rg_allocated_user (a_reg A (class_of n))) + (nc * (class_size (class_of n)))) ≤ ((rg_mapped_user (a_reg A (class_of n))) + ums) ∧ (4 * ((((length (rg_free (a_reg A (class_of n)))) : Nat) : Int) + nc)) ≤ ((rg_mapped_fa (a_reg A (class_of n))) + fam))))
    (h17 : (((rg_mapped_user (a_reg A (class_of n))) + ums) = 0 → (fam = 0 ∧ nc = 0)))
    (h18 : ((rg_mapped_user (a_reg A (class_of n))) + ums) < ((((rg_allocated_user (a_reg A (class_of n))) + (nc * (class_size (class_of n)))) + (9 * (class_size (class_of n)))) + kUserMapSize))
    (h19 : (refill_count (class_of n)) ≤ ((((length (rg_free (a_reg A (class_of n)))) : Nat) : Int) + nc))
    (h20 : (length ksc) = 16) :
    (bv_unsigned x) = (((a_ri A) + (128 * (class_of n))) + ((bv_unsigned x) - ((a_ri A) + (128 * (class_of n))))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/APopTE.v (replace)
example
    {AState list_word T3 T4 T5 : Type}
    (A : AState)
    (n : Int)
    (ums : Int)
    (fam : Int)
    (nc : Int)
    (ksc : list_word)
    (sh : Int → Int)
    (region_beg : T3 → T4 → Int)
    (a_sb : AState → T3)
    (class_of : Int → T4)
    (kFreeArrayOffset : Int)
    (rg_mapped_fa : T5 → Int)
    (a_reg : AState → T4 → T5)
    (z : Int)
    (kMaxPrimaryUser : Int)
    (as_tinycred : AState → Int)
    (prim_cost : Int → Int)
    (as_primcred : AState → Int)
    (as_livebytes : AState → Int)
    (LIVE_MAX : Int)
    (as_nlive : AState → Int)
    (NLIVE_MAX : Int)
    (kUserMapSize : Int)
    (rg_mapped_user : T5 → Int)
    (rg_allocated_user : T5 → Int)
    (class_size : T4 → Int)
    (length : list_word → Nat)
    (a_paid : AState → T4 → list_word)
    (class_slack : T4 → Int)
    (kFreeArrayMapSize : Int)
    (kFreeArraySize : Int)
    (rg_free : T5 → list_word)
    (refill_count : T4 → Int)
    (h1 : (1 ≤ n ∧ n ≤ kMaxPrimaryUser))
    (h2 : (n < 16 → 1 ≤ (as_tinycred A)))
    (h3 : (prim_cost n) ≤ (as_primcred A))
    (h4 : ((as_livebytes A) + n) ≤ LIVE_MAX)
    (h5 : ((as_nlive A) + 1) ≤ NLIVE_MAX)
    (h6 : (0 ≤ ums ∧ ((Int.fmod ums kUserMapSize) = 0 ∧ (((rg_mapped_user (a_reg A (class_of n))) + ums) < (((rg_allocated_user (a_reg A (class_of n))) + (9 * (class_size (class_of n)))) + kUserMapSize) ∧ (rg_allocated_user (a_reg A (class_of n))) ≤ (((class_size (class_of n)) * ((((length (a_paid A (class_of n))) : Nat) : Int) + 7)) + (class_slack (class_of n)))))))
    (h7 : (0 ≤ fam ∧ ((Int.fmod fam kFreeArrayMapSize) = 0 ∧ (((rg_mapped_fa (a_reg A (class_of n))) + fam) ≤ ((4 * (Int.fdiv (rg_allocated_user (a_reg A (class_of n))) (class_size (class_of n)))) + kFreeArrayMapSize) ∧ ((rg_mapped_fa (a_reg A (class_of n))) + fam) ≤ kFreeArraySize))))
    (h8 : (0 ≤ nc ∧ (((rg_allocated_user (a_reg A (class_of n))) + (nc * (class_size (class_of n)))) ≤ ((rg_mapped_user (a_reg A (class_of n))) + ums) ∧ (4 * ((((length (rg_free (a_reg A (class_of n)))) : Nat) : Int) + nc)) ≤ ((rg_mapped_fa (a_reg A (class_of n))) + fam))))
    (h9 : (((rg_mapped_user (a_reg A (class_of n))) + ums) = 0 → (fam = 0 ∧ nc = 0)))
    (h10 : ((rg_mapped_user (a_reg A (class_of n))) + ums) < ((((rg_allocated_user (a_reg A (class_of n))) + (nc * (class_size (class_of n)))) + (9 * (class_size (class_of n)))) + kUserMapSize))
    (h11 : (refill_count (class_of n)) ≤ ((((length (rg_free (a_reg A (class_of n)))) : Nat) : Int) + nc))
    (h12 : (length ksc) = 16)
    (h13 : (0 ≤ z ∧ z < (2 ^ (64 : Nat))))
    (h14 : (¬ ((sh ((region_beg (a_sb A) (class_of n)) + (rg_mapped_user (a_reg A (class_of n))))) ≤ z ∧ z < ((sh ((region_beg (a_sb A) (class_of n)) + (rg_mapped_user (a_reg A (class_of n))))) + (ums / 8)))))
    (h15 : (¬ ((sh (((region_beg (a_sb A) (class_of n)) + kFreeArrayOffset) + (rg_mapped_fa (a_reg A (class_of n))))) ≤ z ∧ z < ((sh (((region_beg (a_sb A) (class_of n)) + kFreeArrayOffset) + (rg_mapped_fa (a_reg A (class_of n))))) + (fam / 8))))) :
    ((sh (((region_beg (a_sb A) (class_of n)) + kFreeArrayOffset) + (rg_mapped_fa (a_reg A (class_of n))))) + (z - (sh (((region_beg (a_sb A) (class_of n)) + kFreeArrayOffset) + (rg_mapped_fa (a_reg A (class_of n))))))) = z := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/ARt_u2d.v (replace)
example
    {T1 : Type}
    (T : Int)
    (n : Int)
    (length : T1 → Nat)
    (j7 : T1)
    (h1 : (1 ≤ n ∧ n ≤ 255))
    (h2 : (length j7) = (Int.toNat (8 * n))) :
    (T + (n + 1)) = ((n + 1) + T) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/ASecB5.v (replace)
example {T1 T2 : Type} (sh : T1 → Int) (sec_alloc_beg : T2 → T1) (mb : T2) :
    ((sh (sec_alloc_beg mb)) + 256) = ((sh (sec_alloc_beg mb)) + ((256 : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/ASma77w.v (replace)
example
    {word AState : Type}
    (k : Int)
    (ra : word)
    (sp : word)
    (A : AState)
    (sz : Int)
    (a_fs : AState → Int)
    (a : Int)
    (fsize : Int → Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (ASTK : Int)
    (nsh : Int)
    (h1 : (k = 0 ∨ (k = 1 ∨ k = 7)))
    (h2 : (0 < sz ∧ sz ≤ (fsize k)))
    (h3 : (7 ≤ k → (sz % 8) = 0))
    (h4 : ((bv_unsigned sp) % 16) = 0)
    (h5 : ((bv_unsigned ra) % 2) = 0)
    (h6 : alloc_ceiling ≤ ((bv_unsigned sp) - ASTK))
    (h7 : (0 ≤ nsh ∧ nsh ≤ ((fsize k) / 8)))
    (h8 : ((bv_unsigned sp) - 8192) ≤ ((bv_unsigned sp) - 224))
    (h9 : (k = 7 → ((sz % 8) = 0 ∧ (8 ≤ sz ∧ sz ≤ (fsize 7))))) :
    ((a_fs A) + (a - (a_fs A))) = a := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/ASma77w.v (replace)
example
    {word AState T3 : Type}
    (k : Int)
    (ra : word)
    (sp : word)
    (A : AState)
    (sz : Int)
    (sh : T3 → Int)
    (a_fs : AState → T3)
    (a : Int)
    (fsize : Int → Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (ASTK : Int)
    (nsh : Int)
    (h1 : (k = 0 ∨ (k = 1 ∨ k = 7)))
    (h2 : (0 < sz ∧ sz ≤ (fsize k)))
    (h3 : (7 ≤ k → (sz % 8) = 0))
    (h4 : ((bv_unsigned sp) % 16) = 0)
    (h5 : ((bv_unsigned ra) % 2) = 0)
    (h6 : alloc_ceiling ≤ ((bv_unsigned sp) - ASTK))
    (h7 : (0 ≤ nsh ∧ nsh ≤ ((fsize k) / 8)))
    (h8 : ((bv_unsigned sp) - 8192) ≤ ((bv_unsigned sp) - 224))
    (h9 : (k = 7 → ((sz % 8) = 0 ∧ (8 ≤ sz ∧ sz ≤ (fsize 7))))) :
    ((sh (a_fs A)) + (a - (sh (a_fs A)))) = a := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AState.v (replace)
example
    (h_1 : Int)
    (k : Int)
    (a1 : Nat)
    (a2 : Nat)
    (fslots : Int → Int)
    (n : Int)
    (h1 : (0 ≤ k ∧ k ≤ 10))
    (h2 : ((a1 : Nat) : Int) < (fslots k))
    (h3 : ((a2 : Nat) : Int) < (fslots k))
    (h4 : (Int.fmod (((h_1 - 1) - ((a1 : Nat) : Int)) - ((h_1 - 1) - ((a2 : Nat) : Int))) n) = 0)
    (h5 : (Int.fmod (((a1 : Nat) : Int) - ((a2 : Nat) : Int)) n) = 0) :
    (-(((a2 : Nat) : Int) - ((a1 : Nat) : Int))) = (((a1 : Nat) : Int) - ((a2 : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AWrapR.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (alloc_ceiling : Int)
    (ra : T1)
    (s0 : T1)
    (cl_tp : T2 → T1)
    (LPA : T2)
    (p : Int)
    (h1 : (alloc_ceiling ≤ ((bv_unsigned sp) - 8192) ∧ ((bv_unsigned sp) - 8192) ≤ ((bv_unsigned sp) - 2192)))
    (h2 : 4096 ≤ (bv_unsigned ra))
    (h3 : (bv_unsigned ra) ≠ 364776)
    (h4 : (bv_unsigned s0) ≤ (bv_unsigned sp))
    (h5 : (bv_unsigned (cl_tp LPA)) = 6194136)
    (h6 : 16 ≤ p) :
    (((bv_unsigned sp) + (-2136)) + 8) = (((bv_unsigned sp) + (-2136)) + ((8 : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AWrapR.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (alloc_ceiling : Int)
    (ra : T1)
    (s0 : T1)
    (cl_tp : T2 → T1)
    (LPA : T2)
    (p : Int)
    (h1 : (alloc_ceiling ≤ ((bv_unsigned sp) - 8192) ∧ ((bv_unsigned sp) - 8192) ≤ ((bv_unsigned sp) - 2192)))
    (h2 : 4096 ≤ (bv_unsigned ra))
    (h3 : (bv_unsigned ra) ≠ 364776)
    (h4 : (bv_unsigned s0) ≤ (bv_unsigned sp))
    (h5 : (bv_unsigned (cl_tp LPA)) = 6194136)
    (h6 : 16 ≤ p) :
    8192 = ((bv_unsigned sp) - ((bv_unsigned sp) - 8192)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AWrapR.v (replace)
example
    {T1 T2 : Type}
    (r : Int)
    (p : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (ra : T1)
    (s0 : T1)
    (cl_tp : T2 → T1)
    (LPA : T2)
    (thr : Int)
    (old : Int)
    (a : Int)
    (n : Int)
    (h1 : (alloc_ceiling ≤ ((bv_unsigned sp) - 8192) ∧ ((bv_unsigned sp) - 8192) ≤ ((bv_unsigned sp) - 2192)))
    (h2 : 4096 ≤ (bv_unsigned ra))
    (h3 : (bv_unsigned ra) ≠ 364776)
    (h4 : (bv_unsigned s0) ≤ (bv_unsigned sp))
    (h5 : (bv_unsigned (cl_tp LPA)) = 6194136)
    (h6 : 16 ≤ p)
    (h7 : (¬ (thr ≤ a ∧ a < (thr + 4096))))
    (h8 : p ≠ r)
    (h9 : (0 < r ∧ r < (2 ^ (64 : Nat))))
    (h10 : ((p + old) ≤ r ∨ (r + n) ≤ (p + (-16)))) :
    (max r (p + (-16))) = (r + ((max r (p + (-16))) - r)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AWrapR.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (alloc_ceiling : Int)
    (ra : T1)
    (s0 : T1)
    (cl_tp : T2 → T1)
    (LPA : T2)
    (p : Int)
    (thr : Int)
    (old : Int)
    (a : Int)
    (n : Int)
    (r : Int)
    (length : T3 → Nat)
    (src : T3)
    (h1 : (alloc_ceiling ≤ ((bv_unsigned sp) - 8192) ∧ ((bv_unsigned sp) - 8192) ≤ ((bv_unsigned sp) - 2192)))
    (h2 : 4096 ≤ (bv_unsigned ra))
    (h3 : (bv_unsigned ra) ≠ 364776)
    (h4 : (bv_unsigned s0) ≤ (bv_unsigned sp))
    (h5 : (bv_unsigned (cl_tp LPA)) = 6194136)
    (h6 : 16 ≤ p)
    (h7 : (¬ (thr ≤ a ∧ a < (thr + 4096))))
    (h8 : p ≠ r)
    (h9 : (0 < r ∧ r < (2 ^ (64 : Nat))))
    (h10 : ((p + old) ≤ r ∨ (r + n) ≤ (p + (-16))))
    (h11 : ((0 ≤ (min n old) ∧ (min n old) ≤ old) ∧ (min n old) ≤ n))
    (h12 : (length src) = (Int.toNat (min n old))) :
    (((bv_unsigned sp) + (-2136)) + 8) = (((bv_unsigned sp) + (-2136)) + ((8 : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Yr/AWrapR.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (alloc_ceiling : Int)
    (ra : T1)
    (s0 : T1)
    (cl_tp : T2 → T1)
    (LPA : T2)
    (p : Int)
    (thr : Int)
    (old : Int)
    (a : Int)
    (n : Int)
    (r : Int)
    (length : T3 → Nat)
    (src : T3)
    (h1 : (alloc_ceiling ≤ ((bv_unsigned sp) - 8192) ∧ ((bv_unsigned sp) - 8192) ≤ ((bv_unsigned sp) - 2192)))
    (h2 : 4096 ≤ (bv_unsigned ra))
    (h3 : (bv_unsigned ra) ≠ 364776)
    (h4 : (bv_unsigned s0) ≤ (bv_unsigned sp))
    (h5 : (bv_unsigned (cl_tp LPA)) = 6194136)
    (h6 : 16 ≤ p)
    (h7 : (¬ (thr ≤ a ∧ a < (thr + 4096))))
    (h8 : p ≠ r)
    (h9 : (0 < r ∧ r < (2 ^ (64 : Nat))))
    (h10 : ((p + old) ≤ r ∨ (r + n) ≤ (p + (-16))))
    (h11 : ((0 ≤ (min n old) ∧ (min n old) ≤ old) ∧ (min n old) ≤ n))
    (h12 : (length src) = (Int.toNat (min n old))) :
    (((bv_unsigned sp) + (-2136)) + 8) = ((bv_unsigned sp) + (-2128)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zd/DA_H5g8.v (replace)
example
    {word T2 : Type}
    (pa : Int)
    (len : Int)
    (ng : Nat)
    (lastb : Int)
    (w1 : word)
    (w2 : word)
    (sha : Int → Int)
    (length : T2 → Nat)
    (le8 : word → T2)
    (Z_shiftr : Int → Int → Int)
    (h1 : (65536 ≤ pa ∧ (pa + len) ≤ 217088))
    (h2 : (1 ≤ len ∧ len ≤ 64))
    (h3 : ((((pa + len) - 1) / 8) - (pa / 8)) = ((ng : Nat) : Int))
    (h4 : (lastb = 0 ∨ ((((pa + len) - 1) % 8) < lastb ∧ lastb ≤ 7)))
    (h5 : (0 ≤ pa ∧ ((pa + len) + 8) ≤ 140737488355328))
    (h6 : (((sha pa) - ((sha pa) % 8)) + (((length (le8 w1)) : Nat) : Int)) ≤ 17594333528064)
    (h7 : (((sha ((pa + len) + (-1))) - ((sha ((pa + len) + (-1))) % 8)) + (((length (le8 w2)) : Nat) : Int)) ≤ 17594333528064)
    (h8 : (0 ≤ (Z_shiftr pa 3) ∧ (Z_shiftr pa 3) ≤ pa))
    (h9 : (0 ≤ (Z_shiftr ((pa + len) + (-1)) 3) ∧ (Z_shiftr ((pa + len) + (-1)) 3) ≤ ((pa + len) - 1)))
    (h10 : (0 ≤ lastb ∧ lastb < 128)) :
    ((pa + len) - 1) = ((pa + len) + (-1)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zd/DA_H5g8.v (replace)
example
    (usp : Int)
    (MEMCPY_ICPT_STACK : Int)
    (SPF : Int → Int)
    (alloc_ceiling : Int)
    (b : Int)
    (cap : Nat → Int)
    (k : Nat)
    (c : Int)
    (Zpow : Int → Int → Int)
    (r : Int)
    (h1 : alloc_ceiling = (usp - 8388608))
    (h2 : 6332416 ≤ b)
    (h3 : (SPF usp) = (usp - 128))
    (h4 : (cap k) = 67108864)
    (h5 : (cap (k + 1)) = (2 * c))
    (h6 : c < (2 ^ (26 : Nat)))
    (h7 : (Zpow 2 ((k : Nat) : Int)) ≤ (2 ^ (9 : Nat)))
    (h8 : 6332416 ≤ r)
    (h9 : b ≠ r) :
    MEMCPY_ICPT_STACK = ((SPF usp) - ((SPF usp) - MEMCPY_ICPT_STACK)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zf/PF_L6.v (replace)
example
    (a : Int)
    (n : Int)
    (q : Int)
    (alloc_ceiling : Int)
    (h1 : (alloc_ceiling + 64) ≤ a)
    (h2 : 1 ≤ n)
    (h3 : ((a + n) + 16) ≤ (2 ^ (47 : Nat)))
    (h4 : alloc_ceiling = (16 * q))
    (h5 : (alloc_ceiling / 8) = (2 * q))
    (h6 : (((2 ^ (47 : Nat)) - alloc_ceiling) / 8) = (17592186044416 - (2 * q))) :
    ((17592186044416 - (2 * q)) * 8) = ((2 ^ (47 : Nat)) - (16 * q)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zf/PF_L6.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (diag_fmt_addr : T2 → Int)
    (d : T2)
    (pa : Int)
    (length : T3 → Nat)
    (arg_1 : T3)
    (firstn : Nat → T4 → T3)
    (slack : T4)
    (s3_la : T2 → Int)
    (alloc_ceiling : Int)
    (PC2_DEPTH : Int)
    (lo : Int)
    (FP_DEPTH : Int)
    (RO_TOP : Int)
    (Z_to_bv : Int → Int → T1)
    (VFB_DEPTH : Int)
    (mf_flags : T5 → Int)
    (f0 : T5)
    (mf_lock : T5 → Int)
    (mf_bufsize : T5 → Int)
    (mf_buf : T5 → Int)
    (mf_mode : T5 → Int)
    (IMG_LO : Int)
    (f1 : T5)
    (mf_lbf : T5 → Int)
    (SBUF_LO : Int)
    (SBUF_HI : Int)
    (kHighMemBeg_z : Int)
    (h1 : (((length (firstn 15 slack)) : Nat) : Int) = 15)
    (h2 : lo ≤ ((bv_unsigned sp) - FP_DEPTH))
    (h3 : alloc_ceiling ≤ lo)
    (h4 : (bv_unsigned sp) ≤ (2 ^ (47 : Nat)))
    (h5 : ((diag_fmt_addr d) + (s3_la d)) ≤ RO_TOP)
    (h6 : lo ≤ ((bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-112)))) - VFB_DEPTH))
    (h7 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-112)))) ≤ (2 ^ (47 : Nat)))
    (h8 : (mf_flags f0) = 5)
    (h9 : (mf_lock f0) = (-1))
    (h10 : (mf_bufsize f0) = 0)
    (h11 : (0 < (mf_buf f0) ∧ (mf_buf f0) < (2 ^ (63 : Nat))))
    (h12 : (0 ≤ (mf_mode f0) ∧ (mf_mode f0) < (2 ^ (32 : Nat))))
    (h13 : lo ≤ ((bv_unsigned (Z_to_bv 64 (((bv_unsigned sp) + (-112)) + (-368)))) - PC2_DEPTH))
    (h14 : ((bv_unsigned (Z_to_bv 64 (((bv_unsigned sp) + (-112)) + (-368)))) + 368) ≤ ((bv_unsigned sp) + (-48)))
    (h15 : IMG_LO ≤ (diag_fmt_addr d))
    (h16 : ((bv_unsigned (Z_to_bv 64 (((bv_unsigned sp) + (-112)) + (-368)))) + 368) ≤ pa)
    (h17 : (((pa + (((length arg_1) : Nat) : Int)) + 1) + (((length (firstn 15 slack)) : Nat) : Int)) < (2 ^ (47 : Nat)))
    (h18 : (((length arg_1) : Nat) : Int) ≤ (2 ^ (17 : Nat)))
    (h19 : (mf_flags f1) = 5)
    (h20 : 0 < (mf_buf f1))
    (h21 : ((mf_buf f1) + (mf_bufsize f1)) < (2 ^ (47 : Nat)))
    (h22 : (0 ≤ (mf_bufsize f1) ∧ (mf_bufsize f1) < (2 ^ (31 : Nat))))
    (h23 : (mf_lbf f1) < 0)
    (h24 : (-(2 ^ (31 : Nat))) ≤ (mf_lbf f1))
    (h25 : ((709384 + 152) ≤ (mf_buf f1) ∨ ((mf_buf f1) + (mf_bufsize f1)) ≤ 709384))
    (h26 : (((mf_buf f1) + (mf_bufsize f1)) ≤ lo ∨ ((bv_unsigned (Z_to_bv 64 (((bv_unsigned sp) + (-112)) + (-368)))) + 16) ≤ (mf_buf f1)))
    (h27 : ((SBUF_LO ≤ (mf_buf f1) ∧ ((mf_buf f1) + (mf_bufsize f1)) ≤ SBUF_HI) ∨ kHighMemBeg_z ≤ (mf_buf f1)))
    (h28 : ((mf_buf f1) + (mf_bufsize f1)) ≤ ((bv_unsigned sp) + (-48)))
    (h29 : ((mf_buf f1) + (mf_bufsize f1)) ≤ pa) :
    ((bv_unsigned sp) + (-40)) = (((bv_unsigned sp) + (-48)) + 8) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zf/PF_L7.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (length : T1 → Nat)
    (p : T1)
    (alloc_ceiling : Int)
    (bv_unsigned : T2 → Int)
    (sp : T2)
    (PC2_DEPTH : Int)
    (lo : Int)
    (VP_DEPTH : Int)
    (Z_to_bv : Int → Int → T2)
    (VFB_DEPTH : Int)
    (mf_flags : T3 → Int)
    (stdout_buffered : T4 → T1 → T3)
    (mo : T4)
    (mf_lock : T3 → Int)
    (mf_buf : T3 → Int)
    (mf_bufsize : T3 → Int)
    (va : Int)
    (mf_lbf : T3 → Int)
    (junk : T1)
    (h1 : (0 : Int) ≤ 4)
    (h2 : (0 : Int) ≤ 1024)
    (h3 : lo ≤ ((bv_unsigned sp) - VP_DEPTH))
    (h4 : alloc_ceiling ≤ lo)
    (h5 : lo ≤ ((bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-96)))) - VFB_DEPTH))
    (h6 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-96)))) ≤ (2 ^ (47 : Nat)))
    (h7 : (mf_flags (stdout_buffered mo p)) = 5)
    (h8 : (mf_lock (stdout_buffered mo p)) = (-1))
    (h9 : 0 < (mf_buf (stdout_buffered mo p)))
    (h10 : ((mf_buf (stdout_buffered mo p)) + (mf_bufsize (stdout_buffered mo p))) < (2 ^ (47 : Nat)))
    (h11 : (0 < (mf_bufsize (stdout_buffered mo p)) ∧ (mf_bufsize (stdout_buffered mo p)) < (2 ^ (31 : Nat))))
    (h12 : lo ≤ ((bv_unsigned (Z_to_bv 64 (((bv_unsigned sp) + (-96)) + (-368)))) - PC2_DEPTH))
    (h13 : ((bv_unsigned (Z_to_bv 64 (((bv_unsigned sp) + (-96)) + (-368)))) + 368) ≤ va)
    (h14 : (0 ≤ (mf_bufsize (stdout_buffered mo p)) ∧ (mf_bufsize (stdout_buffered mo p)) < (2 ^ (31 : Nat))))
    (h15 : ((-(2 ^ (31 : Nat))) ≤ (mf_lbf (stdout_buffered mo p)) ∧ (mf_lbf (stdout_buffered mo p)) < (2 ^ (31 : Nat))))
    (h16 : ((((length p) : Nat) : Int) + 2) ≤ (mf_bufsize (stdout_buffered mo p)))
    (h17 : ((((length p) : Nat) : Int) + (((length junk) : Nat) : Int)) = (mf_bufsize (stdout_buffered mo p))) :
    (6324968 + (((length p) : Nat) : Int)) = (6324968 + ((((length p) + 0) : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zf/PF_pc2d.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (h1 : ((bv_unsigned sp) + 112) ≤ (2 ^ (47 : Nat))) :
    ((bv_unsigned sp) + (-416)) = ((((bv_unsigned sp) + (-544)) + ((112 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zk/ASlot_M4.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
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
    (ranges_free : T4 → Int → Int → Bool)
    (p0_reserved : T4)
    (rid : Nat)
    (step_seq : Nat → Nat)
    (get_stride : T5 → Int)
    (big_meta : Nat → Int → T5)
    (q2 : Nat)
    (q : Nat)
    (s_next_rid : Nat → Nat)
    (big_ml : Int → Int)
    (h1 : (bv_unsigned sp') = ((bv_unsigned sp) + (-48)))
    (h2 : st2 = (fst (new_region RKGroup xa ((n + IB) + UNIT) st1)))
    (h3 : L = (round_up_pg ((n + IB) + UNIT)))
    (h4 : (mmap_len ((n + IB) + UNIT)) = L)
    (h5 : ((xa + L) ≤ 65536 ∨ 405504 ≤ xa))
    (h6 : (ranges_free p0_reserved xa L) = true)
    (h7 : (get_stride (big_meta rid n)) = (L - 16))
    (h8 : q2 ≠ q)
    (h9 : q ≠ rid)
    (h10 : (s_next_rid (step_seq st2)) = (rid + 1))
    (h11 : (32 ≤ (big_ml n) ∧ (big_ml n) < (2 ^ (40 : Nat))))
    (h12 : L ≤ (n + 4115)) :
    16 = ((0 + 16) + ((L - 16) * 0)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zk/Instmbo.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (G : Int)
    (conc : T1 → T2 → Int)
    (st : T1)
    (c : T2)
    (r_base : T3 → Int)
    (r : T3)
    (snd : T2 → Int)
    (off2 : Int)
    (off : Int)
    (NB : Int)
    (ND : Int)
    (alloc_ceiling : Int)
    (OLDL : Int)
    (UNIT : Int)
    (n : Int)
    (IB : Int)
    (mmap_len : T4 → Int)
    (r_len : T3 → T4)
    (a : T2)
    (AREA_HDR : Int)
    (META_SIZE : Int)
    (kk : Int)
    (lr_lo : T3 → Int)
    (h1 : (conc st c) = ((r_base r) + (snd c)))
    (h2 : off2 = off)
    (h3 : 4096 ≤ ND)
    (h4 : ND < (2 ^ (40 : Nat)))
    (h5 : (((UNIT + (UNIT * off)) + n) + IB) ≤ ND)
    (h6 : ND < ((((UNIT + (UNIT * off)) + n) + IB) + 4096))
    (h7 : (mmap_len (r_len r)) = OLDL)
    (h8 : 0 ≤ n)
    (h9 : G = ((conc st a) + (AREA_HDR + (META_SIZE * kk))))
    (h10 : (((G + 40) ≤ NB ∨ (NB + ND) ≤ G) ∧ (((G + 40) ≤ (r_base r) ∨ ((r_base r) + OLDL) ≤ G) ∧ ((G + 40) ≤ alloc_ceiling ∧ (((G + 40) ≤ 65536 ∨ 405504 ≤ G) ∧ 0 ≤ G)))))
    (h11 : (lr_lo r) = (r_base r)) :
    (G + 32) = (((G + ((16 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zk/MI_Wje4.v (replace)
example
    {mstate aptr T3 : Type}
    (st : mstate)
    (g : aptr)
    (m_maplen : T3 → Int)
    (MR : mstate → aptr → T3)
    (m_sizeclass : T3 → Int)
    (h1 : (m_sizeclass (MR st g)) = 63) :
    (((m_maplen (MR st g)) * 256) * 16) = ((m_maplen (MR st g)) * 4096) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zk/MI_Wje4.v (replace)
example
    (off : Int)
    (n : Int)
    (NB : Int)
    (ND : Int)
    (alloc_ceiling : Int)
    (UNIT : Int)
    (IB : Int)
    (h1 : 4096 ≤ ND)
    (h2 : (ND % 4096) = 0)
    (h3 : ND < (2 ^ (40 : Nat)))
    (h4 : 0 < NB)
    (h5 : (NB % 4096) = 0)
    (h6 : (NB + ND) ≤ alloc_ceiling)
    (h7 : (((UNIT + (UNIT * off)) + n) + IB) ≤ ND)
    (h8 : ND < ((((UNIT + (UNIT * off)) + n) + IB) + 4096))
    (h9 : (0 ≤ off ∧ off ≤ 255))
    (h10 : 0 ≤ n) :
    (off * 16) = ((16 + (16 * off)) - (0 + 16)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zk/MI_Wje4.v (replace)
example
    {mstate region aptr T4 T5 T6 : Type}
    (st : mstate)
    (rid : Nat)
    (r : region)
    (g : aptr)
    (off : Int)
    (n : Int)
    (NB : Int)
    (ND : Int)
    (Gc : Int)
    (m_sizeclass : T4 → Int)
    (MR : mstate → aptr → T4)
    (alloc_ceiling : Int)
    (UNIT : Int)
    (IB : Int)
    (ranges_free : T5 → Int → Int → Bool)
    (p0_reserved : T5)
    (Bo : Int)
    (lr_lo : region → Int)
    (conc : mstate → T6 → Int)
    (a : T6)
    (AREA_HDR : Int)
    (META_SIZE : Int)
    (kk : Int)
    (fst : T6 → Nat)
    (q : Nat)
    (a' : T6)
    (h1 : (m_sizeclass (MR st g)) = 63)
    (h2 : 4096 ≤ ND)
    (h3 : (ND % 4096) = 0)
    (h4 : ND < (2 ^ (40 : Nat)))
    (h5 : 0 < NB)
    (h6 : (NB % 4096) = 0)
    (h7 : (NB + ND) ≤ alloc_ceiling)
    (h8 : (((UNIT + (UNIT * off)) + n) + IB) ≤ ND)
    (h9 : ND < ((((UNIT + (UNIT * off)) + n) + IB) + 4096))
    (h10 : (0 ≤ off ∧ off ≤ 255))
    (h11 : 0 ≤ n)
    (h12 : (ranges_free p0_reserved NB ND) = true)
    (h13 : (lr_lo r) = Bo)
    (h14 : Gc = ((conc st a) + (AREA_HDR + (META_SIZE * kk))))
    (h15 : (fst a) ≠ rid)
    (h16 : q ≠ (fst a))
    (h17 : (fst a') ≠ rid) :
    (Gc + 24) = ((Gc + 16) + 8) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zk/MI_Wje4.v (replace)
example
    {mstate region aptr T4 T5 T6 : Type}
    (st : mstate)
    (rid : Nat)
    (r : region)
    (g : aptr)
    (off : Int)
    (n : Int)
    (NB : Int)
    (ND : Int)
    (Gc : Int)
    (m_sizeclass : T4 → Int)
    (MR : mstate → aptr → T4)
    (alloc_ceiling : Int)
    (UNIT : Int)
    (IB : Int)
    (ranges_free : T5 → Int → Int → Bool)
    (p0_reserved : T5)
    (Bo : Int)
    (lr_lo : region → Int)
    (conc : mstate → T6 → Int)
    (a : T6)
    (AREA_HDR : Int)
    (META_SIZE : Int)
    (kk : Int)
    (fst : T6 → Nat)
    (q : Nat)
    (a' : T6)
    (h1 : (m_sizeclass (MR st g)) = 63)
    (h2 : 4096 ≤ ND)
    (h3 : (ND % 4096) = 0)
    (h4 : ND < (2 ^ (40 : Nat)))
    (h5 : 0 < NB)
    (h6 : (NB % 4096) = 0)
    (h7 : (NB + ND) ≤ alloc_ceiling)
    (h8 : (((UNIT + (UNIT * off)) + n) + IB) ≤ ND)
    (h9 : ND < ((((UNIT + (UNIT * off)) + n) + IB) + 4096))
    (h10 : (0 ≤ off ∧ off ≤ 255))
    (h11 : 0 ≤ n)
    (h12 : (ranges_free p0_reserved NB ND) = true)
    (h13 : (lr_lo r) = Bo)
    (h14 : Gc = ((conc st a) + (AREA_HDR + (META_SIZE * kk))))
    (h15 : (fst a) ≠ rid)
    (h16 : q ≠ (fst a))
    (h17 : (fst a') ≠ rid) :
    ((Gc + ((16 : Nat) : Int)) + ((8 : Nat) : Int)) = (Gc + 24) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zk/MI_Wje4.v (replace)
example
    {mstate region aptr T4 T5 T6 : Type}
    (st : mstate)
    (rid : Nat)
    (r : region)
    (g : aptr)
    (off : Int)
    (n : Int)
    (NB : Int)
    (ND : Int)
    (m_sizeclass : T4 → Int)
    (MR : mstate → aptr → T4)
    (alloc_ceiling : Int)
    (UNIT : Int)
    (IB : Int)
    (ranges_free : T5 → Int → Int → Bool)
    (p0_reserved : T5)
    (Bo : Int)
    (Gc : Int)
    (lr_lo : region → Int)
    (conc : mstate → T6 → Int)
    (a : T6)
    (AREA_HDR : Int)
    (META_SIZE : Int)
    (kk : Int)
    (fst : T6 → Nat)
    (q : Nat)
    (a' : T6)
    (snd : T6 → Int)
    (h1 : (m_sizeclass (MR st g)) = 63)
    (h2 : 4096 ≤ ND)
    (h3 : (ND % 4096) = 0)
    (h4 : ND < (2 ^ (40 : Nat)))
    (h5 : 0 < NB)
    (h6 : (NB % 4096) = 0)
    (h7 : (NB + ND) ≤ alloc_ceiling)
    (h8 : (((UNIT + (UNIT * off)) + n) + IB) ≤ ND)
    (h9 : ND < ((((UNIT + (UNIT * off)) + n) + IB) + 4096))
    (h10 : (0 ≤ off ∧ off ≤ 255))
    (h11 : 0 ≤ n)
    (h12 : (ranges_free p0_reserved NB ND) = true)
    (h13 : (lr_lo r) = Bo)
    (h14 : Gc = ((conc st a) + (AREA_HDR + (META_SIZE * kk))))
    (h15 : (fst a) ≠ rid)
    (h16 : q ≠ (fst a))
    (h17 : (fst a') ≠ rid)
    (h18 : ((fst a') ≠ (fst a) ∨ ((fst a') = (fst a) ∧ (((snd a') + 4096) ≤ (snd a) ∨ ((snd a) + 4096) ≤ (snd a')))))
    (h19 : (snd a') ≠ (snd a))
    (h20 : (((conc st a') + 4096) ≤ Gc ∨ (Gc + 40) ≤ (conc st a'))) :
    ((NB + ND) - 4) = (NB + (ND - 4)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zk/RASla24.v (replace)
example (ml : Int) (W : Int) (h1 : W = (4096 * ml)) :
    (ml * (2 ^ (12 : Nat))) = (4096 * ml) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zl/A_PHhja.v (replace)
example
    {word list_mentry : Type}
    (sp : word)
    (a1 : word)
    (VEP : Int)
    (T : Int)
    (es : list_mentry)
    (lo : Int)
    (NV : Int)
    (NT : Int)
    (bv_unsigned : word → Int)
    (VM_STACK : Int)
    (alloc_ceiling : Int)
    (length : list_mentry → Nat)
    (h1 : (lo + VM_STACK) ≤ (bv_unsigned sp))
    (h2 : alloc_ceiling ≤ lo)
    (h3 : 0 < T)
    (h4 : 0 < (bv_unsigned a1))
    (h5 : (0 ≤ VEP ∧ (VEP + 248) ≤ alloc_ceiling))
    (h6 : (T + (16 * (((length es) : Nat) : Int))) ≤ alloc_ceiling)
    (h7 : ((VEP % 8) = 0 ∧ (248 ≤ NV ∧ (VEP + NV) ≤ alloc_ceiling)))
    (h8 : ((T % 8) = 0 ∧ ((16 * (((length es) : Nat) : Int)) ≤ NT ∧ (T + NT) ≤ alloc_ceiling)))
    (h9 : (0 ≤ T ∧ (T + (16 * (((length es) : Nat) : Int))) ≤ (2 ^ (64 : Nat)))) :
    (bv_unsigned sp) = (((bv_unsigned sp) - 80) + 80) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zl/A_WSruy.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (sh : Int → Int)
    (h_ff : T2 → Int)
    (H : T2)
    (wa : Int)
    (vep : Int)
    (h1 : (sh ((h_ff H) + 2976)) = ((sh (h_ff H)) + 372))
    (h2 : (sh ((h_ff H) + 3152)) = ((sh (h_ff H)) + 394))
    (h3 : wa ≠ vep)
    (h4 : (wa % 8) = 0)
    (h5 : ((wa + 24) % 8) = 0)
    (h6 : (((bv_unsigned sp) + (-64)) % 8) = 0) :
    8320 = ((bv_unsigned sp) - ((bv_unsigned sp) - 8320)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zn/Instr3v.v (replace)
example
    {T1 : Type}
    (a : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (h1 : (0 ≤ ((bv_unsigned sp) - 64) ∧ ((bv_unsigned sp) - 64) < (2 ^ (64 : Nat)))) :
    a = (((bv_unsigned sp) - 64) + (a - ((bv_unsigned sp) - 64))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AFre1om.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (p : Int)
    (bv_unsigned : T1 → Int)
    (kw : T1)
    (kb : Int)
    (a_sb : T2 → Int)
    (A : T2)
    (b : Int)
    (n0 : Int)
    (alloc_ceiling : Int)
    (length : T3 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T3 → Int)
    (r : T3)
    (ba_entries : T4 → T3)
    (b0 : T4)
    (ebytes : T3 → Int)
    (es : T3)
    (a_qglobal : T2 → T3)
    (kQuarantineMinSize : Int)
    (batch_addr : Int → T5 → Int)
    (b' : T5)
    (batch_bytes : T5 → Int)
    (h1 : (bv_unsigned kw) = (kb * 512))
    (h2 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h3 : (bv_unsigned kw) < (2 ^ (32 : Nat)))
    (h4 : (1 ≤ n0 ∧ n0 < (2 ^ (32 : Nat))))
    (h5 : (p + (8 * ((n0 + 7) / 8))) ≤ alloc_ceiling)
    (h6 : ((a_sb A) + (2 ^ (37 : Nat))) ≤ (2 ^ (47 : Nat)))
    (h7 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h8 : 0 ≤ (ebytes (ba_entries b0)))
    (h9 : 0 ≤ (ebytes es))
    (h10 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h11 : 0 ≤ (q_bytes (a_qglobal A)))
    (h12 : (((length (a_qglobal A)) : Nat) : Int) < (2 ^ (40 : Nat)))
    (h13 : (((length (a_qglobal A)) : Nat) : Int) ≠ 0)
    (h14 : (0 ≤ kQuarantineMinSize ∧ kQuarantineMinSize < (2 ^ (64 : Nat))))
    (h15 : (batch_addr (a_sb A) b') = b)
    (h16 : (batch_bytes b') = (n0 + 8192)) :
    (p + (-16)) = (p - 16) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AFre1om.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (p_thr : T1 → Int)
    (a_pl : T2 → T1)
    (A : T2)
    (bv_unsigned : T3 → Int)
    (kw : T3)
    (kb : Int)
    (a_sb : T2 → Int)
    (b : Int)
    (n0 : Int)
    (p : Int)
    (alloc_ceiling : Int)
    (length : T4 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T4 → Int)
    (r : T4)
    (ba_entries : T5 → T4)
    (b0 : T5)
    (ebytes : T4 → Int)
    (es : T4)
    (a_qglobal : T2 → T4)
    (kQuarantineMinSize : Int)
    (batch_addr : Int → T6 → Int)
    (b' : T6)
    (batch_bytes : T6 → Int)
    (h1 : (bv_unsigned kw) = (kb * 512))
    (h2 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h3 : (bv_unsigned kw) < (2 ^ (32 : Nat)))
    (h4 : (1 ≤ n0 ∧ n0 < (2 ^ (32 : Nat))))
    (h5 : (p + (8 * ((n0 + 7) / 8))) ≤ alloc_ceiling)
    (h6 : ((a_sb A) + (2 ^ (37 : Nat))) ≤ (2 ^ (47 : Nat)))
    (h7 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h8 : 0 ≤ (ebytes (ba_entries b0)))
    (h9 : 0 ≤ (ebytes es))
    (h10 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h11 : 0 ≤ (q_bytes (a_qglobal A)))
    (h12 : (((length (a_qglobal A)) : Nat) : Int) < (2 ^ (40 : Nat)))
    (h13 : (((length (a_qglobal A)) : Nat) : Int) ≠ 0)
    (h14 : (0 ≤ kQuarantineMinSize ∧ kQuarantineMinSize < (2 ^ (64 : Nat))))
    (h15 : (batch_addr (a_sb A) b') = b)
    (h16 : (batch_bytes b') = (n0 + 8192)) :
    ((((p_thr (a_pl A)) + 208) + 1920) + ((4 : Nat) : Int)) = (((p_thr (a_pl A)) + (208 + (80 * 24))) + 4) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AFre1om.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (p_thr : T1 → Int)
    (a_pl : T2 → T1)
    (A : T2)
    (bv_unsigned : T3 → Int)
    (kw : T3)
    (kb : Int)
    (a_sb : T2 → Int)
    (b : Int)
    (n0 : Int)
    (p : Int)
    (alloc_ceiling : Int)
    (length : T4 → Nat)
    (kQuarantineBatchBytes : Int)
    (q_bytes : T4 → Int)
    (r : T4)
    (ba_entries : T5 → T4)
    (b0 : T5)
    (ebytes : T4 → Int)
    (es : T4)
    (a_qglobal : T2 → T4)
    (kQuarantineMinSize : Int)
    (batch_addr : Int → T6 → Int)
    (b' : T6)
    (batch_bytes : T6 → Int)
    (h1 : (bv_unsigned kw) = (kb * 512))
    (h2 : (((a_sb A) + (24 * (2 ^ (32 : Nat)))) + (16 * (bv_unsigned kw))) = b)
    (h3 : (bv_unsigned kw) < (2 ^ (32 : Nat)))
    (h4 : (1 ≤ n0 ∧ n0 < (2 ^ (32 : Nat))))
    (h5 : (p + (8 * ((n0 + 7) / 8))) ≤ alloc_ceiling)
    (h6 : ((a_sb A) + (2 ^ (37 : Nat))) ≤ (2 ^ (47 : Nat)))
    (h7 : ((((length r) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes r))
    (h8 : 0 ≤ (ebytes (ba_entries b0)))
    (h9 : 0 ≤ (ebytes es))
    (h10 : ((((length (a_qglobal A)) : Nat) : Int) * kQuarantineBatchBytes) ≤ (q_bytes (a_qglobal A)))
    (h11 : 0 ≤ (q_bytes (a_qglobal A)))
    (h12 : (((length (a_qglobal A)) : Nat) : Int) < (2 ^ (40 : Nat)))
    (h13 : (((length (a_qglobal A)) : Nat) : Int) ≠ 0)
    (h14 : (0 ≤ kQuarantineMinSize ∧ kQuarantineMinSize < (2 ^ (64 : Nat))))
    (h15 : (batch_addr (a_sb A) b') = b)
    (h16 : (batch_bytes b') = (n0 + 8192)) :
    (((((p_thr (a_pl A)) + 208) + 1920) + ((4 : Nat) : Int)) + ((4 : Nat) : Int)) = (((p_thr (a_pl A)) + (208 + (80 * 24))) + 8) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AFreeB1.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (chunk_addr : T1 → T2 → T3 → Int)
    (a_sb : T4 → T1)
    (A : T4)
    (kQuarantineBatchClass : T2)
    (ba_idx : T5 → T3)
    (b : T5) :
    ((chunk_addr (a_sb A) kQuarantineBatchClass (ba_idx b)) + 0) = (chunk_addr (a_sb A) kQuarantineBatchClass (ba_idx b)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AFreeR2.v (replace)
example
    (bq : Int)
    (c : Int)
    (ma : Int)
    (size : Int)
    (sb : Int)
    (d : Int)
    (idx : Int)
    (p : Int)
    (mh : Int)
    (sh : Int → Int)
    (sq : Int)
    (dq : Int)
    (mfa : Int)
    (h1 : size = (16 * (size / 16)))
    (h2 : sb = (16 * (sb / 16)))
    (h3 : d = (16 * (d / 16)))
    (h4 : 0 ≤ (idx * size))
    (h5 : (sb ≤ p ∧ (p + size) ≤ (sb + (2 ^ (37 : Nat)))))
    (h6 : (d + 16) ≤ size)
    (h7 : (sh (mh + 16)) = ((((((2 * bq) + (c * 536870912)) + ((2 * idx) * sq)) + (2 * dq)) + 2) + 2147450880))
    (h8 : mfa = (8 * (mfa / 8)))
    (h9 : (sh (((sb + (c * 4294967296)) + 3758096384) + mfa)) = (((((2 * bq) + (c * 536870912)) + 469762048) + ma) + 2147450880)) :
    (((((2 * bq) + (c * 536870912)) + 469762048) + ma) * 8) = ((((16 * bq) + (c * 4294967296)) + 3758096384) + (8 * ma)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AFreeR2.v (replace)
example
    (nb8 : Int)
    (ma : Int)
    (size : Int)
    (sb : Int)
    (d : Int)
    (idx : Int)
    (p : Int)
    (mh : Int)
    (sh : Int → Int)
    (bq : Int)
    (c : Int)
    (sq : Int)
    (dq : Int)
    (mfa : Int)
    (nmv : Int)
    (h1 : size = (16 * (size / 16)))
    (h2 : sb = (16 * (sb / 16)))
    (h3 : d = (16 * (d / 16)))
    (h4 : 0 ≤ (idx * size))
    (h5 : (sb ≤ p ∧ (p + size) ≤ (sb + (2 ^ (37 : Nat)))))
    (h6 : (d + 16) ≤ size)
    (h7 : (sh (mh + 16)) = ((((((2 * bq) + (c * 536870912)) + ((2 * idx) * sq)) + (2 * dq)) + 2) + 2147450880))
    (h8 : mfa = (8 * (mfa / 8)))
    (h9 : nmv = (8 * (nmv / 8)))
    (h10 : (sh (((sb + (c * 4294967296)) + 3758096384) + mfa)) = (((((2 * bq) + (c * 536870912)) + 469762048) + ma) + 2147450880))
    (h11 : ((nmv - mfa) / 8) = (nb8 - ma)) :
    ((nb8 - ma) * 8) = ((8 * nb8) - (8 * ma)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AFreeR2.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    (((bv_unsigned sp) + (-80)) + 32) = (((bv_unsigned sp) - 80) + 32) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AIcp1qh.v (replace)
example (P : Int) (len : Int) (h1 : (0 ≤ P ∧ ((P + (len + 1)) + 8) ≤ 140737488355328)) :
    (P + len) = ((P + (len + 1)) - 1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AIcpkua.v (replace)
example
    (a : Int)
    (n : Int)
    (h1 : (0 ≤ a ∧ ((a + n) + 8) ≤ 140737488355328))
    (h2 : 0 ≤ (a / 8))
    (h3 : (-1) ≤ (((a + n) - 1) / 8))
    (h4 : (((a / 8) + 2147450880) % 8) ≤ (a / 8)) :
    ((a / 8) + (268431360 * 8)) = ((a / 8) + 2147450880) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AIcpzt2.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (str : list_byte)
    (slack : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (strchrnul_idx : Int → list_byte → Nat)
    (j : Int)
    (length : list_byte → Nat)
    (h1 : ((-(((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h2 : (0 ≤ lo ∧ lo ≤ ((bv_unsigned sp) - 16)))
    (h3 : 0 < ((bv_unsigned a1) % 256))
    (h4 : j = (((strchrnul_idx ((bv_unsigned a1) % 256) str) : Nat) : Int)) :
    ((bv_unsigned a0) + (((strchrnul_idx ((bv_unsigned a1) % 256) str) : Nat) : Int)) = ((((bv_unsigned a0) + j) - 1) + 1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AIcpzt2.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (str : list_byte)
    (slack : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (j : Int)
    (length : list_byte → Nat)
    (strchrnul_idx : Int → list_byte → Nat)
    (h1 : ((-(((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h2 : (0 ≤ lo ∧ lo ≤ ((bv_unsigned sp) - 16)))
    (h3 : 0 < ((bv_unsigned a1) % 256))
    (h4 : j = (((strchrnul_idx ((bv_unsigned a1) % 256) str) : Nat) : Int)) :
    (((bv_unsigned a0) + (j + 1)) - 1) = ((((bv_unsigned a0) + j) - 1) + 1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AIcpzt2.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (str : list_byte)
    (slack : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (strchrnul_idx : Int → list_byte → Nat)
    (length : list_byte → Nat)
    (j : Int)
    (b : word)
    (h1 : ((-(((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h2 : (0 ≤ lo ∧ lo ≤ ((bv_unsigned sp) - 16)))
    (h3 : 0 < ((bv_unsigned a1) % 256))
    (h4 : j = (((strchrnul_idx ((bv_unsigned a1) % 256) str) : Nat) : Int))
    (h5 : (bv_unsigned b) = 0) :
    ((bv_unsigned a0) + (((strchrnul_idx ((bv_unsigned a1) % 256) str) : Nat) : Int)) = ((((bv_unsigned a0) + (((strchrnul_idx ((bv_unsigned a1) % 256) str) : Nat) : Int)) - 1) + 1) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AInit0.v (replace)
example
    (a : Int)
    (n : Int)
    (off : Int)
    (i : Int)
    (h1 : 0 ≤ a)
    (h2 : (a + n) ≤ (2 ^ (64 : Nat)))
    (h3 : 0 ≤ off)
    (h4 : (off + 4) ≤ n) :
    (a + (off + i)) = ((a + off) + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AMal8cv.v (replace)
example
    {AState list_word T3 T4 : Type}
    (A : AState)
    (n : Int)
    (ks : list_word)
    (length : list_word → Nat)
    (ref_fetched : list_word → Int → list_word)
    (rg_free : T3 → list_word)
    (a_reg : AState → T4 → T3)
    (class_of : Int → T4)
    (refill_count : T4 → Int)
    (kMaxPrimaryUser : Int)
    (a_cache_inited : AState → Bool)
    (h1 : (1 ≤ n ∧ n ≤ kMaxPrimaryUser))
    (h2 : (a_cache_inited A) = true)
    (h3 : (refill_count (class_of n)) ≤ (((length (rg_free (a_reg A (class_of n)))) : Nat) : Int))
    (h4 : (length ks) = 16)
    (h5 : 1 ≤ (length (ref_fetched (rg_free (a_reg A (class_of n))) (refill_count (class_of n))))) :
    ((((length (ref_fetched (rg_free (a_reg A (class_of n))) (refill_count (class_of n)))) : Nat) : Int) - 1) = ((((length (ref_fetched (rg_free (a_reg A (class_of n))) (refill_count (class_of n)))) - 1) : Nat) : Int) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/APopG5.v (replace)
example
    {AState list_word T3 : Type}
    (A : AState)
    (c : Int)
    (ums : Int)
    (fam : Int)
    (nc : Int)
    (ksc : list_word)
    (a : Int)
    (i : Nat)
    (kUserMapSize : Int)
    (rg_mapped_user : T3 → Int)
    (a_reg : AState → Int → T3)
    (rg_allocated_user : T3 → Int)
    (class_size : Int → Int)
    (length : list_word → Nat)
    (a_paid : AState → Int → list_word)
    (class_slack : Int → Int)
    (kFreeArrayMapSize : Int)
    (rg_mapped_fa : T3 → Int)
    (kFreeArraySize : Int)
    (rg_free : T3 → list_word)
    (h1 : (1 ≤ c ∧ c ≤ 30))
    (h2 : (0 ≤ ums ∧ ((Int.fmod ums kUserMapSize) = 0 ∧ (((rg_mapped_user (a_reg A c)) + ums) < (((rg_allocated_user (a_reg A c)) + (9 * (class_size c))) + kUserMapSize) ∧ (rg_allocated_user (a_reg A c)) ≤ (((class_size c) * ((((length (a_paid A c)) : Nat) : Int) + 7)) + (class_slack c))))))
    (h3 : (0 ≤ fam ∧ ((Int.fmod fam kFreeArrayMapSize) = 0 ∧ (((rg_mapped_fa (a_reg A c)) + fam) ≤ ((4 * (Int.fdiv (rg_allocated_user (a_reg A c)) (class_size c))) + kFreeArrayMapSize) ∧ ((rg_mapped_fa (a_reg A c)) + fam) ≤ kFreeArraySize))))
    (h4 : (0 ≤ nc ∧ (((rg_allocated_user (a_reg A c)) + (nc * (class_size c))) ≤ ((rg_mapped_user (a_reg A c)) + ums) ∧ (4 * ((((length (rg_free (a_reg A c))) : Nat) : Int) + nc)) ≤ ((rg_mapped_fa (a_reg A c)) + fam))))
    (h5 : (((rg_mapped_user (a_reg A c)) + ums) = 0 → (fam = 0 ∧ nc = 0)))
    (h6 : (length ksc) = 16) :
    ((a + ((4 : Nat) : Int)) + (4 * ((i : Nat) : Int))) = (a + (4 * (((i + 1) : Nat) : Int))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/APopG5.v (replace)
example
    {AState list_word T3 T4 T5 : Type}
    (A : AState)
    (c : Int)
    (ums : Int)
    (fam : Int)
    (nc : Int)
    (ksc : list_word)
    (p_thr : T3 → Int)
    (a_pl : AState → T3)
    (c' : Int)
    (kUserMapSize : Int)
    (rg_mapped_user : T4 → Int)
    (a_reg : AState → Int → T4)
    (rg_allocated_user : T4 → Int)
    (class_size : Int → Int)
    (length : list_word → Nat)
    (a_paid : AState → Int → list_word)
    (class_slack : Int → Int)
    (kFreeArrayMapSize : Int)
    (rg_mapped_fa : T4 → Int)
    (kFreeArraySize : Int)
    (rg_free : T4 → list_word)
    (i : Nat)
    (pk_chunks : T5 → list_word)
    (a_cache : AState → Int → T5)
    (h1 : (1 ≤ c ∧ c ≤ 30))
    (h2 : (0 ≤ ums ∧ ((Int.fmod ums kUserMapSize) = 0 ∧ (((rg_mapped_user (a_reg A c)) + ums) < (((rg_allocated_user (a_reg A c)) + (9 * (class_size c))) + kUserMapSize) ∧ (rg_allocated_user (a_reg A c)) ≤ (((class_size c) * ((((length (a_paid A c)) : Nat) : Int) + 7)) + (class_slack c))))))
    (h3 : (0 ≤ fam ∧ ((Int.fmod fam kFreeArrayMapSize) = 0 ∧ (((rg_mapped_fa (a_reg A c)) + fam) ≤ ((4 * (Int.fdiv (rg_allocated_user (a_reg A c)) (class_size c))) + kFreeArrayMapSize) ∧ ((rg_mapped_fa (a_reg A c)) + fam) ≤ kFreeArraySize))))
    (h4 : (0 ≤ nc ∧ (((rg_allocated_user (a_reg A c)) + (nc * (class_size c))) ≤ ((rg_mapped_user (a_reg A c)) + ums) ∧ (4 * ((((length (rg_free (a_reg A c))) : Nat) : Int) + nc)) ≤ ((rg_mapped_fa (a_reg A c)) + fam))))
    (h5 : (((rg_mapped_user (a_reg A c)) + ums) = 0 → (fam = 0 ∧ nc = 0)))
    (h6 : (length ksc) = 16)
    (h7 : ((i : Nat) : Int) < (((length (pk_chunks (a_cache A c'))) : Nat) : Int)) :
    (((p_thr (a_pl A)) + 208) + (80 * c')) = ((p_thr (a_pl A)) + (208 + (80 * c'))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/APopG5.v (replace)
example
    {AState list_word T3 : Type}
    (A : AState)
    (c : Int)
    (ums : Int)
    (fam : Int)
    (nc : Int)
    (ksc : list_word)
    (rg_mapped_fa : T3 → Int)
    (a_reg : AState → Int → T3)
    (kUserMapSize : Int)
    (rg_mapped_user : T3 → Int)
    (rg_allocated_user : T3 → Int)
    (class_size : Int → Int)
    (length : list_word → Nat)
    (a_paid : AState → Int → list_word)
    (class_slack : Int → Int)
    (kFreeArrayMapSize : Int)
    (kFreeArraySize : Int)
    (rg_free : T3 → list_word)
    (h1 : (1 ≤ c ∧ c ≤ 30))
    (h2 : (0 ≤ ums ∧ ((Int.fmod ums kUserMapSize) = 0 ∧ (((rg_mapped_user (a_reg A c)) + ums) < (((rg_allocated_user (a_reg A c)) + (9 * (class_size c))) + kUserMapSize) ∧ (rg_allocated_user (a_reg A c)) ≤ (((class_size c) * ((((length (a_paid A c)) : Nat) : Int) + 7)) + (class_slack c))))))
    (h3 : (0 ≤ fam ∧ ((Int.fmod fam kFreeArrayMapSize) = 0 ∧ (((rg_mapped_fa (a_reg A c)) + fam) ≤ ((4 * (Int.fdiv (rg_allocated_user (a_reg A c)) (class_size c))) + kFreeArrayMapSize) ∧ ((rg_mapped_fa (a_reg A c)) + fam) ≤ kFreeArraySize))))
    (h4 : (0 ≤ nc ∧ (((rg_allocated_user (a_reg A c)) + (nc * (class_size c))) ≤ ((rg_mapped_user (a_reg A c)) + ums) ∧ (4 * ((((length (rg_free (a_reg A c))) : Nat) : Int) + nc)) ≤ ((rg_mapped_fa (a_reg A c)) + fam))))
    (h5 : (((rg_mapped_user (a_reg A c)) + ums) = 0 → (fam = 0 ∧ nc = 0)))
    (h6 : (length ksc) = 16)
    (h7 : ((rg_mapped_fa (a_reg A c)) % 8) = 0)
    (h8 : (fam % 8) = 0)
    (h9 : (((rg_mapped_fa (a_reg A c)) + fam) / 8) = (((rg_mapped_fa (a_reg A c)) / 8) + (fam / 8))) :
    ((((rg_mapped_fa (a_reg A c)) / 8) + (fam / 8)) * 8) = ((8 * ((rg_mapped_fa (a_reg A c)) / 8)) + (8 * (fam / 8))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/APopG5.v (replace)
example
    {AState list_word T3 T4 : Type}
    (A : AState)
    (c : Int)
    (ums : Int)
    (fam : Int)
    (nc : Int)
    (ksc : list_word)
    (rg_allocated_user : T3 → Int)
    (a_reg : AState → Int → T3)
    (class_size : Int → Int)
    (kUserMapSize : Int)
    (rg_mapped_user : T3 → Int)
    (length : list_word → Nat)
    (a_paid : AState → Int → list_word)
    (class_slack : Int → Int)
    (kFreeArrayMapSize : Int)
    (rg_mapped_fa : T3 → Int)
    (kFreeArraySize : Int)
    (rg_free : T3 → list_word)
    (region_beg : T4 → Int → Int)
    (a_sb : AState → T4)
    (k : Int)
    (sh : Int → Int)
    (h1 : (1 ≤ c ∧ c ≤ 30))
    (h2 : (0 ≤ ums ∧ ((Int.fmod ums kUserMapSize) = 0 ∧ (((rg_mapped_user (a_reg A c)) + ums) < (((rg_allocated_user (a_reg A c)) + (9 * (class_size c))) + kUserMapSize) ∧ (rg_allocated_user (a_reg A c)) ≤ (((class_size c) * ((((length (a_paid A c)) : Nat) : Int) + 7)) + (class_slack c))))))
    (h3 : (0 ≤ fam ∧ ((Int.fmod fam kFreeArrayMapSize) = 0 ∧ (((rg_mapped_fa (a_reg A c)) + fam) ≤ ((4 * (Int.fdiv (rg_allocated_user (a_reg A c)) (class_size c))) + kFreeArrayMapSize) ∧ ((rg_mapped_fa (a_reg A c)) + fam) ≤ kFreeArraySize))))
    (h4 : (0 ≤ nc ∧ (((rg_allocated_user (a_reg A c)) + (nc * (class_size c))) ≤ ((rg_mapped_user (a_reg A c)) + ums) ∧ (4 * ((((length (rg_free (a_reg A c))) : Nat) : Int) + nc)) ≤ ((rg_mapped_fa (a_reg A c)) + fam))))
    (h5 : (((rg_mapped_user (a_reg A c)) + ums) = 0 → (fam = 0 ∧ nc = 0)))
    (h6 : (length ksc) = 16)
    (h7 : ((rg_allocated_user (a_reg A c)) % 8) = 0)
    (h8 : ((rg_mapped_user (a_reg A c)) % 8) = 0)
    (h9 : (ums % 8) = 0)
    (h10 : ((class_size c) % 8) = 0)
    (h11 : ((region_beg (a_sb A) c) % 8) = 0)
    (h12 : ((k * (class_size c)) % 8) = 0)
    (h13 : (sh ((region_beg (a_sb A) c) + (k * (class_size c)))) = ((sh ((region_beg (a_sb A) c) + (rg_allocated_user (a_reg A c)))) + (((k * (class_size c)) - (rg_allocated_user (a_reg A c))) / 8)))
    (h14 : (rg_allocated_user (a_reg A c)) ≤ (k * (class_size c)))
    (h15 : ((k * (class_size c)) + (class_size c)) ≤ ((rg_allocated_user (a_reg A c)) + (nc * (class_size c)))) :
    (((Int.fdiv (rg_allocated_user (a_reg A c)) (class_size c)) + nc) * (class_size c)) = (((Int.fdiv (rg_allocated_user (a_reg A c)) (class_size c)) * (class_size c)) + (nc * (class_size c))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/APopG5.v (replace)
example
    {AState list_word T3 T4 : Type}
    (A : AState)
    (c : Int)
    (ums : Int)
    (fam : Int)
    (nc : Int)
    (ksc : list_word)
    (k : Int)
    (class_size : Int → Int)
    (kUserMapSize : Int)
    (rg_mapped_user : T3 → Int)
    (a_reg : AState → Int → T3)
    (rg_allocated_user : T3 → Int)
    (length : list_word → Nat)
    (a_paid : AState → Int → list_word)
    (class_slack : Int → Int)
    (kFreeArrayMapSize : Int)
    (rg_mapped_fa : T3 → Int)
    (kFreeArraySize : Int)
    (rg_free : T3 → list_word)
    (region_beg : T4 → Int → Int)
    (a_sb : AState → T4)
    (sh : Int → Int)
    (h1 : (1 ≤ c ∧ c ≤ 30))
    (h2 : (0 ≤ ums ∧ ((Int.fmod ums kUserMapSize) = 0 ∧ (((rg_mapped_user (a_reg A c)) + ums) < (((rg_allocated_user (a_reg A c)) + (9 * (class_size c))) + kUserMapSize) ∧ (rg_allocated_user (a_reg A c)) ≤ (((class_size c) * ((((length (a_paid A c)) : Nat) : Int) + 7)) + (class_slack c))))))
    (h3 : (0 ≤ fam ∧ ((Int.fmod fam kFreeArrayMapSize) = 0 ∧ (((rg_mapped_fa (a_reg A c)) + fam) ≤ ((4 * (Int.fdiv (rg_allocated_user (a_reg A c)) (class_size c))) + kFreeArrayMapSize) ∧ ((rg_mapped_fa (a_reg A c)) + fam) ≤ kFreeArraySize))))
    (h4 : (0 ≤ nc ∧ (((rg_allocated_user (a_reg A c)) + (nc * (class_size c))) ≤ ((rg_mapped_user (a_reg A c)) + ums) ∧ (4 * ((((length (rg_free (a_reg A c))) : Nat) : Int) + nc)) ≤ ((rg_mapped_fa (a_reg A c)) + fam))))
    (h5 : (((rg_mapped_user (a_reg A c)) + ums) = 0 → (fam = 0 ∧ nc = 0)))
    (h6 : (length ksc) = 16)
    (h7 : ((rg_allocated_user (a_reg A c)) % 8) = 0)
    (h8 : ((rg_mapped_user (a_reg A c)) % 8) = 0)
    (h9 : (ums % 8) = 0)
    (h10 : ((class_size c) % 8) = 0)
    (h11 : ((region_beg (a_sb A) c) % 8) = 0)
    (h12 : ((k * (class_size c)) % 8) = 0)
    (h13 : (sh ((region_beg (a_sb A) c) + (k * (class_size c)))) = ((sh ((region_beg (a_sb A) c) + (rg_allocated_user (a_reg A c)))) + (((k * (class_size c)) - (rg_allocated_user (a_reg A c))) / 8)))
    (h14 : (rg_allocated_user (a_reg A c)) ≤ (k * (class_size c)))
    (h15 : ((k * (class_size c)) + (class_size c)) ≤ ((rg_allocated_user (a_reg A c)) + (nc * (class_size c)))) :
    ((k + 1) * (class_size c)) = ((k * (class_size c)) + (class_size c)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/APopG5.v (replace)
example
    {AState list_word T3 T4 : Type}
    (A : AState)
    (c : Int)
    (ums : Int)
    (fam : Int)
    (nc : Int)
    (ksc : list_word)
    (rg_allocated_user : T3 → Int)
    (a_reg : AState → Int → T3)
    (class_size : Int → Int)
    (kUserMapSize : Int)
    (rg_mapped_user : T3 → Int)
    (length : list_word → Nat)
    (a_paid : AState → Int → list_word)
    (class_slack : Int → Int)
    (kFreeArrayMapSize : Int)
    (rg_mapped_fa : T3 → Int)
    (kFreeArraySize : Int)
    (rg_free : T3 → list_word)
    (region_beg : T4 → Int → Int)
    (a_sb : AState → T4)
    (k : Int)
    (sh : Int → Int)
    (h1 : (1 ≤ c ∧ c ≤ 30))
    (h2 : (0 ≤ ums ∧ ((Int.fmod ums kUserMapSize) = 0 ∧ (((rg_mapped_user (a_reg A c)) + ums) < (((rg_allocated_user (a_reg A c)) + (9 * (class_size c))) + kUserMapSize) ∧ (rg_allocated_user (a_reg A c)) ≤ (((class_size c) * ((((length (a_paid A c)) : Nat) : Int) + 7)) + (class_slack c))))))
    (h3 : (0 ≤ fam ∧ ((Int.fmod fam kFreeArrayMapSize) = 0 ∧ (((rg_mapped_fa (a_reg A c)) + fam) ≤ ((4 * (Int.fdiv (rg_allocated_user (a_reg A c)) (class_size c))) + kFreeArrayMapSize) ∧ ((rg_mapped_fa (a_reg A c)) + fam) ≤ kFreeArraySize))))
    (h4 : (0 ≤ nc ∧ (((rg_allocated_user (a_reg A c)) + (nc * (class_size c))) ≤ ((rg_mapped_user (a_reg A c)) + ums) ∧ (4 * ((((length (rg_free (a_reg A c))) : Nat) : Int) + nc)) ≤ ((rg_mapped_fa (a_reg A c)) + fam))))
    (h5 : (((rg_mapped_user (a_reg A c)) + ums) = 0 → (fam = 0 ∧ nc = 0)))
    (h6 : (length ksc) = 16)
    (h7 : ((rg_allocated_user (a_reg A c)) % 8) = 0)
    (h8 : ((rg_mapped_user (a_reg A c)) % 8) = 0)
    (h9 : (ums % 8) = 0)
    (h10 : ((class_size c) % 8) = 0)
    (h11 : ((region_beg (a_sb A) c) % 8) = 0)
    (h12 : ((k * (class_size c)) % 8) = 0)
    (h13 : (sh ((region_beg (a_sb A) c) + (k * (class_size c)))) = ((sh ((region_beg (a_sb A) c) + (rg_allocated_user (a_reg A c)))) + (((k * (class_size c)) - (rg_allocated_user (a_reg A c))) / 8)))
    (h14 : (rg_allocated_user (a_reg A c)) ≤ (k * (class_size c)))
    (h15 : ((k * (class_size c)) + (class_size c)) ≤ ((rg_allocated_user (a_reg A c)) + (nc * (class_size c))))
    (h16 : ((nc * (class_size c)) % 8) = 0)
    (h17 : (((rg_allocated_user (a_reg A c)) + (nc * (class_size c))) % 8) = 0)
    (h18 : (((rg_allocated_user (a_reg A c)) + (nc * (class_size c))) / 8) = (((rg_allocated_user (a_reg A c)) / 8) + ((nc * (class_size c)) / 8))) :
    ((((rg_allocated_user (a_reg A c)) / 8) + ((nc * (class_size c)) / 8)) * 8) = ((8 * ((rg_allocated_user (a_reg A c)) / 8)) + (8 * ((nc * (class_size c)) / 8))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/APopP.v (replace)
example {T1 T2 : Type} (p_thr : T1 → Int) (a_pl : T2 → T1) (A : T2) (i : Int) :
    (((p_thr (a_pl A)) + (208 + (80 * i))) + 4) = ((((p_thr (a_pl A)) + 208) + (80 * i)) + 4) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/APopP.v (replace)
example
    {AState T2 T3 T4 T5 : Type}
    (A : AState)
    (n : Int)
    (a : Int)
    (k : Int)
    (p_thr : T2 → Int)
    (a_pl : AState → T2)
    (i : Int)
    (kMaxPrimaryUser : Int)
    (length : T3 → Nat)
    (rg_free : T4 → T3)
    (a_reg : AState → T5 → T4)
    (class_of : Int → T5)
    (refill_count : T5 → Int)
    (h1 : (1 ≤ n ∧ n ≤ kMaxPrimaryUser))
    (h2 : (((length (rg_free (a_reg A (class_of n)))) : Nat) : Int) < (refill_count (class_of n)))
    (h3 : (p_thr (a_pl A)) ≤ a)
    (h4 : (a + k) ≤ ((p_thr (a_pl A)) + 4096)) :
    ((p_thr (a_pl A)) + ((a - (p_thr (a_pl A))) + i)) = (a + i) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/ARt34mx.v (replace)
example
    {list_word : Type}
    (dst : Int)
    (au : Int)
    (size : Int)
    (nc : Int)
    (junk : list_word)
    (i : Int)
    (length : list_word → Nat)
    (kHighMemBeg : Int)
    (alloc_ceiling : Int)
    (h1 : (length junk) = (Int.toNat nc))
    (h2 : (1 ≤ nc ∧ nc < (2 ^ (27 : Nat))))
    (h3 : (1 ≤ size ∧ size ≤ 65536))
    (h4 : 0 ≤ au)
    (h5 : (au + (nc * size)) < (2 ^ (40 : Nat)))
    (h6 : kHighMemBeg ≤ dst)
    (h7 : (dst + (4 * nc)) ≤ alloc_ceiling)
    (h8 : (0 ≤ i ∧ i < nc)) :
    (Int.toNat ((nc - 1) - i)) = (Int.toNat (nc - (i + 1))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/ASecTop.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (q : Int)
    (ru : Int)
    (dc : Int)
    (kMaxPrimaryUser : Int)
    (n : Int)
    (bv_unsigned : T1 → Int)
    (wz : Int → T1)
    (map_size : Int → Int)
    (sr_reserved : T2 → Int)
    (a_sec : T3 → T2)
    (A : T3)
    (kChunksBlockCount : Int)
    (pahi : Int)
    (p_pa : T4 → Int)
    (a_pl : T3 → T4)
    (nch : Int)
    (mbw : T1)
    (sh : Int → Int)
    (z : Int)
    (pa_tsd : Int)
    (cl_tp : T5 → T1)
    (LPA : T5)
    (p_thr : T4 → Int)
    (alloc_ceiling : Int)
    (kPtrArrayReserve : Int)
    (lo : Int)
    (kHighMemBeg : Int)
    (spa : T1)
    (stkobj : Int)
    (hi : Int)
    (round_up : T6 → Int → Int)
    (needed_size2 : Int → T6)
    (d : Int)
    (e : Int)
    (h1 : (kMaxPrimaryUser < n ∧ n < ((2 ^ (30 : Nat)) + 1)))
    (h2 : (bv_unsigned (wz (map_size n))) = (map_size n))
    (h3 : (sr_reserved (a_sec A)) = kChunksBlockCount)
    (h4 : (pahi = (((p_pa (a_pl A)) + (8 * nch)) + 8) ∨ (nch = 0 ∧ pahi = ((p_pa (a_pl A)) + (8 * kChunksBlockCount)))))
    (h5 : (0 ≤ z ∧ z < (2 ^ (64 : Nat))))
    (h6 : (6191912 ≤ pa_tsd ∧ (pa_tsd + 8) ≤ 6332416))
    (h7 : (bv_unsigned (cl_tp LPA)) = 6192088)
    (h8 : ((64512 < n ∧ n < ((2 ^ (30 : Nat)) + 1)) ∧ (4096 ≤ (p_thr (a_pl A)) ∧ (((p_thr (a_pl A)) + 4096) ≤ alloc_ceiling ∧ (4096 ≤ (bv_unsigned mbw) ∧ (((bv_unsigned mbw) + (map_size n)) ≤ alloc_ceiling ∧ ((n + 4096) ≤ (map_size n) ∧ ((map_size n) < (2 ^ (31 : Nat)) ∧ (4096 ≤ (p_pa (a_pl A)) ∧ (((p_pa (a_pl A)) + kPtrArrayReserve) ≤ alloc_ceiling ∧ ((0 ≤ nch ∧ nch < kChunksBlockCount) ∧ (alloc_ceiling ≤ lo ∧ ((140735332483072 ≤ alloc_ceiling ∧ alloc_ceiling ≤ 140737479966720) ∧ ((2147450880 + 512) ≤ (sh (bv_unsigned mbw)) ∧ (((sh (bv_unsigned mbw)) + ((map_size n) / 8)) ≤ kHighMemBeg ∧ (lo ≤ ((bv_unsigned spa) - 4096) ∧ ((bv_unsigned spa) ≤ stkobj ∧ ((stkobj + 2064) ≤ hi ∧ hi ≤ (2 ^ (47 : Nat))))))))))))))))))))
    (h9 : (map_size n) = ((round_up (needed_size2 n) 4096) + 4096))
    (h10 : dc = (d + (min e 1)))
    (h11 : ((bv_unsigned mbw) + 4096) = (8 * q))
    (h12 : (round_up (needed_size2 n) 4096) = (8 * ru))
    (h13 : (q + 2147450880) = ((((bv_unsigned mbw) / 8) + 2147450880) + 512))
    (h14 : ((256 + dc) ≤ ru ∧ ((q + ru) + 2147450880) = ((((bv_unsigned mbw) / 8) + 2147450880) + ((map_size n) / 8))))
    (h15 : ((bv_unsigned mbw) + (map_size n)) ≤ (2 ^ (64 : Nat)))
    (h16 : 6332416 ≤ (bv_unsigned mbw))
    (h17 : 6332416 ≤ (((bv_unsigned mbw) / 8) + 2147450880)) :
    ((q + ru) + 2147450880) = ((((q + 256) + dc) + 2147450880) + ((ru - 256) - dc)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/ASecten.v (replace)
example
    {word list_list_Z : Type}
    (sp : word)
    (lo : Int)
    (n : Int)
    (stkobj : Int)
    (sb : Int)
    (AB : Int)
    (q : Int)
    (d : Int)
    (e : Int)
    (dc : Int)
    (ru : Int)
    (n0 : Int)
    (f0 : Int)
    (D : list_list_Z)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (kHighMemBeg : Int)
    (round_up : Int → Int → Int)
    (needed_size2 : Int → Int)
    (length : list_list_Z → Nat)
    (kDepotNodesBlock : Int)
    (kStackStoreBlockBytes : Int)
    (h1 : (alloc_ceiling ≤ lo ∧ lo ≤ ((bv_unsigned sp) - 1024)))
    (h2 : ((bv_unsigned sp) % 16) = 0)
    (h3 : ((bv_unsigned sp) + 65536) < (2 ^ (64 : Nat)))
    (h4 : (64513 ≤ n ∧ n < (2 ^ (31 : Nat))))
    (h5 : n = ((8 * d) + e))
    (h6 : (0 ≤ e ∧ e < 8))
    (h7 : ((bv_unsigned sp) ≤ stkobj ∧ (stkobj + 2064) ≤ (2 ^ (47 : Nat))))
    (h8 : (kHighMemBeg ≤ sb ∧ (sb + (2 ^ (37 : Nat))) ≤ alloc_ceiling))
    (h9 : AB = (8 * q))
    (h10 : (AB % 4096) = 0)
    (h11 : ((AB + (8 * ru)) ≤ sb ∨ (sb + (2 ^ (37 : Nat))) ≤ AB))
    (h12 : (round_up (needed_size2 n) 4096) = (8 * ru))
    (h13 : ((((length D) : Nat) : Int) + 1) < 65535)
    (h14 : ((n0 + kDepotNodesBlock) ≤ (AB - 4096) ∨ (AB + (8 * ru)) ≤ n0))
    (h15 : ((f0 + kStackStoreBlockBytes) ≤ (AB - 4096) ∨ (AB + (8 * ru)) ≤ f0))
    (h16 : (d ≤ dc ∧ dc ≤ (d + 1)))
    (h17 : 0 ≤ lo) :
    2048 = ((AB + 2048) - AB) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/ASecten.v (replace)
example
    {word list_list_Z : Type}
    (sp : word)
    (lo : Int)
    (n : Int)
    (stkobj : Int)
    (sb : Int)
    (AB : Int)
    (q : Int)
    (d : Int)
    (e : Int)
    (dc : Int)
    (ru : Int)
    (n0 : Int)
    (f0 : Int)
    (D : list_list_Z)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (kHighMemBeg : Int)
    (round_up : Int → Int → Int)
    (needed_size2 : Int → Int)
    (length : list_list_Z → Nat)
    (kDepotNodesBlock : Int)
    (kStackStoreBlockBytes : Int)
    (h1 : (alloc_ceiling ≤ lo ∧ lo ≤ ((bv_unsigned sp) - 1024)))
    (h2 : ((bv_unsigned sp) % 16) = 0)
    (h3 : ((bv_unsigned sp) + 65536) < (2 ^ (64 : Nat)))
    (h4 : (64513 ≤ n ∧ n < (2 ^ (31 : Nat))))
    (h5 : n = ((8 * d) + e))
    (h6 : (0 ≤ e ∧ e < 8))
    (h7 : ((bv_unsigned sp) ≤ stkobj ∧ (stkobj + 2064) ≤ (2 ^ (47 : Nat))))
    (h8 : (kHighMemBeg ≤ sb ∧ (sb + (2 ^ (37 : Nat))) ≤ alloc_ceiling))
    (h9 : AB = (8 * q))
    (h10 : (AB % 4096) = 0)
    (h11 : ((AB + (8 * ru)) ≤ sb ∨ (sb + (2 ^ (37 : Nat))) ≤ AB))
    (h12 : (round_up (needed_size2 n) 4096) = (8 * ru))
    (h13 : ((((length D) : Nat) : Int) + 1) < 65535)
    (h14 : ((n0 + kDepotNodesBlock) ≤ (AB - 4096) ∨ (AB + (8 * ru)) ≤ n0))
    (h15 : ((f0 + kStackStoreBlockBytes) ≤ (AB - 4096) ∨ (AB + (8 * ru)) ≤ f0))
    (h16 : (d ≤ dc ∧ dc ≤ (d + 1)))
    (h17 : 0 ≤ lo) :
    (8 * ((ru - 256) - dc)) = ((AB - ((AB + 2048) + (8 * dc))) + (8 * ru)) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AWrapKit.v (assert)
example (fp : Int) (ASTK : Int) (a : Int) :
    (((fp - ASTK) ≤ a ∧ a < fp) ∨ (¬ ((fp - ASTK) ≤ a ∧ a < fp))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AWrapKit.v (assert)
example (wlo : Int) (a : Int) (whi : Int) :
    ((wlo ≤ a ∧ a < whi) ∨ (¬ (wlo ≤ a ∧ a < whi))) := by
  lia

-- varnish/esi_parse_fuzzer: lib/Zq/AWrapR.v (replace)
example
    {T1 T2 T3 : Type}
    (r : Int)
    (a : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (ra : T1)
    (s0 : T1)
    (cl_tp : T2 → T1)
    (LPA : T2)
    (p : Int)
    (thr : Int)
    (old : Int)
    (n : Int)
    (length : T3 → Nat)
    (src : T3)
    (h1 : (alloc_ceiling ≤ ((bv_unsigned sp) - 8192) ∧ ((bv_unsigned sp) - 8192) ≤ ((bv_unsigned sp) - 2192)))
    (h2 : 4096 ≤ (bv_unsigned ra))
    (h3 : (bv_unsigned ra) ≠ 364488)
    (h4 : (bv_unsigned s0) ≤ (bv_unsigned sp))
    (h5 : (bv_unsigned (cl_tp LPA)) = 6192088)
    (h6 : 16 ≤ p)
    (h7 : (¬ (thr ≤ a ∧ a < (thr + 4096))))
    (h8 : p ≠ r)
    (h9 : (0 < r ∧ r < (2 ^ (64 : Nat))))
    (h10 : ((p + old) ≤ r ∨ (r + n) ≤ (p + (-16))))
    (h11 : ((0 ≤ (min n old) ∧ (min n old) ≤ old) ∧ (min n old) ≤ n))
    (h12 : (length src) = (Int.toNat (min n old))) :
    (r + (a - r)) = a := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AF_depot7.v (replace)
example
    (B0 : Int)
    (b : Int)
    (fr : Int)
    (kStoreBlockFrames : Int)
    (stored_of : Int → Int → Int)
    (B1 : Int)
    (h1 : 0 ≤ b)
    (h2 : fr = ((b * kStoreBlockFrames) + (Int.fmod fr kStoreBlockFrames)))
    (h3 : (stored_of fr b) = (Int.fmod fr kStoreBlockFrames))
    (h4 : (stored_of fr (b + 1)) = 0)
    (h5 : B0 = (1571416 + (16 * b)))
    (h6 : B1 = (B0 + 16)) :
    B0 = ((1571400 + 16) + (b * 16)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AF_dputT.v (replace)
example
    {aenv word aps list_word T5 T6 : Type}
    (E0 : aenv)
    (sp : word)
    (s : aps)
    (lo : Int)
    (A : Int)
    (len : Int)
    (ws : list_word)
    (aX : T5)
    (k : Nat)
    (length : T6 → Nat)
    (as_sec : T5 → T6)
    (zlen : list_word → Int)
    (ae_keys0 : aenv → list_word)
    (ae_frames0 : aenv → Int)
    (as_node_blocks : T5 → list_word)
    (aps_alloc : aps → T5)
    (as_store_blocks : T5 → list_word)
    (AsanState_sec_bytes : T5 → Int)
    (as_ndepot_ins : T5 → Int)
    (kInitialCredit : Int)
    (alloc_ceiling : Int)
    (bv_unsigned : word → Int)
    (K_DEPOT : Int)
    (h1 : ((zlen (ae_keys0 E0)) ≤ 1000 ∧ (0 ≤ (ae_frames0 E0) ∧ (ae_frames0 E0) ≤ 4096)))
    (h2 : (zlen (as_node_blocks (aps_alloc s))) ≤ 1832)
    (h3 : (zlen (as_store_blocks (aps_alloc s))) ≤ 7400)
    (h4 : (AsanState_sec_bytes (aps_alloc s)) ≤ (2 ^ (39 : Nat)))
    (h5 : ((as_ndepot_ins (aps_alloc s)) + 1) ≤ kInitialCredit)
    (h6 : alloc_ceiling ≤ lo)
    (h7 : lo ≤ ((bv_unsigned sp) - K_DEPOT))
    (h8 : ((bv_unsigned sp) % 16) = 0)
    (h9 : (bv_unsigned sp) ≤ A)
    (h10 : (A + (8 * (zlen ws))) < (2 ^ (47 : Nat)))
    (h11 : (1 ≤ len ∧ len ≤ (zlen ws)))
    (h12 : (zlen ws) ≤ 30) :
    k = (((length (as_sec aX)) + k) - (length (as_sec aX))) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AF_free4.v (replace)
example
    {T1 T2 : Type}
    (blen : T1 → Int)
    (rr0 : T1)
    (pp : T1)
    (b : T2)
    (L : T1)
    (qbytes : T1 → Int)
    (b_size : T2 → Int)
    (h1 : (((blen pp) + (blen rr0)) + 1) < (2 ^ (40 : Nat)))
    (h2 : (0 ≤ (qbytes pp) ∧ (0 ≤ (qbytes rr0) ∧ (((qbytes pp) + (b_size b)) + (qbytes rr0)) = (qbytes L)))) :
    (blen rr0) = (((blen rr0) + 1) + (-1)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AF_free4.v (replace)
example
    {T1 T2 : Type}
    (qbytes : T1 → Int)
    (rr0 : T1)
    (bsz : Int)
    (pp : T1)
    (b : T2)
    (L : T1)
    (blen : T1 → Int)
    (b_size : T2 → Int)
    (h1 : (((blen pp) + (blen rr0)) + 1) < (2 ^ (40 : Nat)))
    (h2 : (0 ≤ (qbytes pp) ∧ (0 ≤ (qbytes rr0) ∧ (((qbytes pp) + (b_size b)) + (qbytes rr0)) = (qbytes L)))) :
    (qbytes rr0) = ((bsz + (qbytes rr0)) - bsz) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AF_realloc1.v (replace)
example (k : Int) (h1 : (0 ≤ k ∧ k < (2 ^ (15 : Nat)))) :
    ((716160 + (k * 8)) + 8) = ((716160 + 8) + (8 * k)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AI_read_icp.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (tp : word)
    (B : Int)
    (count : Int)
    (SB : Int)
    (ws : list_byte)
    (lo : Int)
    (bs : list_byte)
    (ws' : list_byte)
    (shw_hi : Int → Int → Int → Int)
    (length : list_byte → Nat)
    (shw_lo : Int → Int → Int)
    (rc_sp : Int)
    (bv_unsigned : word → Int)
    (errno_addr : word → Int)
    (h1 : ((max 140735340871680 (min 140737488355328 rc_sp)) - 8388608) ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 2208))
    (h3 : (0 < count ∧ count ≤ 65536))
    (h4 : (B + count) < (2 ^ (47 : Nat)))
    (h5 : (1310160 ≤ (errno_addr tp) ∧ ((errno_addr tp) + 4) ≤ 6303744))
    (h6 : ((B + count) ≤ lo ∨ (bv_unsigned sp) ≤ B))
    (h7 : ((B + count) ≤ (errno_addr tp) ∨ ((errno_addr tp) + 4) ≤ B))
    (h8 : ((B + count) ≤ 671744 ∨ 1310160 ≤ B))
    (h9 : (((length ws) : Nat) : Int) = ((shw_hi SB B count) - (shw_lo SB B)))
    (h10 : ((shw_hi SB B count) ≤ B ∨ (B + count) ≤ (shw_lo SB B)))
    (h11 : ((2 ^ (24 : Nat)) ≤ SB ∧ SB < (2 ^ (32 : Nat))))
    (h12 : (1 ≤ (((length bs) : Nat) : Int) ∧ (((length bs) : Nat) : Int) ≤ count))
    (h13 : (((length ws') : Nat) : Int) = ((shw_hi SB B (((length bs) : Nat) : Int)) - (shw_lo SB B)))
    (h14 : (shw_hi SB B (((length bs) : Nat) : Int)) ≤ (shw_hi SB B count)) :
    ((shw_hi SB B (((length bs) : Nat) : Int)) - 8) = ((shw_lo SB B) + (((shw_hi SB B (((length bs) : Nat) : Int)) - 8) - (shw_lo SB B))) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AI_strnlen_icp.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (A : Int)
    (cnt : Int)
    (SB : Int)
    (str : list_byte)
    (slack : list_byte)
    (ws : list_byte)
    (lo : Int)
    (length : list_byte → Nat)
    (rc_sp : Int)
    (bv_unsigned : word → Int)
    (shw_hi : Int → Int → Int → Int)
    (shw_lo : Int → Int → Int)
    (h1 : ((max 140735340871680 (min 140737488355328 rc_sp)) - 8388608) ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 4384))
    (h3 : (((((length str) : Nat) : Int) + 1) ≤ cnt ∧ cnt < (2 ^ (63 : Nat))))
    (h4 : ((-((A + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h5 : ((((length str) : Nat) : Int) + 1) < (2 ^ (40 : Nat)))
    (h6 : ((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) < (2 ^ (47 : Nat)))
    (h7 : (((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ A))
    (h8 : (((length ws) : Nat) : Int) = ((shw_hi SB A ((((length str) : Nat) : Int) + 1)) - (shw_lo SB A)))
    (h9 : ((2 ^ (24 : Nat)) ≤ SB ∧ SB < (2 ^ (32 : Nat)))) :
    (A + ((((length str) : Nat) : Int) + 1)) = (A + ((((length str) : Nat) : Int) + 1)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AP_printf_core_scan.v (replace)
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
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < 140737488355328)
    (h4 : (A + (zlength fmt)) ≤ 135168)
    (h5 : ((691736 ≤ Fp ∧ (Fp + 232) ≤ 693280) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6294360 ≤ B ∧ (B + BS) ≤ 6303744) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 65536 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (znth fmt i) ≠ 0) :
    n = (((A + i) + n) - (A + i)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AY_lex_kit.v (replace)
example (a : Int) :
    (2147450880 + (a / 8)) = ((a / 8) + 2147450880) := by
  lia

-- yajl-ruby/json_fuzzer: lib/A/AY_parse_lex.v (replace)
example (H : Int) :
    (2147450880 + ((H + 16) / 8)) = (((H + 16) / 8) + 2147450880) := by
  lia

-- yajl-ruby/json_fuzzer: lib/AS5/A_Hooks5.v (replace)
example
    (x : Int)
    (m : Int)
    (k : Int)
    (h1 : 0 < m)
    (h2 : x ≤ (k * m))
    (h3 : (Int.fdiv (-(k * m)) m) ≤ (Int.fdiv (-x) m)) :
    ((-k) * m) = (-(k * m)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/Agent/MallocFacts_R.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (get_stride : T1 → Int)
    (MR : T2 → T3 → T1)
    (st : T2)
    (m : T3)
    (IB : Int)
    (UNIT : Int)
    (off : Int)
    (blk_size : T4 → Int)
    (blk : T4)
    (sstart : T1 → Int → Int)
    (j : Int)
    (off' : Int)
    (n : Int)
    (p : Int)
    (snd : T5 → Int)
    (bm : T5)
    (h1 : (off' = off ∧ n = (blk_size blk)))
    (h2 : p = ((sstart (MR st m) j) + (UNIT * off)))
    (h3 : (sstart (MR st m) j) = (((snd bm) + UNIT) + ((get_stride (MR st m)) * j)))
    (h4 : (UNIT * (Int.fdiv ((((sstart (MR st m) j) + (UNIT * off)) - (snd bm)) - UNIT) UNIT)) = ((((sstart (MR st m) j) + (UNIT * off)) - (snd bm)) - UNIT)) :
    ((((get_stride (MR st m)) - IB) - (UNIT * off)) - (blk_size blk)) = (((((sstart (MR st m) j) + (get_stride (MR st m))) - IB) - ((sstart (MR st m) j) + (UNIT * off))) - (blk_size blk)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BDrv_C.v (replace)
example
    {T1 : Type}
    (length : T1 → Nat)
    (DATA : T1)
    (LEN : Int)
    (cap : Int)
    (h1 : 67108864 ≤ cap)
    (h2 : cap < 67108864)
    (h3 : (cap * 2) ≤ 67108864) :
    (length DATA) = (Int.toNat LEN) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BDrv_C.v (replace)
example
    {list_byte : Type}
    (until_1 : Int)
    (CNT : list_byte)
    (b7 : Int)
    (length : list_byte → Nat)
    (bs : list_byte)
    (h1 : (((length CNT) : Nat) : Int) < until_1)
    (h2 : (0 < b7 ∧ b7 ≤ 65536))
    (h3 : b7 ≤ (until_1 - (((length CNT) : Nat) : Int)))
    (h4 : (length bs) ≠ 0) :
    (Int.toNat (((length bs) : Nat) : Int)) = (length bs) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BF_depot7.v (replace)
example
    (B0 : Int)
    (b : Int)
    (fr : Int)
    (kStoreBlockFrames : Int)
    (stored_of : Int → Int → Int)
    (B1 : Int)
    (h1 : 0 ≤ b)
    (h2 : fr = ((b * kStoreBlockFrames) + (Int.fmod fr kStoreBlockFrames)))
    (h3 : (stored_of fr b) = (Int.fmod fr kStoreBlockFrames))
    (h4 : (stored_of fr (b + 1)) = 0)
    (h5 : B0 = (1574040 + (16 * b)))
    (h6 : B1 = (B0 + 16)) :
    B0 = (1574040 + (b * 16)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BF_depot7.v (replace)
example
    (fr : Int)
    (b : Int)
    (kStoreBlockFrames : Int)
    (stored_of : Int → Int → Int)
    (B0 : Int)
    (B1 : Int)
    (h1 : 0 ≤ b)
    (h2 : fr = ((b * kStoreBlockFrames) + (Int.fmod fr kStoreBlockFrames)))
    (h3 : (stored_of fr b) = (Int.fmod fr kStoreBlockFrames))
    (h4 : (stored_of fr (b + 1)) = 0)
    (h5 : B0 = (1574040 + (16 * b)))
    (h6 : B1 = (B0 + 16)) :
    1048576 = ((fr % 1048576) + (1048576 - (fr % 1048576))) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BF_free1c.v (replace)
example (len : Int) :
    len = (len + ((2 ^ (32 : Nat)) * 0)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BF_pop0.v (replace)
example
    {T1 T2 T3 : Type}
    (kFreeArrayMapSize : Int)
    (rg_mapped_fa : T1 → Int)
    (get_region : T2 → T3 → T1)
    (a1 : T2)
    (c : T3) :
    kFreeArrayMapSize = (((rg_mapped_fa (get_region a1 c)) + kFreeArrayMapSize) - (rg_mapped_fa (get_region a1 c))) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_asan_memset.v (replace)
example
    {T1 T2 T3 : Type}
    (shw_hi : T1 → T2 → T3 → Int)
    (SB : T1)
    (A : T2)
    (n : T3)
    (shw_lo : T1 → T2 → Int) :
    ((shw_hi SB A n) - 8) = ((shw_lo SB A) + (((shw_hi SB A n) - 8) - (shw_lo SB A))) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_memchr_icp.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (A : Int)
    (cnt : Int)
    (SB : Int)
    (str : list_byte)
    (slack : list_byte)
    (ws : list_byte)
    (lo : Int)
    (j : Int)
    (rc_sp : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (shw_hi : Int → Int → Int → Int)
    (shw_lo : Int → Int → Int)
    (h1 : ((max 140735340871680 (min 140737488355328 rc_sp)) - 8388608) ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 2208))
    (h3 : (((((length str) : Nat) : Int) + 1) ≤ cnt ∧ cnt < (2 ^ (63 : Nat))))
    (h4 : ((-((A + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h5 : ((((length str) : Nat) : Int) + 1) < (2 ^ (40 : Nat)))
    (h6 : ((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) < (2 ^ (47 : Nat)))
    (h7 : (((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ A))
    (h8 : (((length ws) : Nat) : Int) = ((shw_hi SB A ((((length str) : Nat) : Int) + 1)) - (shw_lo SB A)))
    (h9 : ((2 ^ (24 : Nat)) ≤ SB ∧ SB < (2 ^ (32 : Nat)))) :
    (SB + (j + 1)) = ((SB + j) + 1) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_memchr_icp.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (A : Int)
    (cnt : Int)
    (SB : Int)
    (str : list_byte)
    (slack : list_byte)
    (ws : list_byte)
    (lo : Int)
    (shw_hi : Int → Int → Int → Int)
    (length : list_byte → Nat)
    (shw_lo : Int → Int → Int)
    (rc_sp : Int)
    (bv_unsigned : word → Int)
    (h1 : ((max 140735340871680 (min 140737488355328 rc_sp)) - 8388608) ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 2208))
    (h3 : (((((length str) : Nat) : Int) + 1) ≤ cnt ∧ cnt < (2 ^ (63 : Nat))))
    (h4 : ((-((A + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h5 : ((((length str) : Nat) : Int) + 1) < (2 ^ (40 : Nat)))
    (h6 : ((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) < (2 ^ (47 : Nat)))
    (h7 : (((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ A))
    (h8 : (((length ws) : Nat) : Int) = ((shw_hi SB A ((((length str) : Nat) : Int) + 1)) - (shw_lo SB A)))
    (h9 : ((2 ^ (24 : Nat)) ≤ SB ∧ SB < (2 ^ (32 : Nat)))) :
    ((shw_hi SB A ((((length str) : Nat) : Int) + 1)) - 8) = ((shw_lo SB A) + (((shw_hi SB A ((((length str) : Nat) : Int) + 1)) - 8) - (shw_lo SB A))) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_memchr_icp.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (A : Int)
    (cnt : Int)
    (SB : Int)
    (str : list_byte)
    (slack : list_byte)
    (ws : list_byte)
    (lo : Int)
    (length : list_byte → Nat)
    (rc_sp : Int)
    (bv_unsigned : word → Int)
    (shw_hi : Int → Int → Int → Int)
    (shw_lo : Int → Int → Int)
    (h1 : ((max 140735340871680 (min 140737488355328 rc_sp)) - 8388608) ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 2208))
    (h3 : (((((length str) : Nat) : Int) + 1) ≤ cnt ∧ cnt < (2 ^ (63 : Nat))))
    (h4 : ((-((A + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h5 : ((((length str) : Nat) : Int) + 1) < (2 ^ (40 : Nat)))
    (h6 : ((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) < (2 ^ (47 : Nat)))
    (h7 : (((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ A))
    (h8 : (((length ws) : Nat) : Int) = ((shw_hi SB A ((((length str) : Nat) : Int) + 1)) - (shw_lo SB A)))
    (h9 : ((2 ^ (24 : Nat)) ≤ SB ∧ SB < (2 ^ (32 : Nat)))) :
    ((((length str) : Nat) : Int) + 1) = (((A + (((length str) : Nat) : Int)) - A) + 1) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_pcommon.v (replace)
example {T1 : Type} (SA : Int) (zlength : T1 → Int) (zs : T1) :
    (SA + (zlength zs)) = ((SA + ((zlength zs) + 1)) + (-1)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_pcommon.v (replace)
example
    {list_Z T2 : Type}
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
    (Z_to_bv : Int → Int → T2)
    (length : list_Z → Nat)
    (bv_unsigned : T2 → Int)
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
    (h12 : ((NA : Nat) : Int) = ((shw_hi SB SA ((zlength zs) + 1)) - (shw_lo SB SA)))
    (h13 : 65 ≤ ((((length zs) : Nat) : Int) + 1))
    (h14 : (bv_unsigned (Z_to_bv 64 (q + (-2240)))) = (q + (-2240)))
    (h15 : ((((length zs) : Nat) : Int) + 1) ≤ 64) :
    (q - 2240) = (q + (-2240)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_pcommon.v (replace)
example
    {list_Z T2 : Type}
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
    (Z_to_bv : Int → Int → T2)
    (bv_unsigned : T2 → Int)
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
    (h12 : ((NA : Nat) : Int) = ((shw_hi SB SA ((zlength zs) + 1)) - (shw_lo SB SA)))
    (h13 : ((0 < c ∧ c < 256) ∧ (c ≠ 37 ∧ (c ≠ 42 ∧ (c ≠ 46 ∧ (c ≠ 108 ∧ (c ≠ 104 ∧ (c ≠ 109 ∧ (c ≠ 110 ∧ 9 < (c - 48))))))))))
    (h14 : (bv_unsigned (Z_to_bv 64 (q + (-2240)))) = (q + (-2240))) :
    (q - 2240) = (q + (-2240)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_pcommon.v (replace)
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
    (np : Nat)
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
    (A + (((np + 2) : Nat) : Int)) = ((A + ((np : Nat) : Int)) + 2) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_pcommon.v (replace)
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
    (q + (-4096)) = (q - 4096) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_pcommon.v (replace)
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
    (q - 2240) = (q + (-2240)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BI_strlen_icp.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (A : Int)
    (SB : Int)
    (str : list_byte)
    (slack : list_byte)
    (ws : list_byte)
    (lo : Int)
    (length : list_byte → Nat)
    (rc_sp : Int)
    (bv_unsigned : word → Int)
    (shw_hi : Int → Int → Int → Int)
    (shw_lo : Int → Int → Int)
    (h1 : ((max 140735340871680 (min 140737488355328 rc_sp)) - 8388608) ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 2160))
    (h3 : (length str) ≤ 63)
    (h4 : ((-((A + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h5 : 0 < A)
    (h6 : ((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) < (2 ^ (47 : Nat)))
    (h7 : (((A + ((((length str) : Nat) : Int) + 1)) + (((length slack) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ A))
    (h8 : (((length ws) : Nat) : Int) = ((shw_hi SB A ((((length str) : Nat) : Int) + 1)) - (shw_lo SB A)))
    (h9 : ((2 ^ (24 : Nat)) ≤ SB ∧ SB < (2 ^ (32 : Nat)))) :
    ((A + ((((length str) : Nat) : Int) + 1)) + (-1)) = ((((length str) : Nat) : Int) + A) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/BY_parse_pro.v (replace)
example (H : Int) (h1 : (H % 8) = 0) :
    (2147450880 + ((H + 60) / 8)) = (((H + 60) / 8) + 2147450880) := by
  lia

-- yajl-ruby/json_fuzzer: lib/B/B_bframe3.v (assert)
example (N2 : Int) (N1 : Int) (h1 : N1 = N2) (h2 : (N1 = 0 ∨ N1 = 1)) :
    (N2 = 0 ∨ N2 = 1) := by
  lia

-- yajl-ruby/json_fuzzer: lib/BS5/B_MainCells5.v (replace)
example {env T2 : Type} (E : env) (uE : env → T2 → Int) (be : T2) (a : Int) (i : Int) :
    (((uE E be) + (a + 1)) + (i - 1)) = (((uE E be) + a) + i) := by
  lia

-- yajl-ruby/json_fuzzer: lib/BS5/B_MainCells5.v (replace)
example
    {env acs T3 T4 : Type}
    (E : env)
    (hs : acs)
    (be : T3)
    (a : Int)
    (n : Int)
    (uE : env → T3 → Int)
    (o : Int)
    (i : Int)
    (zero_ok : T4 → T3 → Int → Int → Bool)
    (kn : acs → T4)
    (h1 : 0 < n)
    (h2 : (zero_ok (kn hs) be a n) = true) :
    (((uE E be) + o) + ((a - o) + i)) = (((uE E be) + a) + i) := by
  lia

-- yajl-ruby/json_fuzzer: lib/BS5/B_MainRep5.v (replace)
example {env T2 : Type} (E : env) (uE : env → T2 → Int) (e_stop : T2) :
    (((uE E e_stop) - (2 ^ (23 : Nat))) + (1 * (2 ^ (64 : Nat)))) = ((uE E e_stop) + ((2 ^ (64 : Nat)) - 8388608)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/Printf_pieces.v (replace)
example {T1 : Type} (length : T1 → Nat) (body : T1) :
    (((length body) : Nat) : Int) = (max (-1) ((((length body) : Nat) : Int) + 0)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/RF_printf_core_scan.v (replace)
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
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < 140737488355328)
    (h4 : (A + (zlength fmt)) ≤ 131072)
    (h5 : ((145712 ≤ Fp ∧ (Fp + 232) ≤ 348080) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((348088 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (znth fmt i) ≠ 0) :
    n = (((A + i) + n) - (A + i)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/RF_realloc_A.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (po : Int)
    (conc : T1 → T2 → Int)
    (st : T1)
    (pf : T2)
    (blk_addr : T3 → Int)
    (b : T3)
    (bm : T2)
    (r_base : T4 → Int)
    (r : T4)
    (snd : T2 → Int)
    (blk_slot : T3 → T2)
    (i : Int)
    (rsv : Int)
    (stride : Int)
    (m_last_idx : T5 → Int)
    (mr : T5)
    (e : T2)
    (IB : Int)
    (blk_size : T3 → Int)
    (h1 : (conc st pf) = (blk_addr b))
    (h2 : (blk_addr b) = ((r_base r) + po))
    (h3 : (conc st bm) = ((r_base r) + (snd bm)))
    (h4 : (conc st (blk_slot b)) = ((r_base r) + (snd (blk_slot b))))
    (h5 : (0 ≤ i ∧ i < 32))
    (h6 : (0 ≤ (min rsv 5) ∧ (min rsv 5) ≤ 5))
    (h7 : 0 ≤ (stride * i))
    (h8 : (stride * (i + 1)) ≤ (stride * ((m_last_idx mr) + 1)))
    (h9 : (snd e) = (((snd (blk_slot b)) + stride) - IB))
    (h10 : (((snd e) - rsv) - po) = (blk_size b)) :
    (po - 3) = (po + (-3)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/RY_buf_append.v (replace)
example
    {T1 T2 T3 : Type}
    (nn : Nat)
    (n : Int)
    (SA : Int)
    (D1 : Int)
    (len1 : Int)
    (mb_addr : T1 → Int)
    (mb : T1)
    (length : T2 → Nat)
    (tail3 : T2)
    (used1 : Int)
    (bv_unsigned : T3 → Int)
    (Z_to_bv : Int → Int → T3)
    (nu : Nat)
    (nr : Nat)
    (jrest : T2)
    (h1 : ((SA + n) ≤ D1 ∨ (D1 + len1) ≤ SA))
    (h2 : ((SA + n) ≤ (mb_addr mb) ∨ ((mb_addr mb) + 32) ≤ SA))
    (h3 : (length tail3) = (Int.toNat ((len1 - used1) - n)))
    (h4 : (bv_unsigned (Z_to_bv 64 SA)) = SA)
    (h5 : (bv_unsigned (Z_to_bv 64 (D1 + used1))) = (D1 + used1))
    (h6 : (bv_unsigned (Z_to_bv 64 n)) = n)
    (h7 : ((nu : Nat) : Int) = used1)
    (h8 : ((nn : Nat) : Int) = n)
    (h9 : ((nr : Nat) : Int) = (((len1 - used1) - n) - 1))
    (h10 : (length jrest) = nr) :
    nn = (Int.toNat n) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/RY_buf_append.v (replace)
example
    {T1 T2 T3 : Type}
    (nr : Nat)
    (len1 : Int)
    (used1 : Int)
    (n : Int)
    (SA : Int)
    (D1 : Int)
    (mb_addr : T1 → Int)
    (mb : T1)
    (length : T2 → Nat)
    (tail3 : T2)
    (bv_unsigned : T3 → Int)
    (Z_to_bv : Int → Int → T3)
    (nu : Nat)
    (nn : Nat)
    (jrest : T2)
    (h1 : ((SA + n) ≤ D1 ∨ (D1 + len1) ≤ SA))
    (h2 : ((SA + n) ≤ (mb_addr mb) ∨ ((mb_addr mb) + 32) ≤ SA))
    (h3 : (length tail3) = (Int.toNat ((len1 - used1) - n)))
    (h4 : (bv_unsigned (Z_to_bv 64 SA)) = SA)
    (h5 : (bv_unsigned (Z_to_bv 64 (D1 + used1))) = (D1 + used1))
    (h6 : (bv_unsigned (Z_to_bv 64 n)) = n)
    (h7 : ((nu : Nat) : Int) = used1)
    (h8 : ((nn : Nat) : Int) = n)
    (h9 : ((nr : Nat) : Int) = (((len1 - used1) - n) - 1))
    (h10 : (length jrest) = nr) :
    nr = (Int.toNat ((len1 - (used1 + n)) - 1)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/RY_decode2.v (replace)
example
    {T1 T2 : Type}
    (e : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (a : Int)
    (lo : Int)
    (Z_land : T2 → Int → Int)
    (cp : T2)
    (n : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-208)))) = ((bv_unsigned sp) + (-208)))
    (h2 : ((bv_unsigned sp) ≤ a ∨ a < lo))
    (h3 : (Z_land cp 64512) ≠ 55296)
    (h4 : (Z_land cp 64512) = 55296)
    (h5 : (e + 7) < n) :
    ((e + 6) + 6) = (e + 12) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/RY_decode2.v (replace)
example
    {T1 T2 : Type}
    (e : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (a : Int)
    (lo : Int)
    (Z_land : T2 → Int → Int)
    (cp : T2)
    (n : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-208)))) = ((bv_unsigned sp) + (-208)))
    (h2 : ((bv_unsigned sp) ≤ a ∨ a < lo))
    (h3 : (Z_land cp 64512) ≠ 55296)
    (h4 : (Z_land cp 64512) = 55296)
    (h5 : (e + 7) < n) :
    (e + 11) = ((e + 8) + 3) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/RY_decode2.v (replace)
example
    {T1 T2 T3 : Type}
    (e : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (a : Int)
    (lo : Int)
    (Z_land : T2 → Int → Int)
    (cp : T2)
    (n : Int)
    (combine_surrogate : T2 → T3 → Int)
    (sur : T3)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-208)))) = ((bv_unsigned sp) + (-208)))
    (h2 : ((bv_unsigned sp) ≤ a ∨ a < lo))
    (h3 : (Z_land cp 64512) ≠ 55296)
    (h4 : (Z_land cp 64512) = 55296)
    (h5 : (e + 7) < n)
    (h6 : (65536 ≤ (combine_surrogate cp sur) ∧ (combine_surrogate cp sur) < 2097152)) :
    (e + 2) = ((e + 1) + 1) := by
  lia

-- yajl-ruby/json_fuzzer: lib/R/RY_decode2.v (replace)
example
    {T1 T2 T3 : Type}
    (e : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (a : Int)
    (lo : Int)
    (Z_land : T2 → Int → Int)
    (cp : T2)
    (n : Int)
    (combine_surrogate : T2 → T3 → Int)
    (sur : T3)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-208)))) = ((bv_unsigned sp) + (-208)))
    (h2 : ((bv_unsigned sp) ≤ a ∨ a < lo))
    (h3 : (Z_land cp 64512) ≠ 55296)
    (h4 : (Z_land cp 64512) = 55296)
    (h5 : (e + 7) < n)
    (h6 : (65536 ≤ (combine_surrogate cp sur) ∧ (combine_surrogate cp sur) < 2097152)) :
    (e + 8) = (((((e + 1) + 1) + 3) + 1) + 2) := by
  lia

-- yajl-ruby/json_fuzzer: lib/Spec/LB_Realloc.v (replace)
example
    {list_blk aptr T3 T4 T5 : Type}
    (BL : list_blk)
    (off : Int)
    (n : Int)
    (B : Int)
    (m : aptr)
    (needed : Int)
    (IB : Int)
    (UNIT : Int)
    (size_overflows : Int → Bool)
    (PHI : T3 → Int)
    (P : T3)
    (R63 : list_blk → Int)
    (bigb : Int → Int)
    (PGSZ : Int)
    (m_sizeclass : T4 → Int)
    (MR : T5 → aptr → T4)
    (st0 : T5)
    (stride : Int)
    (m_maplen : T4 → Int)
    (str : T5)
    (get_stride : T4 → Int)
    (sstart : T4 → Int → Int)
    (m_last_idx : T4 → Int)
    (h1 : 0 ≤ n)
    (h2 : (size_overflows n) = false)
    (h3 : (((PHI P) + (R63 BL)) + (bigb n)) ≤ (B + (3 * PGSZ)))
    (h4 : (m_sizeclass (MR st0 m)) < 48)
    (h5 : (m_sizeclass (MR st0 m)) = 63)
    (h6 : 0 < needed)
    (h7 : ((UNIT * off) + n) ≤ (stride - IB))
    (h8 : (((stride - IB) - (UNIT * off)) - n) < (2 ^ (32 : Nat)))
    (h9 : (m_maplen (MR str m)) = (needed / 4096))
    (h10 : (needed / 4096) < (2 ^ (52 : Nat)))
    (h11 : ((needed / 4096) * 4096) = needed)
    (h12 : (get_stride (MR str m)) = (needed - UNIT))
    (h13 : (sstart (MR str m) 0) = UNIT)
    (h14 : ((0 : Int) ≤ 0 ∧ 0 ≤ (m_last_idx (MR str m))))
    (h15 : ((UNIT * off) + n) ≤ ((get_stride (MR str m)) - IB))
    (h16 : ((((get_stride (MR str m)) - IB) - (UNIT * off)) - n) < (2 ^ (32 : Nat))) :
    (needed - IB) = (UNIT + ((needed - UNIT) - IB)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/Spec/YajlFactsDecode.v (replace)
example
    {T1 : Type}
    (e : Int)
    (yb_used : T1 → Int)
    (b1 : T1)
    (K : Int)
    (b2 : T1)
    (h1 : (yb_used b1) ≤ (K + e))
    (h2 : (yb_used b2) ≤ ((K + e) + 1))
    (h3 : (yb_used b2) ≤ ((K + e) + 5)) :
    (e + 5) = (((e + 1) + 1) + 3) := by
  lia

-- yajl-ruby/json_fuzzer: lib/SpecA/AsanRepHitB.v (replace)
example
    {aenv astate T3 T4 : Type}
    (E : aenv)
    (s : astate)
    (r : Int)
    (fst : T3 → Int)
    (ae_img : aenv → T3)
    (snd : T3 → Int)
    (as_cache_inited : astate → Bool)
    (ae_thread : aenv → Int)
    (ae_depot_nodes : aenv → Int)
    (kDepotNodeBlockBytes : Int)
    (zlen : T4 → Int)
    (ae_ptr_array : aenv → Int)
    (kPtrArrayLen : Int)
    (NB : T4)
    (h1 : ((fst (ae_img E)) = 65536 ∧ 6238208 ≤ (snd (ae_img E))))
    (h2 : (as_cache_inited s) = true)
    (h3 : (((ae_thread E) + 4096) ≤ (ae_depot_nodes E) ∨ ((ae_depot_nodes E) + kDepotNodeBlockBytes) ≤ (ae_thread E)))
    (h4 : (((ae_thread E) + 4096) ≤ (ae_ptr_array E) ∨ ((ae_ptr_array E) + kPtrArrayLen) ≤ (ae_thread E)))
    (h5 : (1 ≤ r ∧ r < (zlen NB))) :
    ((Int.toNat (r - 1)) + 1) = (Int.toNat r) := by
  lia

-- yajl-ruby/json_fuzzer: lib/SpecA/AsanRepLdlB.v (replace)
example
    {astate chunkmeta secchunk list_word T5 : Type}
    (s : astate)
    (cb : Int)
    (cm : chunkmeta)
    (sc : secchunk)
    (i : Nat)
    (junk : list_word)
    (sc_map_size : T5 → Int)
    (List_last : list_word → secchunk → T5)
    (as_sec : astate → list_word)
    (cm_alloc_beg : chunkmeta → Int)
    (sc_map_beg : secchunk → Int)
    (kPageSize : Int)
    (length : list_word → Nat)
    (ldl_st : Int → chunkmeta → secchunk → Nat → astate → astate)
    (kChunksBlockCount : Int)
    (h1 : (cm_alloc_beg cm) = ((sc_map_beg sc) + kPageSize))
    (h2 : ((length (as_sec (ldl_st cb cm sc i s))) + (length junk)) = (Int.toNat kChunksBlockCount)) :
    (24 + (8 + ((sc_map_size (List_last (as_sec s) sc)) - 32))) = (sc_map_size (List_last (as_sec s) sc)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/U/UDrv_C.v (replace)
example
    {T1 : Type}
    (TID : Int)
    (A' : Int)
    (length : T1 → Nat)
    (DATA : T1)
    (LEN : Int)
    (cap : Int)
    (h1 : (0 < TID ∧ TID < 4194304))
    (h2 : 67108864 ≤ cap)
    (h3 : cap < 67108864)
    (h4 : (cap * 2) ≤ 67108864) :
    (A' + ((((length DATA) + 0) : Nat) : Int)) = (A' + ((((Int.toNat LEN) + 0) : Nat) : Int)) := by
  lia

-- yajl-ruby/json_fuzzer: lib/U/UDrv_C.v (replace)
example
    {word EntryDraw T3 T4 T5 : Type}
    (sp0 : word)
    (rnd : EntryDraw)
    (TID : Int)
    (length : T3 → Nat)
    (bs : T3)
    (rc_sp : Int)
    (bv_unsigned : word → Int)
    (rc_secret : Int)
    (secret_of : T4 → word)
    (at_random_bytes : T5 → T4)
    (ed_random : EntryDraw → T5)
    (h1 : rc_sp = (bv_unsigned sp0))
    (h2 : rc_secret = (bv_unsigned (secret_of (at_random_bytes (ed_random rnd)))))
    (h3 : (0 < TID ∧ TID < 4194304))
    (h4 : (length bs) ≠ 0) :
    (Int.toNat (((length bs) : Nat) : Int)) = (length bs) := by
  lia

-- yajl-ruby/json_fuzzer: lib/U/UY_buf_append.v (replace)
example
    {T1 T2 T3 : Type}
    (D1 : Int)
    (used1 : Int)
    (SA : Int)
    (n : Int)
    (len1 : Int)
    (mb_addr : T1 → Int)
    (mb : T1)
    (length : T2 → Nat)
    (tail3 : T2)
    (bv_unsigned : T3 → Int)
    (Z_to_bv : Int → Int → T3)
    (nu : Nat)
    (nn : Nat)
    (nr : Nat)
    (jrest : T2)
    (h1 : ((SA + n) ≤ D1 ∨ (D1 + len1) ≤ SA))
    (h2 : ((SA + n) ≤ (mb_addr mb) ∨ ((mb_addr mb) + 32) ≤ SA))
    (h3 : (length tail3) = (Int.toNat ((len1 - used1) - n)))
    (h4 : (bv_unsigned (Z_to_bv 64 SA)) = SA)
    (h5 : (bv_unsigned (Z_to_bv 64 (D1 + used1))) = (D1 + used1))
    (h6 : (bv_unsigned (Z_to_bv 64 n)) = n)
    (h7 : ((nu : Nat) : Int) = used1)
    (h8 : ((nn : Nat) : Int) = n)
    (h9 : ((nr : Nat) : Int) = (((len1 - used1) - n) - 1))
    (h10 : (length jrest) = nr) :
    (D1 + used1) = (used1 + D1) := by
  lia

-- yajl-ruby/json_fuzzer: lib/U/UY_decode2.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (e : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (is_vhc : T2 → Bool)
    (znth : T3 → Int → T2)
    (str : T3)
    (a : Int)
    (lo : Int)
    (Z_land : T4 → Int → Int)
    (cp : T4)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-208)))) = ((bv_unsigned sp) + (-208)))
    (h2 : (is_vhc (znth str (e + 2))) = true)
    (h3 : (is_vhc (znth str (e + 3))) = true)
    (h4 : (is_vhc (znth str (e + 4))) = true)
    (h5 : (is_vhc (znth str (e + 5))) = true)
    (h6 : ((bv_unsigned sp) ≤ a ∨ a < lo))
    (h7 : (Z_land cp 64512) ≠ 55296) :
    (e + 2) = ((e + 1) + 1) := by
  lia

-- yajl-ruby/json_fuzzer: lib/U/UY_decode2.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (e : Int)
    (k : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (is_vhc : T2 → Bool)
    (znth : T3 → Int → T2)
    (str : T3)
    (a : Int)
    (lo : Int)
    (Z_land : T4 → Int → Int)
    (cp : T4)
    (n : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-208)))) = ((bv_unsigned sp) + (-208)))
    (h2 : (is_vhc (znth str (e + 2))) = true)
    (h3 : (is_vhc (znth str (e + 3))) = true)
    (h4 : (is_vhc (znth str (e + 4))) = true)
    (h5 : (is_vhc (znth str (e + 5))) = true)
    (h6 : ((bv_unsigned sp) ≤ a ∨ a < lo))
    (h7 : (Z_land cp 64512) ≠ 55296)
    (h8 : (Z_land cp 64512) = 55296)
    (h9 : (e + 7) < n) :
    (((e + 6) + 2) + k) = ((e + 8) + k) := by
  lia

-- yajl-ruby/json_fuzzer: lib/U/UY_decode2.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (e : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (is_vhc : T2 → Bool)
    (znth : T3 → Int → T2)
    (str : T3)
    (a : Int)
    (lo : Int)
    (Z_land : T4 → Int → Int)
    (cp : T4)
    (n : Int)
    (combine_surrogate : T4 → T5 → Int)
    (sur : T5)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-208)))) = ((bv_unsigned sp) + (-208)))
    (h2 : (is_vhc (znth str (e + 2))) = true)
    (h3 : (is_vhc (znth str (e + 3))) = true)
    (h4 : (is_vhc (znth str (e + 4))) = true)
    (h5 : (is_vhc (znth str (e + 5))) = true)
    (h6 : ((bv_unsigned sp) ≤ a ∨ a < lo))
    (h7 : (Z_land cp 64512) ≠ 55296)
    (h8 : (Z_land cp 64512) = 55296)
    (h9 : (e + 7) < n)
    (h10 : (is_vhc (znth str (e + 8))) = true)
    (h11 : (is_vhc (znth str (e + 9))) = true)
    (h12 : (is_vhc (znth str (e + 10))) = true)
    (h13 : (is_vhc (znth str (e + 11))) = true)
    (h14 : (65536 ≤ (combine_surrogate cp sur) ∧ (combine_surrogate cp sur) < 2097152)) :
    (e + 2) = ((e + 1) + 1) := by
  lia

-- zstd/fse_read_ncount: lib/AsanW/AF_fse_write_A.v (replace)
example
    {list_Z : Type}
    (SP : Int)
    (BUF : Int)
    (NC : Int)
    (buf0 : list_Z)
    (nc : list_Z)
    (msv : Int)
    (lo : Int)
    (sym : Int)
    (zlen : list_Z → Int)
    (KHIGH : Int)
    (h1 : (0 ≤ msv ∧ msv ≤ 255))
    (h2 : (zlen buf0) ≤ 65536)
    (h3 : 0 < BUF)
    (h4 : 0 < NC)
    (h5 : (NC % 2) = 0)
    (h6 : lo ≤ (SP - 96))
    (h7 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h8 : ((BUF + (zlen buf0)) ≤ (SP - 96) ∨ SP ≤ BUF))
    (h9 : ((NC + (2 * (zlen nc))) ≤ (SP - 96) ∨ SP ≤ NC))
    (h10 : ((NC + (2 * (zlen nc))) ≤ BUF ∨ (BUF + (zlen buf0)) ≤ NC))
    (h11 : (BUF % 8) = 0)
    (h12 : (NC % 8) = 0)
    (h13 : KHIGH ≤ lo) :
    ((msv + 1) - (sym + 1)) = (((msv + 1) - sym) + (-1)) := by
  lia

-- zstd/fse_read_ncount: lib/AsanW/AF_fse_write_A.v (replace)
example
    {list_Z : Type}
    (SP : Int)
    (BUF : Int)
    (NC : Int)
    (buf0 : list_Z)
    (nc : list_Z)
    (msv : Int)
    (lo : Int)
    (sym : Int)
    (zlen : list_Z → Int)
    (KHIGH : Int)
    (h1 : (0 ≤ msv ∧ msv ≤ 255))
    (h2 : (zlen buf0) ≤ 65536)
    (h3 : 0 < BUF)
    (h4 : 0 < NC)
    (h5 : (NC % 2) = 0)
    (h6 : lo ≤ (SP - 96))
    (h7 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h8 : ((BUF + (zlen buf0)) ≤ (SP - 96) ∨ SP ≤ BUF))
    (h9 : ((NC + (2 * (zlen nc))) ≤ (SP - 96) ∨ SP ≤ NC))
    (h10 : ((NC + (2 * (zlen nc))) ≤ BUF ∨ (BUF + (zlen buf0)) ≤ NC))
    (h11 : (BUF % 8) = 0)
    (h12 : (NC % 8) = 0)
    (h13 : KHIGH ≤ lo) :
    (NC + (2 * (sym + 1))) = ((NC + (2 * sym)) + 2) := by
  lia

-- zstd/fse_read_ncount: lib/AsanW/AH_fse_B2.v (replace)
example
    {T1 T2 : Type}
    (F : Int)
    (zlen : T1 → Int)
    (nc : T1)
    (Z_shiftr : Int → Int → Int)
    (ASHOFF : Int)
    (pl : T1)
    (D : Int)
    (ATOP : Int)
    (P : Int)
    (map : T2 → T1 → T1)
    (Z_to_bv : Int → T2)
    (length : T1 → Nat)
    (jdata : T1)
    (data0 : T1)
    (u16s : T1 → T1)
    (h1 : (2147450880 ≤ ((Z_shiftr F 3) + ASHOFF) ∧ (((Z_shiftr F 3) + ASHOFF) + 256) ≤ 17594333495296))
    (h2 : ((F + 2048) ≤ ((Z_shiftr F 3) + ASHOFF) ∨ (((Z_shiftr F 3) + ASHOFF) + 256) ≤ F))
    (h3 : (0 < D ∧ (D + (zlen pl)) ≤ ATOP))
    (h4 : ((P + 16) ≤ ((Z_shiftr F 3) + ASHOFF) ∨ (((Z_shiftr F 3) + ASHOFF) + 256) ≤ P))
    (h5 : ((D + (zlen pl)) ≤ ((Z_shiftr F 3) + ASHOFF) ∨ (((Z_shiftr F 3) + ASHOFF) + 256) ≤ D))
    (h6 : (zlen (map (Z_to_bv 8) pl)) = (zlen pl))
    (h7 : (length jdata) = 512)
    (h8 : (length data0) = 512)
    (h9 : (length (map (Z_to_bv 64) nc)) = 256)
    (h10 : (length (u16s (map (Z_to_bv 64) nc))) = 512)
    (h11 : (zlen data0) = 512)
    (h12 : (zlen nc) = 256) :
    ((F + 608) + (2 * (zlen nc))) = (F + 1120) := by
  lia

-- zstd/fse_read_ncount: lib/AsanW/AH_fse_D1.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (bsz : Int)
    (dsz : Int)
    (pl : T1)
    (D : Int)
    (zlen : T1 → Int)
    (ATOP : Int)
    (map : T2 → T1 → T1)
    (Z_to_bv : Int → T2)
    (length : T1 → Nat)
    (data : T1)
    (F : Int)
    (firstn : Nat → T3 → T1)
    (skipn : Nat → T4 → T3)
    (jB : T4)
    (shad : Int → Int)
    (h1 : (0 < D ∧ (D + (zlen pl)) ≤ ATOP))
    (h2 : (zlen (map (Z_to_bv 8) pl)) = (zlen pl))
    (h3 : (length data) = (Int.toNat dsz))
    (h4 : (zlen data) = dsz)
    (h5 : (length (map (Z_to_bv 8) data)) = (Int.toNat dsz))
    (h6 : (length (firstn (Int.toNat (bsz - dsz)) (skipn (Int.toNat dsz) jB))) = (Int.toNat (bsz - dsz)))
    (h7 : ((shad (F + 576)) - (shad F)) = 72)
    (h8 : ((F % 64) = 0 ∧ ((F + 576) % 64) = 0))
    (h9 : dsz = bsz) :
    0 = (Int.toNat (bsz - dsz)) := by
  lia

-- zstd/fse_read_ncount: lib/BothW/AF_fse_prod.v (replace)
example
    {list_Z T2 : Type}
    (SP : Int)
    (P : Int)
    (D : Int)
    (pl : list_Z)
    (size : Int)
    (lo : Int)
    (Z_shiftr : Int → Int → Int)
    (sz : Int)
    (zlen : list_Z → Int)
    (KHIGH : Int)
    (map : T2 → list_Z → list_Z)
    (Z_to_bv : Int → T2)
    (h1 : (0 ≤ size ∧ size ≤ (zlen pl)))
    (h2 : 0 < P)
    (h3 : (P % 8) = 0)
    (h4 : 0 < D)
    (h5 : lo ≤ (SP - 16))
    (h6 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h7 : (P + 16) ≤ lo)
    (h8 : (D + (zlen pl)) ≤ lo)
    (h9 : ((D + (zlen pl)) ≤ P ∨ (P + 16) ≤ D))
    (h10 : (D % 8) = 0)
    (h11 : KHIGH ≤ lo)
    (h12 : (zlen (map (Z_to_bv 8) pl)) = (zlen pl))
    (h13 : sz = 0)
    (h14 : 0 < sz) :
    ((Z_shiftr ((sz + (-1)) + D) 3) + 2147450880) = (2147450880 + (Z_shiftr ((sz + (-1)) + D) 3)) := by
  lia

-- zstd/fse_read_ncount: lib/BothW/AF_fse_write_A.v (replace)
example
    (nb : Int)
    (thr : Int)
    (Zpow : Int → Int → Int)
    (h1 : 2 ≤ nb)
    (h2 : (2 ≤ thr ∧ thr ≤ 4096))
    (h3 : (thr / 2) = (Zpow 2 ((nb - 1) - 1))) :
    (nb + (-1)) = (nb - 1) := by
  lia

-- zstd/fse_read_ncount: lib/BothW/AF_fse_write_A.v (replace)
example
    {list_Z : Type}
    (SP : Int)
    (BUF : Int)
    (NC : Int)
    (buf0 : list_Z)
    (nc : list_Z)
    (msv : Int)
    (lo : Int)
    (sym : Int)
    (zlen : list_Z → Int)
    (KHIGH : Int)
    (h1 : (0 ≤ msv ∧ msv ≤ 255))
    (h2 : (zlen buf0) ≤ 65536)
    (h3 : 0 < BUF)
    (h4 : 0 < NC)
    (h5 : (NC % 2) = 0)
    (h6 : lo ≤ (SP - 144))
    (h7 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h8 : ((BUF + (zlen buf0)) ≤ (SP - 144) ∨ SP ≤ BUF))
    (h9 : ((NC + (2 * (zlen nc))) ≤ (SP - 144) ∨ SP ≤ NC))
    (h10 : ((NC + (2 * (zlen nc))) ≤ BUF ∨ (BUF + (zlen buf0)) ≤ NC))
    (h11 : (BUF % 8) = 0)
    (h12 : (NC % 8) = 0)
    (h13 : KHIGH ≤ lo) :
    (2 * (sym + 1)) = ((2 * sym) + 2) := by
  lia

-- zstd/fse_read_ncount: lib/BothW/AF_fse_write_B2.v (replace)
example
    {list_Z T2 T3 : Type}
    (SP : Int)
    (BUF : Int)
    (NC : Int)
    (buf0 : list_Z)
    (nc : list_Z)
    (msv : Int)
    (lo : Int)
    (s : T2)
    (X : Int)
    (bc1 : Int)
    (zlen : list_Z → Int)
    (KHIGH : Int)
    (w_symbol : T2 → Int)
    (w_bitStream : T2 → Int)
    (w_threshold : T2 → Int)
    (count2 : Int)
    (rem' : Int)
    (w_bitCount : T2 → Int)
    (bv_swrap : Int → T3 → Int)
    (Z_shiftl : Int → Int → T3)
    (h1 : (0 ≤ msv ∧ msv ≤ 255))
    (h2 : (zlen buf0) ≤ 65536)
    (h3 : 0 < BUF)
    (h4 : 0 < NC)
    (h5 : (NC % 2) = 0)
    (h6 : lo ≤ (SP - 144))
    (h7 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h8 : ((BUF + (zlen buf0)) ≤ (SP - 144) ∨ SP ≤ BUF))
    (h9 : ((NC + (2 * (zlen nc))) ≤ (SP - 144) ∨ SP ≤ NC))
    (h10 : ((NC + (2 * (zlen nc))) ≤ BUF ∨ (BUF + (zlen buf0)) ≤ NC))
    (h11 : (BUF % 8) = 0)
    (h12 : (NC % 8) = 0)
    (h13 : KHIGH ≤ lo)
    (h14 : (w_symbol s) < (msv + 1))
    (h15 : (0 ≤ X ∧ X < (2 ^ (64 : Nat))))
    (h16 : (Int.fmod X (2 ^ (32 : Nat))) = (w_bitStream s))
    (h17 : (1 ≤ (w_threshold s) ∧ (w_threshold s) ≤ 4096))
    (h18 : ((-50000) ≤ count2 ∧ count2 < 50000))
    (h19 : (0 ≤ bc1 ∧ bc1 ≤ 44))
    (h20 : (1 ≤ rem' ∧ rem' ≤ 8192))
    (h21 : (0 ≤ (Int.fmod ((bv_swrap 32 (Z_shiftl (count2 % 18446744073709551616) ((w_bitCount s) % 32))) + X) (2 ^ (64 : Nat))) ∧ (Int.fmod ((bv_swrap 32 (Z_shiftl (count2 % 18446744073709551616) ((w_bitCount s) % 32))) + X) (2 ^ (64 : Nat))) < (2 ^ (64 : Nat)))) :
    (bc1 - 16) = (bc1 + (-16)) := by
  lia

-- zstd/fse_read_ncount: lib/BothW/AH_fse_D1.v (replace)
example
    {T1 T2 : Type}
    (bsz : Int)
    (dsz : Int)
    (D : Int)
    (zlen : T1 → Int)
    (pl : T1)
    (ATOP : Int)
    (shad : Int → Int)
    (F : Int)
    (map : T2 → T1 → T1)
    (Z_to_bv : Int → T2)
    (length : T1 → Nat)
    (data : T1)
    (rest : T1)
    (h1 : (0 < D ∧ (D + (zlen pl)) ≤ ATOP))
    (h2 : ((shad (F + 576)) - (shad F)) = 72)
    (h3 : ((F % 64) = 0 ∧ ((F + 576) % 64) = 0))
    (h4 : (zlen (map (Z_to_bv 8) pl)) = (zlen pl))
    (h5 : (length data) = (Int.toNat dsz))
    (h6 : (zlen data) = dsz)
    (h7 : (length (map (Z_to_bv 8) data)) = (Int.toNat dsz))
    (h8 : (length rest) = (Int.toNat (bsz - dsz)))
    (h9 : bsz = dsz) :
    (((Int.toNat (bsz - dsz)) : Nat) : Int) = (bsz - dsz) := by
  lia

-- zstd/fse_read_ncount: lib/BothW/AH_fse_kit.v (replace)
example (SP : Int) :
    (((((((((((((SP + (-104)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) + ((8 : Nat) : Int)) = (SP - 8) := by
  lia

-- zstd/fse_read_ncount: lib/BothW/ARefillP.v (assert)
example (c : Int) (c' : Int) (h1 : (1 ≤ c ∧ c < 32)) (h2 : (1 ≤ c' ∧ c' < 32)) (h3 : c' ≠ c) :
    ((c' + 1) ≤ c ∨ (c + 1) ≤ c') := by
  lia

-- zstd/fse_read_ncount: lib/BothW/F_irt.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (a0 : T1)
    (i : Int)
    (length : T2 → Nat)
    (str : T2)
    (h1 : i = (((length str) : Nat) : Int)) :
    (((bv_unsigned a0) + i) + 1) = ((bv_unsigned a0) + (((Int.toNat (i + 1)) : Nat) : Int)) := by
  lia

-- zstd/fse_read_ncount: lib/Common/FseRdKit.v (replace)
example (b2 : Int) (b3 : Int) (S3 : Int) (h1 : (Int.fmod S3 (2 ^ (24 : Nat))) = 0) :
    (((b2 + (b3 * (2 ^ (8 : Nat)))) + ((2 ^ (48 : Nat)) - (2 ^ (16 : Nat)))) * (2 ^ (16 : Nat))) = ((b2 * (2 ^ (16 : Nat))) + ((b3 * (2 ^ (24 : Nat))) + ((2 ^ (64 : Nat)) - (2 ^ (32 : Nat))))) := by
  lia

-- zstd/fse_read_ncount: lib/Plain/RMalloc_fp.v (replace)
example
    {T1 T2 : Type}
    (snd : T1 → Int)
    (b : T1)
    (stride : Int)
    (idx : Int)
    (B : Int)
    (r_base : T2 → Int)
    (r : T2)
    (q : Int)
    (h1 : B = ((r_base r) + (snd b)))
    (h2 : 0 ≤ (stride * idx))
    (h3 : (stride * idx) = (16 * (q * idx))) :
    ((((snd b) + 16) + (stride * idx)) - 1) = ((((snd b) + (16 + (stride * idx))) + (-2)) + 1) := by
  lia

-- zstd/fse_read_ncount: lib/Spec/FseReadSound.v (replace)
example
    {T1 : Type}
    (r_bitCount : T1 → Int)
    (s : T1)
    (h_1 : Int)
    (ip' : Int)
    (bc' : Int)
    (r_ip : T1 → Int)
    (w : Int)
    (Zpow : Int → Int → Int)
    (h1 : (0 ≤ ip' ∧ ((ip' + 4) ≤ h_1 ∧ ((0 ≤ bc' ∧ bc' < 32) ∧ ((bc' ≤ 7 ∨ ip' = (h_1 - 4)) ∧ (3 ≤ ip' ∧ (((r_ip s) ≤ (h_1 - 7) ∧ ip' = ((r_ip s) + 3)) ∨ ((h_1 - 7) < (r_ip s) ∧ (ip' = (h_1 - 4) ∧ bc' = (((r_bitCount s) - (8 * ((h_1 - 7) - (r_ip s)))) % 32))))))))))
    (h2 : (0 ≤ (Int.fdiv w (Zpow 2 bc')) ∧ (Int.fdiv w (Zpow 2 bc')) < (2 ^ (32 : Nat))))
    (h3 : (r_ip s) = (h_1 - 4)) :
    ((r_bitCount s) + 24) = ((r_bitCount s) - (8 * ((h_1 - 7) - (h_1 - 4)))) := by
  lia

-- zstd/fse_read_ncount: lib/Spec/FseReadSound.v (replace)
example
    {T1 : Type}
    (r_bitCount : T1 → Int)
    (s : T1)
    (ip' : Int)
    (h_1 : Int)
    (bc' : Int)
    (r_ip : T1 → Int)
    (w : Int)
    (Zpow : Int → Int → Int)
    (h1 : (0 ≤ ip' ∧ ((ip' + 4) ≤ h_1 ∧ ((0 ≤ bc' ∧ bc' < 32) ∧ ((bc' ≤ 7 ∨ ip' = (h_1 - 4)) ∧ (3 ≤ ip' ∧ (((r_ip s) ≤ (h_1 - 7) ∧ ip' = ((r_ip s) + 3)) ∨ ((h_1 - 7) < (r_ip s) ∧ (ip' = (h_1 - 4) ∧ bc' = (((r_bitCount s) - (8 * ((h_1 - 7) - (r_ip s)))) % 32))))))))))
    (h2 : (0 ≤ (Int.fdiv w (Zpow 2 bc')) ∧ (Int.fdiv w (Zpow 2 bc')) < (2 ^ (32 : Nat))))
    (h3 : (r_ip s) = (h_1 - 4))
    (h4 : ((8 ≤ (r_bitCount s) ∧ (r_bitCount s) ≤ 16) ∧ bc' = ((r_bitCount s) - 8))) :
    (((r_bitCount s) - 8) + (1 * 32)) = ((r_bitCount s) + 24) := by
  lia

-- zstd/fse_read_ncount: lib/Spec/FseReadSound.v (replace)
example
    {T1 T2 : Type}
    (Z_log2 : Int → Int)
    (rem' : Int)
    (r_nbBits : T1 → Int)
    (s : T1)
    (Zpow : Int → Int → Int)
    (tl : Int)
    (Z_land : T2 → Int → Int)
    (bs : T2)
    (thr : Int)
    (rem : Int)
    (count : Int)
    (to_short : Int → Int)
    (h1 : (2 ≤ (Zpow 2 ((r_nbBits s) - 1)) ∧ (Zpow 2 ((r_nbBits s) - 1)) ≤ (Zpow 2 tl)))
    (h2 : (Zpow 2 tl) ≤ (2 ^ (15 : Nat)))
    (h3 : (0 ≤ (Z_land bs (thr - 1)) ∧ (Z_land bs (thr - 1)) ≤ (thr - 1)))
    (h4 : (0 ≤ (Z_land bs ((2 * thr) - 1)) ∧ (Z_land bs ((2 * thr) - 1)) ≤ ((2 * thr) - 1)))
    (h5 : (rem' = (rem - ((count).natAbs : Int)) ∧ rem' ≤ rem))
    (h6 : (Zpow 2 tl) ≤ (2 ^ (14 : Nat)))
    (h7 : (to_short count) = count)
    (h8 : (Z_log2 rem') < tl) :
    (Z_log2 rem') = (((Z_log2 rem') + 1) - 1) := by
  lia

-- zstd/simple_decompress: lib/BothW/AFake_arepk1.v (replace)
example
    {T1 : Type}
    (F : Int)
    (h_1 : Int)
    (Z_land : Int → Int → Int)
    (al_fake : T1 → Int)
    (L : T1)
    (fk_flag : T1 → Int → Int → Int)
    (i : Nat)
    (j : Nat)
    (pos : Int)
    (flag : Int)
    (fk_frame : T1 → Int → Int → Int)
    (fflag : T1 → Int → Int → Int)
    (shad : Int → Int)
    (shlen : Int → Int)
    (pos' : Int)
    (n : Int)
    (c : Int)
    (a' : Int)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (Z_land (h_1 + ((i : Nat) : Int)) 8191) = (Z_land (h_1 + ((j : Nat) : Int)) 8191))
    (h3 : (0 ≤ pos ∧ pos < 8192))
    (h4 : flag = (fk_flag L 1 pos))
    (h5 : F = (fk_frame L 1 pos))
    (h6 : (fflag L 1 F) = flag)
    (h7 : (shad F) = (2147450880 + (F / 8)))
    (h8 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h9 : ((((shad (al_fake L)) + 135680) + (16 * pos)) = (shad F) ∧ (((shad F) + 16) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 16) ≤ 17594333495296)))
    (h10 : (((shad F) + 16) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h11 : pos' = pos)
    (h12 : pos = (Z_land (h_1 + n) 8191))
    (h13 : flag = (((al_fake L) + 20480) + pos))
    (h14 : F = (((al_fake L) + 1085440) + (pos * 128)))
    (h15 : (F % 128) = 0)
    (h16 : (fk_flag L c pos') ≠ flag)
    (h17 : (shad a') = (2147450880 + (a' / 8))) :
    (F + 24) = ((F + ((8 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- zstd/simple_decompress: lib/BothW/AFake_arepk2.v (replace)
example
    {T1 : Type}
    (F : Int)
    (h_1 : Int)
    (Z_land : Int → Int → Int)
    (al_fake : T1 → Int)
    (L : T1)
    (fk_flag : T1 → Int → Int → Int)
    (i : Nat)
    (j : Nat)
    (pos : Int)
    (flag : Int)
    (fk_frame : T1 → Int → Int → Int)
    (fflag : T1 → Int → Int → Int)
    (shad : Int → Int)
    (shlen : Int → Int)
    (pos' : Int)
    (n : Int)
    (c : Int)
    (a' : Int)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (Z_land (h_1 + ((i : Nat) : Int)) 4095) = (Z_land (h_1 + ((j : Nat) : Int)) 4095))
    (h3 : (0 ≤ pos ∧ pos < 4096))
    (h4 : flag = (fk_flag L 2 pos))
    (h5 : F = (fk_frame L 2 pos))
    (h6 : (fflag L 2 F) = flag)
    (h7 : (shad F) = (2147450880 + (F / 8)))
    (h8 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h9 : ((((shad (al_fake L)) + 266752) + (32 * pos)) = (shad F) ∧ (((shad F) + 32) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 32) ≤ 17594333495296)))
    (h10 : (((shad F) + 32) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h11 : pos' = pos)
    (h12 : pos = (Z_land (h_1 + n) 4095))
    (h13 : flag = (((al_fake L) + 28672) + pos))
    (h14 : F = (((al_fake L) + 2134016) + (pos * 256)))
    (h15 : (F % 256) = 0)
    (h16 : (fk_flag L c pos') ≠ flag)
    (h17 : (shad a') = (2147450880 + (a' / 8))) :
    (F + 8) = (F + ((8 : Nat) : Int)) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_bfse_defs.v (replace)
example
    (tl : Int)
    (Zpow : Int → Int → Int)
    (h1 : (2 ^ (5 : Nat)) ≤ (Zpow 2 tl))
    (h2 : (Zpow 2 tl) ≤ (2 ^ (9 : Nat)))
    (h3 : (2 ^ (4 : Nat)) ≤ (Zpow 2 (tl - 1)))
    (h4 : (Zpow 2 (tl - 1)) ≤ (2 ^ (8 : Nat))) :
    ((tl - 1) + 1) = tl := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_createdctx.v (replace)
example (A : Int) (h1 : ((A + 95992) ≤ 2147446784 ∨ 17594333495296 ≤ A)) :
    (A + 30152) = (((A + 30096) + ((32 : Nat) : Int)) + ((24 : Nat) : Int)) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_getfh_b.v (assert)
example
    {list_Z T2 T3 : Type}
    (SPV : Int)
    (SPA : Int)
    (ZFH : Int)
    (SRC : Int)
    (src : list_Z)
    (off : Int)
    (size : Int)
    (lo : Int)
    (ws0 : Int)
    (fhd_fcsID : T2 → Int)
    (fhd : T2)
    (zlen : list_Z → Int)
    (ATOP : Int)
    (fhd_singleSegment : T2 → Int)
    (wl_windowSize : T3 → Int)
    (Znth : Int → list_Z → T3)
    (p : Int)
    (fcs_fieldSize : Int → Int)
    (fhd_extra : T3 → Int)
    (h1 : 0 ≤ off)
    (h2 : 5 ≤ size)
    (h3 : (off + size) ≤ (zlen src))
    (h4 : (ZFH % 8) = 0)
    (h5 : ((ATOP + 4096) ≤ lo ∧ (lo ≤ (SPA - 2208) ∧ (((SPV - 144) ≤ SPA ∧ SPA ≤ (SPV - 128)) ∧ ((SPA % 32) = 0 ∧ ((SPV + 16) < (2 ^ (47 : Nat)) ∧ (SPV % 16) = 0))))))
    (h6 : ((fhd_singleSegment fhd) = 0 → ws0 = (wl_windowSize (Znth (off + 5) src))))
    (h7 : (0 ≤ ws0 ∧ ws0 < 18446744073709551616))
    (h8 : (6459392 ≤ SRC ∧ ((SRC + (zlen src)) + 8) ≤ (2 ^ (47 : Nat))))
    (h9 : ((5 ≤ p ∧ p ≤ 10) ∧ (((off + p) + (fcs_fieldSize (fhd_fcsID fhd))) + (fhd_extra (Znth (off + 4) src))) ≤ (off + size)))
    (h10 : (fhd_fcsID fhd) = 3)
    (h11 : (fcs_fieldSize (fhd_fcsID fhd)) = 8)
    (h12 : (0 ≤ (off + p) ∧ (((off + p) + 8) ≤ (zlen src) ∧ 0 ≤ SRC)))
    (h13 : (fhd_fcsID fhd) = 2)
    (h14 : (fcs_fieldSize (fhd_fcsID fhd)) = 4)
    (h15 : (0 ≤ (off + p) ∧ (((off + p) + 4) ≤ (zlen src) ∧ 0 ≤ SRC))) :
    (fhd_fcsID fhd) = 1 := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_hft_bdt_p2c.v (replace)
example
    {list_Z : Type}
    (maxSV : Int)
    (tl : Int)
    (norm : list_Z)
    (j : Int)
    (hhigh : list_Z → Int → Int → Int)
    (Zpow : Int → Int → Int)
    (fse_tablestep : Int → Int)
    (h1 : (hhigh norm maxSV tl) = ((Zpow 2 tl) - 1))
    (h2 : (0 ≤ (fse_tablestep (Zpow 2 tl)) ∧ (fse_tablestep (Zpow 2 tl)) < 1048576))
    (h3 : (0 ≤ (Int.fmod (j * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) ∧ (Int.fmod (j * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) < (Zpow 2 tl)))
    (h4 : (0 ≤ (Int.fmod ((j + 1) * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) ∧ (Int.fmod ((j + 1) * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) < (Zpow 2 tl)))
    (h5 : (0 ≤ (Int.fmod ((j + 2) * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) ∧ (Int.fmod ((j + 2) * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) < (Zpow 2 tl)))
    (h6 : (Int.fmod ((Int.fmod (j * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) + (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) = (Int.fmod ((j + 1) * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)))
    (h7 : (Int.fmod ((Int.fmod (j * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl)) + (2 * (fse_tablestep (Zpow 2 tl)))) (Zpow 2 tl)) = (Int.fmod ((j + 2) * (fse_tablestep (Zpow 2 tl))) (Zpow 2 tl))) :
    (j + 2) = ((j + 1) + 1) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_hft_fdec_call.v (replace)
example (FF : Int) (h1 : (FF % 64) = 0) (h2 : 0 ≤ FF) (h3 : (FF + 64) ≤ (2 ^ (47 : Nat))) :
    (((((FF / 8) + 2147450880) + 4) + 1) + 1) = (2147450880 + ((FF / 8) + 6)) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_hft_fdec_defs.v (replace)
example (tl : Int) (st : Int) (Zpow : Int → Int → Int) (h1 : (0 ≤ st ∧ st < (Zpow 2 tl))) :
    (((4 * st) + 2) + 1) = ((4 * st) + 3) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_hft_x2_facts2.v (replace)
example
    {list_Z : Type}
    (hw : list_Z)
    (rank : list_Z)
    (tl : Int)
    (maxW : Int)
    (w : Int)
    (len : Int)
    (minW : Int)
    (AZ_hft_x2_defs_TT : Int → Int)
    (zlen : list_Z → Int)
    (Zpow : Int → Int → Int)
    (h1 : (zlen hw) = 256)
    (h2 : (zlen rank) = 13)
    (h3 : (1 ≤ maxW ∧ maxW ≤ tl))
    (h4 : (1 ≤ w ∧ w ≤ maxW))
    (h5 : ((tl - maxW) + 1) ≤ ((AZ_hft_x2_defs_TT tl) - ((tl + 1) - w)))
    (h6 : len = (Zpow 2 ((AZ_hft_x2_defs_TT tl) - ((tl + 1) - w))))
    (h7 : minW = (max 1 (((tl + 1) - w) + ((tl + 1) - (AZ_hft_x2_defs_TT tl)))))
    (h8 : (2 ≤ len ∧ len ≤ 2048)) :
    ((AZ_hft_x2_defs_TT tl) - ((tl + 1) - w)) = ((AZ_hft_x2_defs_TT tl) - ((tl + 1) - w)) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_hft_x2_k4.v (replace)
example (st : Int) (i : Int) (len : Int) (h1 : (i + 8) ≤ len) :
    ((st + i) + 8) = (st + (i + 8)) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_hft_x2_s2.v (replace)
example
    {list_Z : Type}
    (WK : Int)
    (hw : list_Z)
    (rank : list_Z)
    (tl : Int)
    (maxW : Int)
    (w : Int)
    (zlen : list_Z → Int)
    (Znth : Int → list_Z → Int)
    (AZ_hft_x2_defs_TT : Int → Int)
    (Zpow : Int → Int → Int)
    (h1 : (zlen hw) = 256)
    (h2 : (zlen rank) = 13)
    (h3 : (1 ≤ maxW ∧ maxW ≤ tl))
    (h4 : (0 ≤ ((Znth w rank) * (Zpow 2 ((((AZ_hft_x2_defs_TT tl) - tl) + w) - 1))) ∧ ((Znth w rank) * (Zpow 2 ((((AZ_hft_x2_defs_TT tl) - tl) + w) - 1))) ≤ 4096)) :
    (4 * w) = (((WK + (4 * w)) + 0) - WK) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_huf_dx41_e.v (replace)
example
    {T1 T2 : Type}
    (SPV : Int)
    (SRC : Int)
    (n : Int)
    (DT : Int)
    (DST : Int)
    (dcap : Int)
    (firstn : Int → T1 → T2)
    (dtb : T1)
    (zlen : T2 → Int)
    (lo : Int)
    (h1 : ((((SPV - 480) + 480) ≤ SRC ∨ (SRC + n) ≤ (SPV - 480)) ∧ (((SPV - 480) + 480) ≤ DT ∨ (DT + 16388) ≤ (SPV - 480))))
    (h2 : ((1 ≤ n ∧ n ≤ 4294967296) ∧ (4096 ≤ (DST + dcap) ∧ (DST + dcap) ≤ 140737488355328)))
    (h3 : (zlen (firstn 4 dtb)) = 4)
    (h4 : ((SPV + (-376)) % 8) = 0)
    (h5 : (4096 ≤ lo ∧ (lo ≤ ((SPV + (-480)) - 48) ∧ ((SPV + (-480)) < (2 ^ (47 : Nat)) ∧ (4096 ≤ (SPV + (-376)) ∧ (((SPV + (-376)) + 152) < (2 ^ (47 : Nat)) ∧ ((((SPV + (-376)) + 152) ≤ lo ∨ (SPV + (-480)) ≤ (SPV + (-376))) ∧ (4096 ≤ SRC ∧ ((SRC + n) < (2 ^ (47 : Nat)) ∧ (((SRC + n) ≤ lo ∨ (SPV + (-480)) ≤ SRC) ∧ (n < (2 ^ (32 : Nat)) ∧ (4096 ≤ DT ∧ ((DT + 4) < (2 ^ (47 : Nat)) ∧ (((DT + 4) ≤ lo ∨ (SPV + (-480)) ≤ DT) ∧ (4096 ≤ DST ∧ ((0 ≤ dcap ∧ dcap < (2 ^ (32 : Nat))) ∧ ((DST + dcap) < (2 ^ (47 : Nat)) ∧ ((((SPV + (-376)) + 152) ≤ SRC ∨ (SRC + n) ≤ (SPV + (-376))) ∧ (((SPV + (-376)) + 152) ≤ DT ∨ (DT + 4) ≤ (SPV + (-376))))))))))))))))))))) :
    (SPV + (-336)) = ((SPV + (-376)) + 40) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_huf_dx41_fik.v (replace)
example
    {T1 : Type}
    (DT : Int)
    (dtb : T1)
    (A : Int)
    (X : Int)
    (zlen : T1 → Int)
    (length : T1 → Nat)
    (h1 : (zlen dtb) = 16388)
    (h2 : (((A - DT) - 4) % 2) = 0)
    (h3 : (0 ≤ ((A - DT) - 4) ∧ ((A - DT) - 4) < 4096))
    (h4 : (A = (DT + (4 + (2 * X))) ∧ (0 ≤ X ∧ X < 2048)))
    (h5 : (Int.toNat ((2 * X) + 4)) < (length dtb)) :
    (Int.toNat ((2 * X) + 4)) = (Int.toNat (4 + (2 * X))) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_huf_dx41_n0.v (replace)
example
    (SPV : Int)
    (DT : Int)
    (DST : Int)
    (dcap : Int)
    (h1 : ((4100 ≤ (DT + 4) ∧ (DT + 4) ≤ 140737488338944) ∧ ((4096 ≤ (DST + dcap) ∧ (DST + dcap) ≤ 140737488355328) ∧ (((SPV - 480) + 480) ≤ DT ∨ (DT + 16388) ≤ (SPV - 480))))) :
    (SPV + (-144)) = ((SPV + (-480)) + 336) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_huf_dx42_i4.v (replace)
example
    (S4 : Int)
    (bitd_ptr : Int → Int → Int)
    (n4 : Int)
    (SPV : Int)
    (tot : Int)
    (S3 : Int)
    (n3 : Int)
    (S2 : Int)
    (n2 : Int)
    (S1 : Int)
    (n1 : Int)
    (lo : Int)
    (h1 : ((0 ≤ n4 ∧ n4 ≤ 4294967296) ∧ ((4096 ≤ S4 ∧ S4 ≤ 140737488355328) ∧ ((0 ≤ tot ∧ tot ≤ 4294967296) ∧ ((4096 ≤ S3 ∧ S3 ≤ 140737488355328) ∧ ((0 ≤ n3 ∧ n3 ≤ 4294967296) ∧ ((4096 ≤ S2 ∧ S2 ≤ 140737488355328) ∧ ((0 ≤ n2 ∧ n2 ≤ 4294967296) ∧ ((4096 ≤ S1 ∧ S1 ≤ 140737488355328) ∧ (0 ≤ n1 ∧ n1 ≤ 4294967296))))))))))
    (h2 : ((SPV + (-264)) % 8) = 0)
    (h3 : (4096 ≤ (SPV + (-264)) ∧ (((SPV + (-264)) + 40) < (2 ^ (47 : Nat)) ∧ (4096 ≤ S4 ∧ ((S4 + n4) < (2 ^ (47 : Nat)) ∧ (n4 < (2 ^ (32 : Nat)) ∧ ((((SPV + (-264)) + 40) ≤ S4 ∨ (S4 + n4) ≤ (SPV + (-264))) ∧ (lo ≤ ((SPV + (-384)) - 2224) ∧ ((SPV + (-384)) < (2 ^ (47 : Nat)) ∧ ((((SPV + (-264)) + 40) ≤ lo ∨ (SPV + (-384)) ≤ (SPV + (-264))) ∧ ((S4 + n4) ≤ lo ∨ (SPV + (-384)) ≤ S4))))))))))) :
    (S4 + ((bitd_ptr S4 n4) - S4)) = (bitd_ptr S4 n4) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_prod.v (replace)
example
    {list_Z T2 : Type}
    (SP : Int)
    (P : Int)
    (D : Int)
    (pl : list_Z)
    (size : Int)
    (lo : Int)
    (result : Int)
    (zlen : list_Z → Int)
    (map : T2 → list_Z → list_Z)
    (Z_to_bv : Int → T2)
    (h1 : (0 ≤ size ∧ size ≤ (zlen pl)))
    (h2 : 0 < P)
    (h3 : (P % 8) = 0)
    (h4 : 0 < D)
    (h5 : lo ≤ (SP - 16))
    (h6 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h7 : SP < (2 ^ (47 : Nat)))
    (h8 : (P + 16) ≤ lo)
    (h9 : (D + (zlen pl)) ≤ lo)
    (h10 : ((D + (zlen pl)) ≤ P ∨ (P + 16) ≤ D))
    (h11 : (zlen (map (Z_to_bv 8) pl)) = (zlen pl))
    (h12 : ((P + 16) ≤ 2147446784 ∨ 17594333495296 ≤ P)) :
    ((((result * 256) - 2147483648) - 2147483648) + (1 * 18446744073709551616)) = ((result * 256) + 18446744069414584320) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_prod.v (replace)
example (sz : Int) (h1 : sz = 0) (h2 : 0 < sz) :
    ((sz - 1) + (-1)) = (sz + (-2)) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_xxh_update.v (replace)
example {T1 : Type} (zlen : T1 → Int) (inb : T1) (p : Int) :
    ((zlen inb) - p) = ((zlen inb) + ((-1) * p)) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_xxh_update.v (replace)
example (S8 : Int) :
    (((8 * S8) + 40) + 0) = ((8 * S8) + 40) := by
  lia

-- zstd/simple_decompress: lib/BothW/AZ_xxh_update.v (replace)
example
    (S8 : Int)
    (h1 : 6459392 ≤ (8 * S8))
    (h2 : (((8 * S8) + 88) ≤ 2147446784 ∨ 17594333495296 ≤ (8 * S8))) :
    ((8 * S8) + 40) = ((8 * S8) + ((40 : Nat) : Int)) := by
  lia

-- zstd/simple_decompress: lib/Plain/F_memmove.v (replace)
example
    {word : Type}
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (bv_unsigned : word → Int)
    (h1 : (((bv_unsigned a1) + (bv_unsigned a2)) ≤ (2 ^ (63 : Nat)) ∧ ((bv_unsigned a0) + (bv_unsigned a2)) ≤ (2 ^ (63 : Nat))))
    (h2 : (((bv_unsigned a1) + (bv_unsigned a2)) ≤ (bv_unsigned a0) ∨ ((bv_unsigned a0) + (bv_unsigned a2)) ≤ (bv_unsigned a1))) :
    (bv_unsigned a2) = (((bv_unsigned a1) + (bv_unsigned a2)) - (bv_unsigned a1)) := by
  lia

-- zstd/simple_decompress: lib/Plain/F_printf_core_dloop.v (replace)
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
    (j : Int)
    (zlength : list_Z → Int)
    (W' : list_Z)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (x : Int)
    (dec_digits : Int → list_Z)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 196608)
    (h5 : ((200000 ≤ Fp ∧ (Fp + 232) ≤ 402216) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((402224 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (x / 10) < 1844674407370955162)
    (h12 : 2 ≤ (zlength (dec_digits x))) :
    (Int.toNat (j - ((zlength W') + 1))) = (Int.toNat ((j - 1) - (zlength W'))) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_bfse_c.v (replace)
example
    {T1 T2 : Type}
    (Znth : T1 → T2 → Int)
    (s : T1)
    (norm : T2)
    (tl : Int)
    (Zpow : Int → Int → Int)
    (high : Int)
    (h1 : ((-1) ≤ (Znth s norm) ∧ (Znth s norm) ≤ (Zpow 2 tl)))
    (h2 : (Znth s norm) ≤ 0)
    (h3 : 0 < (Znth s norm))
    (h4 : (Znth s norm) = (-1))
    (h5 : (0 ≤ high ∧ high < (Zpow 2 tl))) :
    (Int.toNat (Znth s norm)) = ((Int.toNat ((Znth s norm) - 1)) + 1) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_bfse_p1.v (replace)
example
    {T1 T2 T3 : Type}
    (NC : Int)
    (s : Int)
    (Znth : Int → T1 → Int)
    (norm : T1)
    (tl : Int)
    (Zpow : Int → Int → Int)
    (zlenF : T2 → Int)
    (upd_nat : Nat → Int → T3 → T2)
    (symNext : T3)
    (h1 : ((-1) ≤ (Znth s norm) ∧ (Znth s norm) ≤ (Zpow 2 tl)))
    (h2 : 0 ≤ (Znth s norm))
    (h3 : (16 ≤ (Zpow 2 (tl + (-1))) ∧ (Zpow 2 (tl + (-1))) ≤ 256))
    (h4 : (2 ^ (4 : Nat)) ≤ (Zpow 2 (tl + (-1))))
    (h5 : (Zpow 2 (tl + (-1))) ≤ (2 ^ (8 : Nat)))
    (h6 : (zlenF (upd_nat (Int.toNat s) (Int.fmod (Znth s norm) (2 ^ (16 : Nat))) symNext)) = 53) :
    (NC + (2 * (s + 1))) = ((NC + (2 * s)) + 2) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_dmf_a.v (replace)
example
    {list_Z : Type}
    (SP : Int)
    (lo : Int)
    (DCTX : Int)
    (DST : Int)
    (CAP : Int)
    (SRC : Int)
    (src : list_Z)
    (size : Int)
    (sz : Int)
    (tot : Int)
    (zlen : list_Z → Int)
    (h1 : 4096 ≤ DCTX)
    (h2 : (DCTX + 95992) < (2 ^ (47 : Nat)))
    (h3 : (DCTX % 8) = 0)
    (h4 : 0 ≤ size)
    (h5 : size ≤ (zlen src))
    (h6 : size < 1099511627776)
    (h7 : 4096 ≤ SRC)
    (h8 : (SRC + (zlen src)) < (2 ^ (47 : Nat)))
    (h9 : 0 ≤ CAP)
    (h10 : CAP < 1099511627776)
    (h11 : (DST = 0 → CAP = 0))
    (h12 : (DST ≠ 0 → 4096 ≤ DST))
    (h13 : (DST + CAP) < (2 ^ (47 : Nat)))
    (h14 : 4096 ≤ lo)
    (h15 : lo ≤ (SP - 2368))
    (h16 : SP < (2 ^ (47 : Nat)))
    (h17 : ((DCTX + 95992) ≤ lo ∨ SP ≤ DCTX))
    (h18 : ((DST + CAP) ≤ lo ∨ SP ≤ DST))
    (h19 : ((SRC + (zlen src)) ≤ lo ∨ SP ≤ SRC))
    (h20 : ((199936 + 16) ≤ lo ∨ SP ≤ 199936))
    (h21 : ((DST + CAP) ≤ DCTX ∨ (DCTX + 95992) ≤ DST))
    (h22 : ((DST + CAP) ≤ SRC ∨ (SRC + (zlen src)) ≤ DST))
    (h23 : ((SRC + (zlen src)) ≤ DCTX ∨ (DCTX + 95992) ≤ SRC))
    (h24 : ((199936 + 16) ≤ DCTX ∨ (DCTX + 95992) ≤ 199936))
    (h25 : ((199936 + 16) ≤ DST ∨ (DST + CAP) ≤ 199936))
    (h26 : (0 ≤ sz ∧ sz < (2 ^ (64 : Nat))))
    (h27 : (0 ≤ tot ∧ tot ≤ CAP)) :
    tot = ((DST + tot) - DST) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_dmf_c.v (replace)
example
    {list_Z : Type}
    (SP : Int)
    (lo : Int)
    (DCTX : Int)
    (DST : Int)
    (CAP : Int)
    (SRC : Int)
    (src : list_Z)
    (size : Int)
    (tot : Int)
    (o : Int)
    (v : Int)
    (zlen : list_Z → Int)
    (h1 : 4096 ≤ DCTX)
    (h2 : (DCTX + 95992) < (2 ^ (47 : Nat)))
    (h3 : (DCTX % 8) = 0)
    (h4 : 0 ≤ size)
    (h5 : size ≤ (zlen src))
    (h6 : size < 1099511627776)
    (h7 : 4096 ≤ SRC)
    (h8 : (SRC + (zlen src)) < (2 ^ (47 : Nat)))
    (h9 : 0 ≤ CAP)
    (h10 : CAP < 1099511627776)
    (h11 : (DST + CAP) < (2 ^ (47 : Nat)))
    (h12 : 4096 ≤ lo)
    (h13 : lo ≤ (SP - 2368))
    (h14 : SP < (2 ^ (47 : Nat)))
    (h15 : v ≤ ((CAP - tot) - o)) :
    ((DST + tot) + (o + v)) = (((DST + tot) + o) + v) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_finddsize.v (replace)
example
    {list_Z : Type}
    (SP : Int)
    (SRC : Int)
    (src : list_Z)
    (size0 : Int)
    (lo : Int)
    (zlen : list_Z → Int)
    (h1 : 0 ≤ size0)
    (h2 : size0 < 1099511627776)
    (h3 : size0 ≤ (zlen src))
    (h4 : 0 < SRC)
    (h5 : (SRC + (zlen src)) < (2 ^ (64 : Nat)))
    (h6 : lo ≤ (SP - 320))
    (h7 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h8 : ((SRC + (zlen src)) ≤ lo ∨ SP ≤ SRC)) :
    (SP + (-88)) = ((SP + (-136)) + ((48 : Nat) : Int)) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_findfsi.v (replace)
example (SRC : Int) (ip : Int) (cbs : Int) :
    (SRC + (ip + (3 + cbs))) = ((SRC + ip) + (cbs + 3)) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_findfsi.v (replace)
example (rem : Int) (cbs : Int) :
    (rem - (3 + cbs)) = (rem - (cbs + 3)) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_getfh.v (assert)
example
    {list_Z T2 : Type}
    (SP : Int)
    (ZFH : Int)
    (SRC : Int)
    (src : list_Z)
    (off : Int)
    (size : Int)
    (lo : Int)
    (ws0 : Int)
    (fhd_fcsID : Int → Int)
    (fhd : Int)
    (zlen : list_Z → Int)
    (fhd_singleSegment : Int → Int)
    (wl_windowSize : T2 → Int)
    (Znth : Int → list_Z → T2)
    (fcs_fieldSize : Int → Int)
    (h1 : 0 ≤ off)
    (h2 : 5 ≤ size)
    (h3 : (off + size) ≤ (zlen src))
    (h4 : 0 < SRC)
    (h5 : lo ≤ (SP - 48))
    (h6 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h7 : ((ZFH + 48) ≤ lo ∨ SP ≤ ZFH))
    (h8 : ((SRC + (zlen src)) ≤ lo ∨ SP ≤ SRC))
    (h9 : ((ZFH + 48) ≤ SRC ∨ (SRC + (zlen src)) ≤ ZFH))
    (h10 : ((fhd_singleSegment fhd) = 0 → ws0 = (wl_windowSize (Znth (off + 5) src))))
    (h11 : (0 ≤ ws0 ∧ ws0 < 18446744073709551616))
    (h12 : (fhd_fcsID fhd) = 3)
    (h13 : (fcs_fieldSize (fhd_fcsID fhd)) = 8)
    (h14 : (fhd_fcsID fhd) = 2)
    (h15 : (fcs_fieldSize (fhd_fcsID fhd)) = 4) :
    (fhd_fcsID fhd) = 1 := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_getfh.v (assert)
example
    {list_Z T2 T3 : Type}
    (SP : Int)
    (ZFH : Int)
    (SRC : Int)
    (src : list_Z)
    (off : Int)
    (size : Int)
    (lo : Int)
    (ws0 : Int)
    (fhd_dictIDSizeCode : T2 → Int)
    (fhd : T2)
    (zlen : list_Z → Int)
    (fhd_singleSegment : T2 → Int)
    (wl_windowSize : T3 → Int)
    (Znth : Int → list_Z → T3)
    (did_fieldSize : Int → Int)
    (h1 : 0 ≤ off)
    (h2 : 5 ≤ size)
    (h3 : (off + size) ≤ (zlen src))
    (h4 : 0 < SRC)
    (h5 : lo ≤ (SP - 48))
    (h6 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h7 : ((ZFH + 48) ≤ lo ∨ SP ≤ ZFH))
    (h8 : ((SRC + (zlen src)) ≤ lo ∨ SP ≤ SRC))
    (h9 : ((ZFH + 48) ≤ SRC ∨ (SRC + (zlen src)) ≤ ZFH))
    (h10 : ((fhd_singleSegment fhd) = 0 → ws0 = (wl_windowSize (Znth (off + 5) src))))
    (h11 : (0 ≤ ws0 ∧ ws0 < 18446744073709551616))
    (h12 : (fhd_dictIDSizeCode fhd) = 3)
    (h13 : (did_fieldSize (fhd_dictIDSizeCode fhd)) = 4)
    (h14 : (fhd_dictIDSizeCode fhd) = 2)
    (h15 : (did_fieldSize (fhd_dictIDSizeCode fhd)) = 2) :
    (fhd_dictIDSizeCode fhd) = 0 := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_getfh.v (assert)
example
    {list_Z T2 T3 : Type}
    (SP : Int)
    (ZFH : Int)
    (SRC : Int)
    (src : list_Z)
    (off : Int)
    (size : Int)
    (lo : Int)
    (ws0 : Int)
    (fhd_dictIDSizeCode : T2 → Int)
    (fhd : T2)
    (zlen : list_Z → Int)
    (fhd_singleSegment : T2 → Int)
    (wl_windowSize : T3 → Int)
    (Znth : Int → list_Z → T3)
    (did_fieldSize : Int → Int)
    (h1 : 0 ≤ off)
    (h2 : 5 ≤ size)
    (h3 : (off + size) ≤ (zlen src))
    (h4 : 0 < SRC)
    (h5 : lo ≤ (SP - 48))
    (h6 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h7 : ((ZFH + 48) ≤ lo ∨ SP ≤ ZFH))
    (h8 : ((SRC + (zlen src)) ≤ lo ∨ SP ≤ SRC))
    (h9 : ((ZFH + 48) ≤ SRC ∨ (SRC + (zlen src)) ≤ ZFH))
    (h10 : ((fhd_singleSegment fhd) = 0 → ws0 = (wl_windowSize (Znth (off + 5) src))))
    (h11 : (0 ≤ ws0 ∧ ws0 < 18446744073709551616))
    (h12 : (fhd_dictIDSizeCode fhd) = 3)
    (h13 : (did_fieldSize (fhd_dictIDSizeCode fhd)) = 4)
    (h14 : (fhd_dictIDSizeCode fhd) = 2)
    (h15 : (did_fieldSize (fhd_dictIDSizeCode fhd)) = 2)
    (h16 : (fhd_dictIDSizeCode fhd) = 0)
    (h17 : (did_fieldSize (fhd_dictIDSizeCode fhd)) = 0) :
    (fhd_dictIDSizeCode fhd) = 1 := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_hft_bdt_p1.v (replace)
example
    {list_Z T2 T3 T4 : Type}
    (W : Int)
    (maxSV : Int)
    (tl : Int)
    (norm : list_Z)
    (s : Int)
    (Znth : Int → list_Z → Int)
    (Zpow : Int → Int → Int)
    (length : T2 → Nat)
    (upd_nat : Nat → Int → T3 → T2)
    (sn : T3)
    (Zupd : Nat → Int → T4 → T2)
    (high : Nat)
    (tb : T4)
    (h1 : ((-1) ≤ (Znth s norm) ∧ (Znth s norm) ≤ (Zpow 2 tl)))
    (h2 : 0 ≤ (Znth s norm))
    (h3 : (((length (upd_nat (Int.toNat s) (Znth s norm) sn)) : Nat) : Int) = (maxSV + 1))
    (h4 : (Znth s norm) = (-1))
    (h5 : (((length (Zupd ((4 * high) + 2) s tb)) : Nat) : Int) = (4 * (Zpow 2 tl))) :
    (W + (2 * (s + 1))) = ((W + (2 * s)) + 2) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_hft_bdt_p1.v (replace)
example
    {list_Z T2 T3 T4 : Type}
    (maxSV : Int)
    (tl : Int)
    (norm : list_Z)
    (s : Int)
    (Znth : Int → list_Z → Int)
    (Zpow : Int → Int → Int)
    (length : T2 → Nat)
    (upd_nat : Nat → Int → T3 → T2)
    (sn : T3)
    (Zupd : Nat → Int → T4 → T2)
    (high : Nat)
    (tb : T4)
    (h1 : ((-1) ≤ (Znth s norm) ∧ (Znth s norm) ≤ (Zpow 2 tl)))
    (h2 : 0 ≤ (Znth s norm))
    (h3 : (((length (upd_nat (Int.toNat s) (Znth s norm) sn)) : Nat) : Int) = (maxSV + 1))
    (h4 : (Znth s norm) = (-1))
    (h5 : (((length (Zupd ((4 * high) + 2) s tb)) : Nat) : Int) = (4 * (Zpow 2 tl))) :
    (maxSV + 1) = (s + 1) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_hft_fdec.v (replace)
example
    {list_byte : Type}
    (SPV : Int)
    (lo : Int)
    (DST : Int)
    (cap : Int)
    (SRC : Int)
    (n : Int)
    (WK : Int)
    (wksz : Int)
    (src : list_byte)
    (hn : Int)
    (length : list_byte → Nat)
    (out : list_byte)
    (jn : list_byte)
    (buf : list_byte)
    (tl : Int)
    (Zpow : Int → Int → Int)
    (msv : Int)
    (need0 : Int)
    (h1 : 4096 ≤ lo)
    (h2 : lo ≤ (SPV - 384))
    (h3 : SPV < (2 ^ (47 : Nat)))
    (h4 : 4096 ≤ DST)
    (h5 : (0 ≤ cap ∧ cap ≤ 65536))
    (h6 : (DST + cap) < (2 ^ (47 : Nat)))
    (h7 : (((length src) : Nat) : Int) = n)
    (h8 : 4096 ≤ SRC)
    (h9 : n ≤ 65536)
    (h10 : (SRC + n) < (2 ^ (47 : Nat)))
    (h11 : 4096 ≤ WK)
    (h12 : (0 ≤ wksz ∧ wksz < (2 ^ (32 : Nat))))
    (h13 : (WK + wksz) < (2 ^ (47 : Nat)))
    (h14 : ((DST + cap) ≤ lo ∨ SPV ≤ DST))
    (h15 : ((WK + wksz) ≤ lo ∨ SPV ≤ WK))
    (h16 : ((SRC + n) ≤ lo ∨ SPV ≤ SRC))
    (h17 : ((DST + cap) ≤ WK ∨ (WK + wksz) ≤ DST))
    (h18 : ((DST + cap) ≤ SRC ∨ (SRC + n) ≤ DST))
    (h19 : ((WK + wksz) ≤ SRC ∨ (SRC + n) ≤ WK))
    (h20 : (((length out) : Nat) : Int) = cap)
    (h21 : (length jn) = 512)
    (h22 : (((length buf) : Nat) : Int) = n)
    (h23 : (32 ≤ (Zpow 2 tl) ∧ (Zpow 2 tl) ≤ 512))
    (h24 : ((((5 * (Zpow 2 tl)) + (2 * (msv + 1))) + 16) ≤ need0 ∧ need0 ≤ (((5 * (Zpow 2 tl)) + (2 * (msv + 1))) + 19)))
    (h25 : (1 ≤ hn ∧ hn ≤ n)) :
    (SRC + hn) = (SRC + (((min (Int.toNat hn) (length src)) : Nat) : Int)) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_hft_fdec.v (replace)
example
    {list_byte : Type}
    (SPV : Int)
    (lo : Int)
    (DST : Int)
    (cap : Int)
    (SRC : Int)
    (n : Int)
    (WK : Int)
    (wksz : Int)
    (src : list_byte)
    (length : list_byte → Nat)
    (out : list_byte)
    (jn : list_byte)
    (buf : list_byte)
    (tl : Int)
    (Zpow : Int → Int → Int)
    (msv : Int)
    (need0 : Int)
    (hn : Int)
    (skipn : Nat → list_byte → list_byte)
    (h1 : 4096 ≤ lo)
    (h2 : lo ≤ (SPV - 384))
    (h3 : SPV < (2 ^ (47 : Nat)))
    (h4 : 4096 ≤ DST)
    (h5 : (0 ≤ cap ∧ cap ≤ 65536))
    (h6 : (DST + cap) < (2 ^ (47 : Nat)))
    (h7 : (((length src) : Nat) : Int) = n)
    (h8 : 4096 ≤ SRC)
    (h9 : n ≤ 65536)
    (h10 : (SRC + n) < (2 ^ (47 : Nat)))
    (h11 : 4096 ≤ WK)
    (h12 : (0 ≤ wksz ∧ wksz < (2 ^ (32 : Nat))))
    (h13 : (WK + wksz) < (2 ^ (47 : Nat)))
    (h14 : ((DST + cap) ≤ lo ∨ SPV ≤ DST))
    (h15 : ((WK + wksz) ≤ lo ∨ SPV ≤ WK))
    (h16 : ((SRC + n) ≤ lo ∨ SPV ≤ SRC))
    (h17 : ((DST + cap) ≤ WK ∨ (WK + wksz) ≤ DST))
    (h18 : ((DST + cap) ≤ SRC ∨ (SRC + n) ≤ DST))
    (h19 : ((WK + wksz) ≤ SRC ∨ (SRC + n) ≤ WK))
    (h20 : (((length out) : Nat) : Int) = cap)
    (h21 : (length jn) = 512)
    (h22 : (((length buf) : Nat) : Int) = n)
    (h23 : (32 ≤ (Zpow 2 tl) ∧ (Zpow 2 tl) ≤ 512))
    (h24 : ((((5 * (Zpow 2 tl)) + (2 * (msv + 1))) + 16) ≤ need0 ∧ need0 ≤ (((5 * (Zpow 2 tl)) + (2 * (msv + 1))) + 19)))
    (h25 : (1 ≤ hn ∧ hn ≤ n))
    (h26 : (((length (skipn (Int.toNat hn) src)) : Nat) : Int) = (n - hn)) :
    (SPV + (-152)) = ((SPV + (-160)) + ((8 : Nat) : Int)) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_hft_x1.v (replace)
example
    {list_byte : Type}
    (SPV : Int)
    (SRC : Int)
    (n : Int)
    (DT : Int)
    (WK : Int)
    (wksz : Int)
    (lo : Int)
    (src : list_byte)
    (nbs : Int)
    (tl0 : Int)
    (sc : Int)
    (s : Int)
    (HUF_TBL_STACK : Int)
    (length : list_byte → Nat)
    (HUF_DTABLE_BYTES : Int)
    (cur : list_byte)
    (cur' : list_byte)
    (h1 : 4096 ≤ lo)
    (h2 : lo ≤ (SPV - HUF_TBL_STACK))
    (h3 : SPV < (2 ^ (47 : Nat)))
    (h4 : (((length src) : Nat) : Int) = n)
    (h5 : 4096 ≤ SRC)
    (h6 : n < (2 ^ (32 : Nat)))
    (h7 : (SRC + n) < (2 ^ (47 : Nat)))
    (h8 : 4096 ≤ DT)
    (h9 : (DT + HUF_DTABLE_BYTES) < (2 ^ (47 : Nat)))
    (h10 : (DT % 4) = 0)
    (h11 : 4096 ≤ WK)
    (h12 : (0 ≤ wksz ∧ wksz < (2 ^ (32 : Nat))))
    (h13 : (WK + wksz) < (2 ^ (47 : Nat)))
    (h14 : (WK % 4) = 0)
    (h15 : ((DT + HUF_DTABLE_BYTES) ≤ lo ∨ SPV ≤ DT))
    (h16 : ((WK + wksz) ≤ lo ∨ SPV ≤ WK))
    (h17 : ((SRC + n) ≤ lo ∨ SPV ≤ SRC))
    (h18 : ((DT + HUF_DTABLE_BYTES) ≤ WK ∨ (WK + wksz) ≤ DT))
    (h19 : ((DT + HUF_DTABLE_BYTES) ≤ SRC ∨ (SRC + n) ≤ DT))
    (h20 : ((WK + wksz) ≤ SRC ∨ (SRC + n) ≤ WK))
    (h21 : (2 ≤ nbs ∧ nbs ≤ 256))
    (h22 : 0 < sc)
    (h23 : (tl0 + sc) = 11)
    (h24 : 1 ≤ tl0)
    (h25 : 1492 ≤ wksz)
    (h26 : (((length cur) : Nat) : Int) = 13)
    (h27 : (((length cur') : Nat) : Int) = 13)
    (h28 : (s - 1) = sc) :
    sc = (s + (-1)) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_hft_x2_l1.v (replace)
example
    {T1 : Type}
    (off : Int)
    (q : Int)
    (b4 : Int)
    (pos : Int)
    (cw' : T1)
    (length : T1 → Nat)
    (h1 : (b4 / 2) = (2 * ((pos + off) + (8 * q))))
    (h2 : (((length cw') : Nat) : Int) = 8192) :
    (off + (8 * (q + 1))) = ((off + (8 * q)) + 8) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_hft_x2_l2.v (replace)
example
    {T1 : Type}
    (s : Int)
    (tb : Int)
    (bsym : Int)
    (cw' : T1)
    (length : T1 → Nat)
    (h1 : (0 ≤ (((tb * 65536) + bsym) + 33554432) ∧ (((tb * 65536) + bsym) + 33554432) < 4294967296))
    (h2 : ((((tb * 65536) + bsym) + 33554432) / 65536) = (tb + 512))
    (h3 : (((length cw') : Nat) : Int) = 8192) :
    (8 * (s + 1)) = ((8 * s) + 8) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_huf_dx1.v (replace)
example (dcap : Int) (j : Int) :
    (dcap - (j + 1)) = ((((-1) * j) + dcap) + (-1)) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_huf_dx41r.v (replace)
example
    (SRC : Int)
    (PP : Int)
    (n : Int)
    (SPV : Int)
    (DST : Int)
    (dcap : Int)
    (DT : Int)
    (h1 : ((SRC + n) ≤ (SPV - 416) ∨ SPV ≤ SRC))
    (h2 : ((DST + dcap) ≤ (SPV - 416) ∨ SPV ≤ DST))
    (h3 : ((DT + 16388) ≤ (SPV - 416) ∨ SPV ≤ DT)) :
    (SRC + (PP - SRC)) = PP := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_offinfo.v (replace)
example {T1 : Type} (st_log : T1 → Int) (t : T1) (Zpow : Int → Int → Int) :
    (8 + (8 * (Zpow 2 (st_log t)))) = (8 * (1 + (Zpow 2 (st_log t)))) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_prod.v (replace)
example (v : Int) (h1 : (0 ≤ v ∧ v < 4294967296)) :
    (v + (4294967295 * 4294967296)) = (v + 18446744069414584320) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_prod.v (replace)
example
    {list_Z T2 : Type}
    (SP : Int)
    (P : Int)
    (D : Int)
    (pl : list_Z)
    (size : Int)
    (lo : Int)
    (result : Int)
    (zlen : list_Z → Int)
    (map : T2 → list_Z → list_Z)
    (Z_to_bv : Int → T2)
    (h1 : (0 ≤ size ∧ size ≤ (zlen pl)))
    (h2 : lo ≤ (SP - 16))
    (h3 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h4 : (P + 16) ≤ lo)
    (h5 : (D + (zlen pl)) ≤ lo)
    (h6 : ((D + (zlen pl)) ≤ P ∨ (P + 16) ≤ D))
    (h7 : (zlen (map (Z_to_bv 8) pl)) = (zlen pl)) :
    ((((result * 256) - 2147483648) - 2147483648) + (1 * 18446744073709551616)) = ((result * 256) + 18446744069414584320) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_seq_l_ient2b.v (replace)
example
    {slp T2 : Type}
    (P : slp)
    (DCTX : Int)
    (y_nbSeq : slp → Int)
    (y_LOC : slp → Int)
    (y_CAP : slp → Int)
    (SPV : Int)
    (lo : Int)
    (DST : Int)
    (CAP : Int)
    (LITP : Int)
    (LBE : Int)
    (nbSeq : Int)
    (zlen : T2 → Int)
    (sq : T2)
    (SEQ : Int)
    (B0 : Int)
    (B1 : Int)
    (LLT : Int)
    (OFT : Int)
    (MLT : Int)
    (LOC : Int)
    (h1 : (y_nbSeq P) ≠ 0)
    (h2 : ((y_LOC P) = 0 ∧ 1 ≤ (y_CAP P)))
    (h3 : ((816 ≤ SPV ∧ SPV < (2 ^ (47 : Nat))) ∧ ((0 ≤ lo ∧ lo ≤ (SPV - 816)) ∧ (4096 ≤ DCTX ∧ ((DCTX + 95992) < (2 ^ (47 : Nat)) ∧ ((4096 ≤ DST ∧ DST < (2 ^ (47 : Nat))) ∧ ((0 ≤ CAP ∧ CAP < (2 ^ (47 : Nat))) ∧ ((4096 ≤ (DST + CAP) ∧ (DST + CAP) < (2 ^ (47 : Nat))) ∧ ((4096 ≤ LITP ∧ LITP < (2 ^ (47 : Nat))) ∧ ((4096 ≤ LBE ∧ LBE < (2 ^ (47 : Nat))) ∧ ((1 ≤ nbSeq ∧ nbSeq ≤ 98047) ∧ ((0 ≤ (zlen sq) ∧ (zlen sq) < (2 ^ (47 : Nat))) ∧ (4096 ≤ SEQ ∧ SEQ < (2 ^ (47 : Nat)))))))))))))))
    (h4 : (SPV ≤ DCTX ∨ (DCTX + 95992) ≤ lo))
    (h5 : (SPV ≤ B0 ∨ B1 ≤ (SPV - 608)))
    (h6 : (SPV ≤ LITP ∨ (LBE + 32) ≤ (SPV - 608)))
    (h7 : (SPV ≤ SEQ ∨ (SEQ + (zlen sq)) ≤ (SPV - 608)))
    (h8 : (SPV ≤ LLT ∨ (LLT + 4104) ≤ (SPV - 608)))
    (h9 : (SPV ≤ OFT ∨ (OFT + 2056) ≤ (SPV - 608)))
    (h10 : (SPV ≤ MLT ∨ (MLT + 4104) ≤ (SPV - 608)))
    (h11 : (B1 ≤ DCTX ∨ (DCTX + 95992) ≤ B0))
    (h12 : ((SEQ + (zlen sq)) ≤ (DCTX + 26684) ∨ (DCTX + 95992) ≤ SEQ))
    (h13 : ((LLT + 4104) ≤ (DCTX + 26684) ∨ (DCTX + 95992) ≤ LLT))
    (h14 : ((OFT + 2056) ≤ (DCTX + 26684) ∨ (DCTX + 95992) ≤ OFT))
    (h15 : ((MLT + 4104) ≤ (DCTX + 26684) ∨ (DCTX + 95992) ≤ MLT))
    (h16 : (LOC ≠ 2 → ((LBE + 32) ≤ (DCTX + 26684) ∨ (DCTX + 30372) ≤ LITP))) :
    ((DCTX + 30372) + 65568) = (DCTX + 95940) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_seq_s_end.v (replace)
example
    (LEND : Int)
    (LP : Int)
    (SPV : Int)
    (OP : Int)
    (DST : Int)
    (OEND : Int)
    (h1 : ((544 ≤ SPV ∧ SPV < (2 ^ (47 : Nat))) ∧ ((4096 ≤ OP ∧ OP < (2 ^ (47 : Nat))) ∧ ((4096 ≤ DST ∧ DST < (2 ^ (47 : Nat))) ∧ ((4096 ≤ OEND ∧ OEND < (2 ^ (47 : Nat))) ∧ ((4096 ≤ LP ∧ LP < (2 ^ (47 : Nat))) ∧ ((4096 ≤ LEND ∧ LEND < (2 ^ (47 : Nat))) ∧ ((0 ≤ (LEND - LP) ∧ (LEND - LP) ≤ (2 ^ (47 : Nat))) ∧ (0 ≤ (OEND - OP) ∧ (OEND - OP) ≤ (2 ^ (47 : Nat))))))))))) :
    LEND = (LP + (((-1) * LP) + LEND)) := by
  lia

-- zstd/simple_decompress: lib/Plain/RZ_xxh_update.v (replace)
example
    {T1 : Type}
    (STA : Int)
    (zlen : T1 → Int)
    (inb : T1)
    (p : Int)
    (h1 : (zlen inb) = (zlen inb)) :
    (((STA + 40) + 0) + ((zlen inb) - p)) = ((STA + 40) + ((zlen inb) - p)) := by
  lia

-- zstd/simple_decompress: lib/Spec/FseAbs.v (replace)
example
    {T1 T2 : Type}
    (maxSV : Int)
    (f : Nat)
    (acond : T1 → Bool)
    (arun : Nat → T2 → T1)
    (a0 : T2)
    (h1 : (Int.toNat (maxSV + 1)) ≤ f)
    (h2 : (acond (arun (Int.toNat (maxSV + 1)) a0)) = false) :
    ((Int.toNat (maxSV + 1)) + (f - (Int.toNat (maxSV + 1)))) = f := by
  lia

-- zstd/simple_decompress: lib/Spec/FseAbs.v (replace)
example
    {T1 T2 : Type}
    (maxSV : Int)
    (f : Nat)
    (acond : T1 → Bool)
    (arun : Nat → T2 → T1)
    (a0 : T2)
    (h1 : (Int.toNat (maxSV + 1)) ≤ f)
    (h2 : (acond (arun (Int.toNat (maxSV + 1)) a0)) = false) :
    ((Int.toNat (maxSV + 1)) + 1) = ((Int.toNat (maxSV + 1)) + 1) := by
  lia

-- zstd/simple_decompress: lib/Spec/FseLemmas.v (replace)
example
    {T1 T2 T3 : Type}
    (j : Nat)
    (ctz_aux : T1 → T2 → Int)
    (f : T1)
    (Z_div2 : T3 → T2)
    (x : T3)
    (h1 : ((j : Nat) : Int) ≤ (ctz_aux f (Z_div2 x))) :
    ((((j + 1) : Nat) : Int) - 1) = ((j : Nat) : Int) := by
  lia

-- zstd/simple_decompress: lib/Spec/FseLemmas.v (replace)
example
    (x : Int)
    (m : Int)
    (r : Int)
    (Zpow : Int → Int → Int)
    (a : Int)
    (h1 : (0 ≤ x ∧ x < (2 ^ (32 : Nat))))
    (h2 : (0 ≤ m ∧ m ≤ 11))
    (h3 : (0 ≤ r ∧ r ≤ 2))
    (h4 : (Int.fmod x (Zpow 2 ((2 * m) + 2))) = (((Zpow 2 (2 * m)) - 1) + (r * (Zpow 2 (2 * m)))))
    (h5 : (Int.fmod a (Zpow 2 ((2 * m) + 2))) = ((3 - r) * (Zpow 2 (2 * m))))
    (h6 : 0 < (Zpow 2 (2 * m)))
    (h7 : (Zpow 2 ((2 * m) + 1)) = (2 * (Zpow 2 (2 * m))))
    (h8 : (Zpow 2 ((2 * m) + 2)) = (4 * (Zpow 2 (2 * m))))
    (h9 : (r = 0 ∨ r = 2)) :
    ((Zpow 2 (2 * m)) + (1 * (Zpow 2 ((2 * m) + 1)))) = ((3 - 0) * (Zpow 2 (2 * m))) := by
  lia

-- zstd/simple_decompress: lib/Spec/FseLemmas.v (replace)
example
    (x : Int)
    (m : Int)
    (r : Int)
    (Zpow : Int → Int → Int)
    (a : Int)
    (h1 : (0 ≤ x ∧ x < (2 ^ (32 : Nat))))
    (h2 : (0 ≤ m ∧ m ≤ 11))
    (h3 : (0 ≤ r ∧ r ≤ 2))
    (h4 : (Int.fmod x (Zpow 2 ((2 * m) + 2))) = (((Zpow 2 (2 * m)) - 1) + (r * (Zpow 2 (2 * m)))))
    (h5 : (Int.fmod a (Zpow 2 ((2 * m) + 2))) = ((3 - r) * (Zpow 2 (2 * m))))
    (h6 : 0 < (Zpow 2 (2 * m)))
    (h7 : (Zpow 2 ((2 * m) + 1)) = (2 * (Zpow 2 (2 * m))))
    (h8 : (Zpow 2 ((2 * m) + 2)) = (4 * (Zpow 2 (2 * m))))
    (h9 : (r = 0 ∨ r = 2)) :
    (Zpow 2 (2 * m)) = ((3 - 2) * (Zpow 2 (2 * m))) := by
  lia

-- zstd/simple_decompress: lib/Spec/FseReaderRT.v (replace)
example
    {T1 T2 : Type}
    (m : Int)
    (Zpow : Int → Int → Int)
    (bits : T1 → Int → Int → Int)
    (r_bitStream : T2 → T1)
    (s : T2)
    (r : Int)
    (h1 : 0 ≤ (m / 12))
    (h2 : 0 < (Zpow 2 (2 * m)))
    (h3 : (bits (r_bitStream s) 0 ((2 * m) + 2)) = (((Zpow 2 (2 * m)) - 1) + (r * (Zpow 2 (2 * m)))))
    (h4 : (bits (r_bitStream s) 0 24) = ((2 ^ (24 : Nat)) - 1))
    (h5 : 0 < (Zpow 2 (2 * (m - 12)))) :
    ((2 * (m - 12)) + 2) = ((2 * (m - 12)) + 2) := by
  lia

-- zstd/simple_decompress: lib/Spec/FseReaderRT.v (replace)
example
    {T1 T2 : Type}
    (a_T : T1 → Int)
    (a : T1)
    (m : Int)
    (m' : Int)
    (r : Int)
    (k : Int)
    (T1 : Int)
    (hbSize : Int)
    (r_bitStream : T2 → Int)
    (s1 : T2)
    (Zpow : Int → Int → Int)
    (h1 : (0 ≤ m ∧ m ≤ 85))
    (h2 : (0 ≤ r ∧ r < 3))
    (h3 : k = ((3 * m) + r))
    (h4 : T1 = (((a_T a) + (2 * m)) + 2))
    (h5 : (m / 12) < ((((Int.toNat hbSize) + 1) : Nat) : Int))
    (h6 : (m / 12) < 8)
    (h7 : (0 ≤ m' ∧ m' < 12))
    (h8 : m = ((12 * (m / 12)) + m'))
    (h9 : ((Int.fdiv (r_bitStream s1) (Zpow 2 (2 * m'))) % 4) = r) :
    ((a_T a) + (2 * m)) = (((a_T a) + (24 * (m / 12))) + (2 * m')) := by
  lia

-- zstd/simple_decompress: lib/Spec/FseWriterRT.v (replace)
example
    {T1 : Type}
    (q24 : Int)
    (q3 : Int)
    (a : T1)
    (a_T : T1 → Int)
    (k : Int)
    (maxSV : Int)
    (j : Int)
    (a_sym : T1 → Int)
    (T1 : Int)
    (Zpow : Int → Int → Int)
    (v : Int)
    (N2 : Int)
    (T2 : Int)
    (h1 : 0 ≤ q24)
    (h2 : (0 ≤ q24 ∧ (8 * q24) ≤ (k / 3)))
    (h3 : (k / 3) ≤ maxSV)
    (h4 : q24 = ((j - (a_sym a)) / 24))
    (h5 : ((a_T a) + (16 * q24)) ≤ T1)
    (h6 : (0 ≤ q3 ∧ q3 < 8))
    (h7 : (k / 3) = ((8 * q24) + q3))
    (h8 : (0 ≤ ((Zpow 2 (16 * q24)) - 1) ∧ ((Zpow 2 (16 * q24)) - 1) < (Zpow 2 (16 * q24))))
    (h9 : (v = (k % 3) ∧ (0 ≤ v ∧ v < 3)))
    (h10 : (0 ≤ N2 ∧ N2 < (Zpow 2 T2)))
    (h11 : (T2 + 2) = T1) :
    ((16 * q24) + (2 * q3)) = (2 * ((8 * q24) + q3)) := by
  lia

-- zstd/simple_decompress: lib/Spec/ZdHufFse.v (replace)
example
    {T1 : Type}
    (norm : T1)
    (N_1 : Int)
    (s : Int)
    (i : Int)
    (Znth : Int → T1 → Int)
    (h1 : (0 ≤ s ∧ s < N_1))
    (h2 : (0 ≤ i ∧ i < (Znth s norm))) :
    s = (0 + (((Int.toNat s) : Nat) : Int)) := by
  lia

-- zstd/simple_decompress: lib/Spec/ZdSeqBuildThm.v (assert)
example
    (tl : Int)
    (high : Int)
    (u : Int)
    (Zpow : Int → Int → Int)
    (cover_tl : Int → Bool)
    (h1 : (5 ≤ tl ∧ tl ≤ 9))
    (h2 : (0 ≤ high ∧ high < (Zpow 2 tl)))
    (h3 : (0 ≤ u ∧ u ≤ high))
    (h4 : (cover_tl tl) = true) :
    (tl = 5 ∨ (tl = 6 ∨ (tl = 7 ∨ (tl = 8 ∨ tl = 9)))) := by
  lia

-- zstd/simple_decompress: lib/Spec/ZdSeqBuildThm.v (replace)
example
    {T1 : Type}
    (Znth : Int → T1 → Int)
    (s : Int)
    (norm : T1)
    (nsum : Int → Int)
    (maxSV : Int)
    (h1 : s = (maxSV + 1))
    (h2 : (0 ≤ s ∧ s ≤ maxSV)) :
    ((Int.toNat (Znth s norm)) + (Int.toNat ((nsum (maxSV + 1)) - (nsum (s + 1))))) = (Int.toNat ((nsum (maxSV + 1)) - (nsum s))) := by
  lia

-- zstd/simple_decompress: lib/Spec/ZdSeqBuildThm.v (replace)
example
    {list_Z seq_kind : Type}
    (norm : list_Z)
    (maxSV : Int)
    (tl : Int)
    (k : seq_kind)
    (cells0 : list_Z)
    (symNext0 : list_Z)
    (spread0 : list_Z)
    (size : Int)
    (Zlength : list_Z → Int)
    (pws : list_Z → Int → Int)
    (Zpow : Int → Int → Int)
    (kind_max : seq_kind → Int)
    (kind_maxLog : seq_kind → Int)
    (nsum : Int → Int)
    (high : Int)
    (h1 : (5 ≤ tl ∧ tl ≤ 9))
    (h2 : (0 ≤ maxSV ∧ maxSV ≤ 52))
    (h3 : (maxSV + 1) ≤ (Zlength norm))
    (h4 : (pws norm (maxSV + 1)) = (Zpow 2 tl))
    (h5 : maxSV ≤ (kind_max k))
    (h6 : tl ≤ (kind_maxLog k))
    (h7 : (Zlength cells0) = size)
    (h8 : (maxSV + 1) ≤ (Zlength symNext0))
    (h9 : (size + 8) ≤ (Zlength spread0))
    (h10 : (nsum (maxSV + 1)) ≤ size)
    (h11 : high = ((nsum (maxSV + 1)) - 1))
    (h12 : (2 * (size / 2)) = size)
    (h13 : size = ((Zpow 2 (tl - 1)) * 2)) :
    (Int.toNat ((size - 1) + 1)) = (2 * (Int.toNat (size / 2))) := by
  lia

-- zstd/zstd_frame_info: lib/AsanW/AFake_arep.v (replace)
example
    {T1 : Type}
    (F : Int)
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
    (Z_land : Int → Int → Int)
    (c : Int)
    (pos' : Int)
    (a' : Int)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ pos ∧ pos < 16384))
    (h3 : flag = (fk_flag L 0 pos))
    (h4 : F = (fk_frame L 0 pos))
    (h5 : (fflag L 0 F) = flag)
    (h6 : (shad F) = (2147450880 + (F / 8)))
    (h7 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h8 : ((((shad (al_fake L)) + 4608) + (8 * pos)) = (shad F) ∧ (((shad F) + 8) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 8) ≤ 17594333495296)))
    (h9 : (((shad F) + 8) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h10 : pos = (Z_land h_1 16383))
    (h11 : flag = (((al_fake L) + 4096) + pos))
    (h12 : F = (((al_fake L) + 36864) + (pos * 64)))
    (h13 : (F % 64) = 0)
    (h14 : (fk_flag L c pos') ≠ flag)
    (h15 : (shad a') = (2147450880 + (a' / 8))) :
    (F + 24) = ((F + ((8 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- zstd/zstd_frame_info: lib/AsanW/AFake_arep1k.v (replace)
example
    {T1 : Type}
    (F : Int)
    (shad : Int → Int)
    (al_fake : T1 → Int)
    (L : T1)
    (shlen : Int → Int)
    (fk_flag : T1 → Int → Int → Int)
    (fk_frame : T1 → Int → Int → Int)
    (pos : Int)
    (pos' : Int)
    (flag : Int)
    (fflag : T1 → Int → Int → Int)
    (c : Int)
    (a' : Int)
    (h1 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h2 : pos' = pos)
    (h3 : flag = (fk_flag L 1 pos))
    (h4 : F = (fk_frame L 1 pos))
    (h5 : (fflag L 1 F) = flag)
    (h6 : (shad F) = (2147450880 + (F / 8)))
    (h7 : ((((shad (al_fake L)) + 135680) + (16 * pos)) = (shad F) ∧ (((shad F) + 16) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 16) ≤ 17594333495296)))
    (h8 : (((shad F) + 16) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h9 : flag = (((al_fake L) + 20480) + pos))
    (h10 : F = (((al_fake L) + 1085440) + (pos * 128)))
    (h11 : (F % 128) = 0)
    (h12 : (fk_flag L c pos') ≠ flag)
    (h13 : (shad a') = (2147450880 + (a' / 8))) :
    (F + 8) = (F + ((8 : Nat) : Int)) := by
  lia

-- zstd/zstd_frame_info: lib/AsanW/AFake_arep1k.v (replace)
example
    {T1 : Type}
    (F : Int)
    (shad : Int → Int)
    (al_fake : T1 → Int)
    (L : T1)
    (shlen : Int → Int)
    (fk_flag : T1 → Int → Int → Int)
    (fk_frame : T1 → Int → Int → Int)
    (pos : Int)
    (pos' : Int)
    (flag : Int)
    (fflag : T1 → Int → Int → Int)
    (c : Int)
    (a' : Int)
    (h1 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h2 : pos' = pos)
    (h3 : flag = (fk_flag L 1 pos))
    (h4 : F = (fk_frame L 1 pos))
    (h5 : (fflag L 1 F) = flag)
    (h6 : (shad F) = (2147450880 + (F / 8)))
    (h7 : ((((shad (al_fake L)) + 135680) + (16 * pos)) = (shad F) ∧ (((shad F) + 16) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 16) ≤ 17594333495296)))
    (h8 : (((shad F) + 16) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h9 : flag = (((al_fake L) + 20480) + pos))
    (h10 : F = (((al_fake L) + 1085440) + (pos * 128)))
    (h11 : (F % 128) = 0)
    (h12 : (fk_flag L c pos') ≠ flag)
    (h13 : (shad a') = (2147450880 + (a' / 8))) :
    (F + 120) = (((F + ((8 : Nat) : Int)) + ((16 : Nat) : Int)) + ((96 : Nat) : Int)) := by
  lia

-- zstd/zstd_frame_info: lib/AsanW/ATsafeCore.v (replace)
example
    (lo : Int)
    (len : Int)
    (z : Int)
    (h1 : 0 ≤ lo)
    (h2 : (lo ≤ z ∧ z < (lo + len)))
    (h3 : (lo / 4096) ≤ (z / 4096))
    (h4 : (z / 4096) ≤ (((lo + len) - 1) / 4096)) :
    (((lo / 4096) * 4096) + (4096 * (((Int.toNat ((z / 4096) - (lo / 4096))) : Nat) : Int))) = ((z / 4096) * 4096) := by
  lia

-- zstd/zstd_frame_info: lib/AsanW/F_printf_core_xloop.v (replace)
example
    {region list_Z T3 : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (rstk : region)
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
    (KHIGH : Int)
    (r_lo : region → Int)
    (r_hi : region → Int)
    (x : Int)
    (hex_digits : T3 → Int → list_Z)
    (l : T3)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 622592)
    (h5 : ((634056 ≤ Fp ∧ (Fp + 232) ≤ 659064) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6241880 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : KHIGH ≤ lo)
    (h12 : ((r_lo rstk) ≤ lo ∧ q ≤ (r_hi rstk)))
    (h13 : (x / 16) < 1152921504606846976)
    (h14 : 1 ≤ (zlength (hex_digits l x))) :
    ((q + (-392)) + (j - 1)) = (((q + (-392)) + j) + (-1)) := by
  lia

-- zstd/zstd_frame_info: lib/BothW/AF_fi_fdsA.v (replace)
example
    {alayout list_Z region : Type}
    (L : alayout)
    (SPV : Int)
    (bl : list_Z)
    (lo : Int)
    (rstk : region)
    (FF : Int)
    (zlen : list_Z → Int)
    (ATOP : Int)
    (al_top : alayout → Int)
    (r_lo : region → Int)
    (r_hi : region → Int)
    (r_rlo : region → Int)
    (shad : Int → Int)
    (Z_shiftr : Int → Int → Int)
    (h1 : (zlen bl) < (2 ^ (62 : Nat)))
    (h2 : (ATOP + 4096) ≤ lo)
    (h3 : lo ≤ ((SPV - 224) - (192 + 8192)))
    (h4 : (SPV + 16) < (al_top L))
    (h5 : (SPV % 16) = 0)
    (h6 : (r_lo rstk) ≤ lo)
    (h7 : SPV ≤ (r_hi rstk))
    (h8 : ATOP ≤ (r_rlo rstk))
    (h9 : (al_top L) ≤ (2 ^ (47 : Nat)))
    (h10 : (FF + 128) ≤ ATOP)
    (h11 : (FF % 128) = 0)
    (h12 : (shad FF) = ((Z_shiftr FF 3) + 2147450880))
    (h13 : (2147450880 ≤ ((Z_shiftr FF 3) + 2147450880) ∧ (((Z_shiftr FF 3) + 2147450880) + 16) ≤ 17594333495296)) :
    ((FF + 32) + (8 * ((6 : Nat) : Int))) = ((FF + 32) + 48) := by
  lia

-- zstd/zstd_frame_info: lib/BothW/ASF_refill.v (replace)
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
    (a_qglob_bytes : T10 → Int)
    (Q_MAX : Int)
    (aregion_info : T1 → T4 → Int)
    (al_space_beg : T1 → Int)
    (aregion : T1 → T4 → Int)
    (c_mapped_user : T11 → Int)
    (get_cls : T6 → T4 → T11)
    (K_REGION : Int)
    (h1 : (bv_unsigned sp) < (2 ^ (47 : Nat)))
    (h2 : ((shad (hm + 16)) = ((shad mb) + 768) ∧ ((shlen (rup n 8)) ≤ ((ms / 8) - 768) ∧ (0 < (shlen (rup n 8)) ∧ (((hm + 16) + (rup n 8)) ≤ (mb + ms) ∧ (2148232192 ≤ (shad mb) ∧ ((shad mb) + (ms / 8)) ≤ 17594332446720))))))
    (h3 : (mb % 8) = 0)
    (h4 : (0 ≤ (qfirst L (q_loc Q)) ∧ (qfirst L (q_loc Q)) < (2 ^ (64 : Nat))))
    (h5 : (enq_is_app st_r) = false)
    (h6 : (enq_is_app st_r) = true)
    (h7 : (Q_CACHE < (a_qloc_bytes (st_enq st_r (CSec mb ms n))) → ((a_qglob_bytes (st_enq st_r (CSec mb ms n))) + (a_qloc_bytes (st_enq st_r (CSec mb ms n)))) ≤ Q_MAX))
    (h8 : (aregion_info L K_BATCH_CLASS) = (((al_space_beg L) + 137438953472) + 3072))
    (h9 : (aregion L K_BATCH_CLASS) = ((al_space_beg L) + (24 * 4294967296)))
    (h10 : (2199023255552 ≤ (shad ((aregion L K_BATCH_CLASS) + (c_mapped_user (get_cls st K_BATCH_CLASS)))) ∧ ((shad (aregion L K_BATCH_CLASS)) + (shlen K_REGION)) ≤ 17594333495296))
    (h11 : ((mb + ms) ≤ ((aregion L K_BATCH_CLASS) + (c_mapped_user (get_cls st K_BATCH_CLASS))) ∨ ((aregion L K_BATCH_CLASS) + K_REGION) ≤ mb))
    (h12 : (((shad (hm + 16)) + (shlen (rup n 8))) ≤ (shad ((aregion L K_BATCH_CLASS) + (c_mapped_user (get_cls st K_BATCH_CLASS)))) ∨ ((shad (aregion L K_BATCH_CLASS)) + (shlen K_REGION)) ≤ (shad (hm + 16)))) :
    ((al_t L) + 2784) = (((al_t L) + 2768) + 16) := by
  lia

-- zstd/zstd_frame_info: lib/Plain/RF_fi_ffsi.v (replace)
example
    {list_Z T2 T3 : Type}
    (SP : Int)
    (bl : list_Z)
    (R : Int)
    (lo : Int)
    (zlen : list_Z → Int)
    (FFSI_DEPTH : Int)
    (length : T2 → Nat)
    (map : T3 → list_Z → T2)
    (Z_to_bv : Nat → T3)
    (h1 : (zlen bl) < (2 ^ (62 : Nat)))
    (h2 : lo ≤ (SP - FFSI_DEPTH))
    (h3 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h4 : ((R + 24) ≤ (SP - FFSI_DEPTH) ∨ SP ≤ R))
    (h5 : (((length (map (Z_to_bv 8) bl)) : Nat) : Int) = (zlen bl)) :
    (SP + (-104)) = ((SP + (-116)) + ((12 : Nat) : Int)) := by
  lia

-- zstd/zstd_frame_info: lib/Plain/RF_fi_ffsi.v (replace)
example
    {list_Z T2 T3 T4 : Type}
    (SP : Int)
    (bl : list_Z)
    (R : Int)
    (lo : Int)
    (zlen : list_Z → Int)
    (k : Int)
    (bv_unsigned : T2 → Int)
    (r : T2)
    (FFSI_DEPTH : Int)
    (length : T3 → Nat)
    (map : T4 → list_Z → T3)
    (Z_to_bv : Nat → T4)
    (h1 : (zlen bl) < (2 ^ (62 : Nat)))
    (h2 : lo ≤ (SP - FFSI_DEPTH))
    (h3 : (0 ≤ SP ∧ SP < (2 ^ (64 : Nat))))
    (h4 : ((R + 24) ≤ (SP - FFSI_DEPTH) ∨ SP ≤ R))
    (h5 : (((length (map (Z_to_bv 8) bl)) : Nat) : Int) = (zlen bl)) :
    ((zlen bl) - (k + ((bv_unsigned r) + 3))) = (((zlen bl) - k) - ((bv_unsigned r) + 3)) := by
  lia

-- zstd/zstd_frame_info: lib/Plain/RF_free.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (m_maplen : T1 → Int)
    (get_meta_rec : T2 → T3 → T1)
    (st : T2)
    (g : T3)
    (off' : Int)
    (off : Int)
    (r : T4)
    (pf : T5)
    (b : T5)
    (conc : T2 → T5 → Int)
    (r_base : T4 → Int)
    (snd : T5 → Int)
    (c0 : T5)
    (blk_addr : T6 → Int)
    (blk : T6)
    (get_stride : T1 → Int)
    (i : Int)
    (m_last_idx : T1 → Int)
    (round_up_pg : T7 → Int)
    (r_len : T4 → T7)
    (stq : Int)
    (e : T5)
    (h1 : off' = off)
    (h2 : (conc st pf) = ((r_base r) + (snd pf)))
    (h3 : (conc st c0) = ((r_base r) + (snd c0)))
    (h4 : (snd pf) = ((snd c0) + (16 * off)))
    (h5 : (blk_addr blk) = ((r_base r) + (snd pf)))
    (h6 : (snd c0) = (((snd b) + 16) + ((get_stride (get_meta_rec st g)) * i)))
    (h7 : (((get_stride (get_meta_rec st g)) * i) % 16) = 0)
    (h8 : 0 ≤ ((get_stride (get_meta_rec st g)) * i))
    (h9 : ((get_stride (get_meta_rec st g)) * (i + 1)) ≤ ((get_stride (get_meta_rec st g)) * ((m_last_idx (get_meta_rec st g)) + 1)))
    (h10 : ((snd pf) % 16) = 0)
    (h11 : ((snd pf) + 16) ≤ (round_up_pg (r_len r)))
    (h12 : ((16 * off) + 16) ≤ stq)
    (h13 : (0 ≤ ((r_base r) + (snd pf)) ∧ (((r_base r) + (snd pf)) + 16) ≤ (2 ^ (64 : Nat))))
    (h14 : (((r_base r) + (round_up_pg (r_len r))) ≤ 65536 ∨ 323584 ≤ (r_base r)))
    (h15 : (conc st b) = ((r_base r) + (snd b)))
    (h16 : (snd e) = (((((snd b) + 16) + ((get_stride (get_meta_rec st g)) * i)) + (get_stride (get_meta_rec st g))) - 4)) :
    (((m_maplen (get_meta_rec st g)) * 256) * 16) = ((m_maplen (get_meta_rec st g)) * 4096) := by
  lia

-- zstd/zstd_frame_info: lib/Plain/RF_main_B3.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (DATA : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st : T3)
    (rd_cap : T3 → Int)
    (A' : Int)
    (A : Int)
    (h1 : (zlength (rd_content st)) = (((length DATA) : Nat) : Int))
    (h2 : 67108864 ≤ (rd_cap st))
    (h3 : (rd_cap st) < 67108864)
    (h4 : ((A' + ((rd_cap st) * 2)) ≤ A ∨ (A + (rd_cap st)) ≤ A')) :
    (Int.toNat (((length DATA) : Nat) : Int)) = (length DATA) := by
  lia
