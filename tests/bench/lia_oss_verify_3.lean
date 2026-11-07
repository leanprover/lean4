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

Part 3 of 4. `lia_oss_verify_failing.lean` has the goals that `lia` does not prove yet.
-/

set_option linter.unusedVariables false

-- msgpack-c/unpack_pack_fuzzer: lib/Unp/PkAux.v (replace)
example {T1 : Type} (a : Int) (ELEM_SIZE : Int) (length : T1 → Nat) (es1 : T1) :
    ((a + ELEM_SIZE) + (ELEM_SIZE * (((length es1) : Nat) : Int))) = (a + (ELEM_SIZE * ((((length es1) : Nat) : Int) + 1))) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Unp/PkPop.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : Type}
    (E : T1)
    (st : T2)
    (A : Int)
    (v_end : T3 → Int)
    (k_evec : T4 → T3)
    (g : T4)
    (to_Z : T5 → Int)
    (s_next : T2 → T5)
    (bit62i : T5)
    (PrimInt63_ltb : T6 → T6 → Bool)
    (kT : T6)
    (n : T6)
    (bv_unsigned : T7 → Int)
    (ev : T1 → T6 → T7)
    (v_begin : T3 → Int)
    (length : T8 → Nat)
    (ls : T8)
    (v_capend : T3 → Int)
    (v_bytes : T3 → Int)
    (ls1 : T8)
    (okids : T9 → T8)
    (lo : T9)
    (sp : Int)
    (pe_ptr : T10 → Int)
    (e : T10)
    (two64 : Int)
    (E' : T1)
    (PrimInt63_add : T6 → Int → T6)
    (pe_rest : T10 → Int)
    (m : Bool)
    (k : Bool)
    (wsB : T8)
    (two63 : Int)
    (wsF : T8)
    (h1 : (to_Z (s_next st)) < (to_Z bit62i))
    (h2 : (PrimInt63_ltb kT n) = true)
    (h3 : (bv_unsigned (ev E kT)) = ((v_end (k_evec g)) - 24))
    (h4 : (v_begin (k_evec g)) ≠ ((v_end (k_evec g)) - 24))
    (h5 : 2 ≤ (((length ls) : Nat) : Int))
    (h6 : (v_capend (k_evec g)) = ((v_begin (k_evec g)) + (v_bytes (k_evec g))))
    (h7 : (v_end (k_evec g)) ≤ (v_capend (k_evec g)))
    (h8 : ((v_begin (k_evec g)) + 48) ≤ (v_end (k_evec g)))
    (h9 : (((length ls) : Nat) : Int) = ((((length ls1) : Nat) : Int) + 2))
    (h10 : sp < (((length (okids lo)) : Nat) : Int))
    (h11 : A = ((v_end (k_evec g)) - 48))
    (h12 : (0 ≤ (pe_ptr e) ∧ ((pe_ptr e) + 24) ≤ two64))
    (h13 : (4104 ≤ (pe_ptr e) ∧ ((pe_ptr e) + 24) ≤ 4611686018427387904))
    (h14 : (bv_unsigned (ev E' n)) = ((v_end (k_evec g)) - 48))
    (h15 : (bv_unsigned (ev E' (PrimInt63_add n 1))) = (pe_ptr e))
    (h16 : (bv_unsigned (ev E' (PrimInt63_add n 2))) = (pe_rest e))
    (h17 : ((m = false ∧ k = false) ∨ ((m = true ∧ k = true) ∨ (m = true ∧ k = false))))
    (h18 : (((length wsB) : Nat) : Int) < two63)
    (h19 : (((length wsF) : Nat) : Int) < two63) :
    (A + 17) = ((((v_end (k_evec g)) - 48) + (8 * 2)) + 1) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Unp/PkPush.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 T9 : Type}
    (E : T1)
    (st : T2)
    (v_end : T3 → Int)
    (k_evec : T4 → T3)
    (g : T4)
    (to_Z : T5 → Int)
    (s_next : T2 → T5)
    (bit62i : T5)
    (PrimInt63_ltb : T6 → T6 → Bool)
    (kT : T6)
    (n : T6)
    (rT : T7)
    (loZ : T7 → Int)
    (bv_unsigned : T8 → Int)
    (ev : T1 → T6 → T8)
    (v_cap : T3 → Int)
    (length : T9 → Nat)
    (ls : T9)
    (v_capend : T3 → Int)
    (v_begin : T3 → Int)
    (v_bytes : T3 → Int)
    (v_size : T3 → Int)
    (ls0 : T9)
    (E' : T1)
    (ws' : T9)
    (two63 : Int)
    (rN : T7)
    (wsF : T9)
    (h1 : (to_Z (s_next st)) < (to_Z bit62i))
    (h2 : (PrimInt63_ltb kT n) = true)
    (h3 : (loZ rT) = 0)
    (h4 : (bv_unsigned (ev E kT)) = ((v_end (k_evec g)) - 24))
    (h5 : 1 ≤ (((length ls) : Nat) : Int))
    (h6 : (v_capend (k_evec g)) = ((v_begin (k_evec g)) + (v_bytes (k_evec g))))
    (h7 : (v_end (k_evec g)) ≤ (v_capend (k_evec g)))
    (h8 : ((v_begin (k_evec g)) + 24) ≤ (v_end (k_evec g)))
    (h9 : ((v_end (k_evec g)) + 24) ≤ (v_capend (k_evec g)))
    (h10 : ((v_size (k_evec g)) + 1) ≤ (v_cap (k_evec g)))
    (h11 : (((length ls) : Nat) : Int) = ((((length ls0) : Nat) : Int) + 1))
    (h12 : (bv_unsigned (ev E' n)) = (v_end (k_evec g)))
    (h13 : (((length ws') : Nat) : Int) < two63)
    (h14 : (loZ rN) = 0)
    (h15 : (((length wsF) : Nat) : Int) < two63) :
    (((v_end (k_evec g)) - 24) + 24) = (v_end (k_evec g)) := by
  lia

-- msgpack-c/unpack_pack_fuzzer: lib/Unp/VDestroy.v (replace)
example
    {int r5 env sstate w64 T6 T7 T8 T9 T10 : Type}
    (PC : int)
    (CUR : r5)
    (BEG : r5)
    (NG : Nat)
    (E : env)
    (st0 : sstate)
    (l : w64)
    (B : Int)
    (Sz : Int)
    (n : Nat)
    (r5_eqb : r5 → T6 → Bool)
    (X0 : T6)
    (getr : sstate → r5 → T7)
    (bv_unsigned : T8 → Int)
    (den : env → T7 → T8)
    (w2Z : w64 → Int)
    (to_Z : int → Int)
    (EXIT : int)
    (guards_ok : int → Nat → Bool)
    (branch_taken : T9 → T8 → T8 → Bool)
    (BC_NE : T9)
    (mk : T10 → T7 → sstate)
    (pcB : T10)
    (y : T7)
    (rs1 : r5)
    (rs2 : r5)
    (z : Int)
    (two64 : Int)
    (h1 : (r5_eqb CUR X0) = false)
    (h2 : (bv_unsigned (den E (getr st0 BEG))) = B)
    (h3 : (w2Z l) < B)
    (h4 : (1 ≤ Sz ∧ Sz ≤ 32))
    (h5 : (to_Z PC) < (2 ^ (62 : Nat)))
    (h6 : NG ≤ 8)
    (h7 : (to_Z EXIT) < (2 ^ (62 : Nat)))
    (h8 : (guards_ok PC NG) = true)
    (h9 : (branch_taken BC_NE (den E (getr (mk pcB y) rs1)) (den E (getr (mk pcB y) rs2))) = false)
    (h10 : (0 ≤ z ∧ z < two64))
    (h11 : (bv_unsigned (den E y)) = z) :
    ((B + (Sz * (((n : Nat) : Int) + 1))) + (1 * 18446744073709551616)) = ((B + (Sz * ((((n : Nat) : Int) + 1) + 1))) + (18446744073709551616 - Sz)) := by
  lia

-- openssl/bignum: lib/BgB/X_exit.v (replace)
example
    {T1 : Type}
    (a : Int)
    (b : Int)
    (seg_rw_ok : T1 → Int → Int → Bool)
    (bgbsegs : T1)
    (h1 : (seg_rw_ok bgbsegs a (b - a)) = true) :
    b = (a + (b - a)) := by
  lia

-- openssl/bignum: lib/BgBnBoth/BnKaraMemA.v (replace)
example
    {list_Z block T3 T4 T5 T6 T7 : Type}
    (rp : Int)
    (tq : Int)
    (ap : Int)
    (bp : Int)
    (SP : Int)
    (lo : Int)
    (a : list_Z)
    (b : list_Z)
    (nR : Nat)
    (nT : Nat)
    (FS : Int)
    (SK : Int)
    (FB : Int)
    (bR : block)
    (bT : block)
    (bA : block)
    (bB : block)
    (i : Nat)
    (length : list_Z → Nat)
    (blk_addr : block → Int)
    (blk_size : block → Int)
    (USTACK_TOP : Int)
    (le8 : T3 → list_Z)
    (Z_to_bv : Int → T4 → T3)
    (v : T4)
    (store_ok : T5 → T6 → T7 → Int → Bool)
    (bgbsegs : T5)
    (m1 : T6)
    (wa : Int → T7)
    (h1 : 0 ≤ FS)
    (h2 : FB = (SP - FS))
    (h3 : 0 ≤ SK)
    (h4 : ((rp + (8 * ((nR : Nat) : Int))) ≤ ap ∨ (ap + (8 * (((length a) : Nat) : Int))) ≤ rp))
    (h5 : ((rp + (8 * ((nR : Nat) : Int))) ≤ bp ∨ (bp + (8 * (((length b) : Nat) : Int))) ≤ rp))
    (h6 : ((tq + (8 * ((nT : Nat) : Int))) ≤ ap ∨ (ap + (8 * (((length a) : Nat) : Int))) ≤ tq))
    (h7 : ((tq + (8 * ((nT : Nat) : Int))) ≤ bp ∨ (bp + (8 * (((length b) : Nat) : Int))) ≤ tq))
    (h8 : ((rp + (8 * ((nR : Nat) : Int))) ≤ tq ∨ (tq + (8 * ((nT : Nat) : Int))) ≤ rp))
    (h9 : ((rp + (8 * ((nR : Nat) : Int))) ≤ ((SP - FS) - SK) ∨ SP ≤ rp))
    (h10 : ((tq + (8 * ((nT : Nat) : Int))) ≤ ((SP - FS) - SK) ∨ SP ≤ tq))
    (h11 : ((ap + (8 * (((length a) : Nat) : Int))) ≤ ((SP - FS) - SK) ∨ SP ≤ ap))
    (h12 : ((bp + (8 * (((length b) : Nat) : Int))) ≤ ((SP - FS) - SK) ∨ SP ≤ bp))
    (h13 : ((blk_addr bR) ≤ rp ∧ (rp + (8 * ((nR : Nat) : Int))) ≤ ((blk_addr bR) + (blk_size bR))))
    (h14 : ((blk_addr bT) ≤ tq ∧ (tq + (8 * ((nT : Nat) : Int))) ≤ ((blk_addr bT) + (blk_size bT))))
    (h15 : ((blk_addr bA) ≤ ap ∧ (ap + (8 * (((length a) : Nat) : Int))) ≤ ((blk_addr bA) + (blk_size bA))))
    (h16 : ((blk_addr bB) ≤ bp ∧ (bp + (8 * (((length b) : Nat) : Int))) ≤ ((blk_addr bB) + (blk_size bB))))
    (h17 : lo ≤ ((SP - FS) - SK))
    (h18 : SP ≤ USTACK_TOP)
    (h19 : (length (le8 (Z_to_bv 64 v))) = 8)
    (h20 : (store_ok bgbsegs m1 (wa (rp + (8 * ((i : Nat) : Int)))) 8) = true) :
    (rp + (8 * (((i + 1) : Nat) : Int))) = ((rp + (8 * ((i : Nat) : Int))) + (8 * ((1 : Nat) : Int))) := by
  lia

-- openssl/bignum: lib/BgBnBoth/W_uadd_coreA.v (replace)
example
    {bignum_bptr list_Z T3 : Type}
    (Dr : Int)
    (br : bignum_bptr)
    (la : list_Z)
    (lb : list_Z)
    (length : list_Z → Nat)
    (wlimbs : T3 → list_Z)
    (bn_buf : bignum_bptr → T3)
    (bn_dmax : bignum_bptr → Nat)
    (W_uadd_core_uadd_top : list_Z → list_Z → Nat)
    (firstn : Nat → list_Z → list_Z)
    (h1 : (length (wlimbs (bn_buf br))) = (bn_dmax br))
    (h2 : (length la) = 0)
    (h3 : (W_uadd_core_uadd_top la lb) = 0)
    (h4 : 0 < (length la))
    (h5 : 0 < (((length la) : Nat) : Int))
    (h6 : (length (firstn (length lb) la)) = (length lb)) :
    (Dr + 0) = Dr := by
  lia

-- openssl/bignum: lib/BgBnE/W_recp_free.v (replace)
example
    {T1 : Type}
    (an : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (h1 : ((bv_unsigned sp) ≤ an ∧ 0 < an)) :
    (an + 60) = ((an + 48) + ((12 : Nat) : Int)) := by
  lia

-- openssl/bignum: lib/BgBnR/ShiftArr.v (replace)
example
    {list_Z T2 T3 : Type}
    (f : list_Z)
    (fp : Int)
    (Dr : Int)
    (nw8 : Int)
    (n : Int)
    (lb : Int)
    (nn : Int)
    (i : Nat)
    (Z_land : Int → Nat → Int)
    (length : list_Z → Nat)
    (le8 : T2 → list_Z)
    (Z_to_bv : Nat → T3 → T2)
    (lsh_at : list_Z → Int → Nat → T3)
    (h1 : (0 ≤ n ∧ n < 2147483648))
    (h2 : (0 ≤ lb ∧ lb < 64))
    (h3 : (Z_land n 63) = lb)
    (h4 : (0 ≤ nn ∧ nn < 18446744073709551616))
    (h5 : (nn % 64) = ((64 - lb) % 64))
    (h6 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h7 : 8 ≤ fp)
    (h8 : 0 ≤ Dr)
    (h9 : 0 ≤ nw8)
    (h10 : (fp ≤ (Dr + nw8) ∨ ((Dr + nw8) + (8 * ((((length f) : Nat) : Int) + 1))) ≤ fp))
    (h11 : 0 ≤ (Dr + nw8))
    (h12 : (length (le8 (Z_to_bv 64 (lsh_at f lb i)))) = 8) :
    i = (min i (i + 1)) := by
  lia

-- openssl/bignum: lib/BgBnR/ShiftArr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (Dr : Int)
    (nw8 : Int)
    (n : Int)
    (lb : Int)
    (nn : Int)
    (j : Nat)
    (j' : Nat)
    (Z_land : Int → Nat → Int)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 2147483648))
    (h2 : (0 ≤ lb ∧ lb < 64))
    (h3 : (Z_land n 63) = lb)
    (h4 : (0 ≤ nn ∧ nn < 18446744073709551616))
    (h5 : (nn % 64) = ((64 - lb) % 64))
    (h6 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h7 : 8 ≤ fp)
    (h8 : 0 ≤ Dr)
    (h9 : 0 ≤ nw8)
    (h10 : (fp ≤ (Dr + nw8) ∨ ((Dr + nw8) + (8 * ((((length f) : Nat) : Int) + 1))) ≤ fp))
    (h11 : (j + 1) < (length f))
    (h12 : 0 ≤ (Dr + nw8))
    (h13 : (0 ≤ (nth (j + 1) f 0) ∧ (nth (j + 1) f 0) < 18446744073709551616))
    (h14 : (0 ≤ (nth j f 0) ∧ (nth j f 0) < 18446744073709551616)) :
    ((Dr + nw8) + (8 * (((j' + 1) : Nat) : Int))) = (((Dr + nw8) + (8 * ((((j' + 1) + 1) : Nat) : Int))) + (-8)) := by
  lia

-- openssl/bignum: lib/BgBnR/ShiftArr.v (replace)
example
    {T1 T2 : Type}
    (fp : Int)
    (length : T1 → Nat)
    (f : T1)
    (Z_land : T2 → Nat → Int)
    (nn : T2)
    (lb : Int)
    (h1 : (Z_land nn 63) = ((64 - lb) % 64))
    (h2 : (length f) = 1)
    (h3 : ((length f) - 1) = (((length f) - 2) + 1)) :
    (fp + (8 * ((((length f) - 2) : Nat) : Int))) = ((fp + (8 * (((length f) : Nat) : Int))) + (-16)) := by
  lia

-- openssl/bignum: lib/BgBnR2/W_set_bit.v (replace)
example
    {T1 T2 : Type}
    (cnt : Nat)
    (n : Int)
    (i : Nat)
    (length : T1 → Nat)
    (bn_buf : T2 → T1)
    (br : T2)
    (bn_dmax : T2 → Nat)
    (wlimbs : T1 → T1)
    (nb : T1)
    (bn_top : T2 → Nat)
    (firstn : Nat → T1 → T1)
    (skipn : Nat → T1 → T1)
    (h1 : (n / 64) = ((i : Nat) : Int))
    (h2 : (0 ≤ ((i : Nat) : Int) ∧ ((i : Nat) : Int) ≤ n))
    (h3 : (length (bn_buf br)) = (bn_dmax br))
    (h4 : (0 ≤ ((i : Nat) : Int) ∧ ((i : Nat) : Int) < (((length (wlimbs (bn_buf br))) : Nat) : Int)))
    (h5 : (length nb) = (bn_dmax br))
    (h6 : ((cnt : Nat) : Int) = ((((i : Nat) : Int) + 1) - (((bn_top br) : Nat) : Int)))
    (h7 : (((length (wlimbs (firstn (bn_top br) (bn_buf br)))) : Nat) : Int) = (((bn_top br) : Nat) : Int))
    (h8 : (((length (wlimbs (skipn (i + 1) (bn_buf br)))) : Nat) : Int) = ((((bn_dmax br) : Nat) : Int) - (((i : Nat) : Int) + 1))) :
    (8 * cnt) = (Int.toNat (8 * ((cnt : Nat) : Int))) := by
  lia

-- openssl/bignum: lib/BgBnR2/W_sqr.v (replace)
example
    {T1 T2 : Type}
    (Dt : Int)
    (length : T1 → Nat)
    (la : T1)
    (al : Nat)
    (r0 : T1)
    (bv_unsigned : T2 → Int)
    (Z_to_bv : Int → Int → T2)
    (sp : T2)
    (Dr : Int)
    (Dx : Int)
    (h1 : (length la) = al)
    (h2 : (length r0) = (2 * al))
    (h3 : (2 * ((al : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-336)))) = ((bv_unsigned sp) + (-336)))
    (h5 : (bv_unsigned (Z_to_bv 64 Dr)) = Dr)
    (h6 : (bv_unsigned (Z_to_bv 64 Dt)) = Dt)
    (h7 : (bv_unsigned (Z_to_bv 64 Dx)) = Dx)
    (h8 : (bv_unsigned (Z_to_bv 64 ((al : Nat) : Int))) = ((al : Nat) : Int)) :
    (Dt + 0) = Dt := by
  lia

-- openssl/bignum: lib/BgBnRA/AFromMontArr.v (replace)
example
    {word list_Z T3 T4 T5 : Type}
    (sp : word)
    (lo : Int)
    (RP : Int)
    (NP : Int)
    (np : list_Z)
    (nl : Nat)
    (LB : Nat)
    (k : Nat)
    (length : list_Z → Nat)
    (bv_unsigned : word → Int)
    (SHHI : Int)
    (SHLO : Int)
    (le8 : T3 → list_Z)
    (Z_to_bv : Int → Int → T3)
    (v : Int)
    (store_ok : T4 → T5 → T3 → Int → Bool)
    (bgasegs : T4)
    (m1 : T5)
    (h1 : (length np) = nl)
    (h2 : 1 ≤ nl)
    (h3 : (2 * nl) ≤ LB)
    (h4 : ((LB : Nat) : Int) < (2 ^ (28 : Nat)))
    (h5 : ((NP + (8 * ((nl : Nat) : Int))) ≤ RP ∨ (RP + (8 * ((LB : Nat) : Int))) ≤ NP))
    (h6 : lo ≤ (((bv_unsigned sp) + (-144)) - 80))
    (h7 : SHHI ≤ lo)
    (h8 : (RP + (8 * ((LB : Nat) : Int))) ≤ (((bv_unsigned sp) + (-144)) - 80))
    (h9 : (NP + (8 * ((nl : Nat) : Int))) ≤ (((bv_unsigned sp) + (-144)) - 80))
    (h10 : (RP % 8) = 0)
    (h11 : (0 ≤ RP ∧ (RP + (8 * ((LB : Nat) : Int))) ≤ 140737488355328))
    (h12 : (NP % 8) = 0)
    (h13 : (0 ≤ NP ∧ (NP + (8 * ((nl : Nat) : Int))) ≤ 140737488355328))
    (h14 : ((RP + (8 * ((LB : Nat) : Int))) ≤ SHLO ∨ SHHI ≤ RP))
    (h15 : (bv_unsigned sp) ≤ 140737488355328)
    (h16 : (length (le8 (Z_to_bv 64 v))) = 8)
    (h17 : (store_ok bgasegs m1 (Z_to_bv 64 (RP + (8 * ((k : Nat) : Int)))) 8) = true) :
    (RP + (8 * (((k + 1) : Nat) : Int))) = ((RP + (8 * ((k : Nat) : Int))) + (8 * ((1 : Nat) : Int))) := by
  lia

-- openssl/bignum: lib/BgBnRA/AShiftArr.v (replace)
example
    {list_Z T2 T3 : Type}
    (f : list_Z)
    (fp : Int)
    (Dr : Int)
    (nw8 : Int)
    (n : Int)
    (lb : Int)
    (i : Nat)
    (Z_land : Int → Nat → Int)
    (length : list_Z → Nat)
    (le8 : T2 → list_Z)
    (Z_to_bv : Nat → T3 → T2)
    (lsh_at : list_Z → Int → Nat → T3)
    (h1 : (0 ≤ n ∧ n < 2147483648))
    (h2 : (0 ≤ lb ∧ lb < 64))
    (h3 : (Z_land n 63) = lb)
    (h4 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h5 : 8 ≤ fp)
    (h6 : 0 ≤ Dr)
    (h7 : 0 ≤ nw8)
    (h8 : (fp ≤ (Dr + nw8) ∨ ((Dr + nw8) + (8 * ((((length f) : Nat) : Int) + 1))) ≤ fp))
    (h9 : (fp % 8) = 0)
    (h10 : ((Dr + nw8) % 8) = 0)
    (h11 : 0 ≤ (Dr + nw8))
    (h12 : (length (le8 (Z_to_bv 64 (lsh_at f lb i)))) = 8) :
    i = (min i (i + 1)) := by
  lia

-- openssl/bignum: lib/BgBnRA/AShiftArr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (Dr : Int)
    (nw8 : Int)
    (n : Int)
    (lb : Int)
    (j : Nat)
    (j' : Nat)
    (Z_land : Int → Nat → Int)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 2147483648))
    (h2 : (0 ≤ lb ∧ lb < 64))
    (h3 : (Z_land n 63) = lb)
    (h4 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h5 : 8 ≤ fp)
    (h6 : 0 ≤ Dr)
    (h7 : 0 ≤ nw8)
    (h8 : (fp ≤ (Dr + nw8) ∨ ((Dr + nw8) + (8 * ((((length f) : Nat) : Int) + 1))) ≤ fp))
    (h9 : (fp % 8) = 0)
    (h10 : ((Dr + nw8) % 8) = 0)
    (h11 : (j + 1) < (length f))
    (h12 : (0 ≤ (nth (j + 1) f 0) ∧ (nth (j + 1) f 0) < 18446744073709551616))
    (h13 : (0 ≤ (nth j f 0) ∧ (nth j f 0) < 18446744073709551616)) :
    (fp + (8 * ((j' : Nat) : Int))) = ((fp + (8 * (((j' + 1) : Nat) : Int))) + (-8)) := by
  lia

-- openssl/bignum: lib/BgBnRA/AW_sqr_normal.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (length : list_Z → Nat)
    (bv_unsigned : word → Int)
    (Z_to_bv : Nat → Int → word)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 208))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : 208 ≤ (bv_unsigned sp))
    (h13 : (bv_unsigned (Z_to_bv 64 (2 * (((length A) : Nat) : Int)))) = (2 * (((length A) : Nat) : Int))) :
    (2 * (((length A) : Nat) : Int)) = (((2 * (length A)) : Nat) : Int) := by
  lia

-- openssl/bignum: lib/BgBnRA/AW_sqr_normal.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (bv_unsigned : word → Int)
    (k : Nat)
    (length : list_Z → Nat)
    (j : Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 208))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : (((((length A) : Nat) : Int) - 1) - ((k : Nat) : Int)) = ((j : Nat) : Int))
    (h13 : (0 ≤ (nth k A 0) ∧ (nth k A 0) < 18446744073709551616)) :
    ((bv_unsigned a1) + (8 * (1 + ((k : Nat) : Int)))) = (((bv_unsigned a1) + (8 * (((k : Nat) : Int) - 1))) + 16) := by
  lia

-- openssl/bignum: lib/BgBnRA/AW_sqr_normal.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (bv_unsigned : word → Int)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (Z_to_bv : Nat → Int → word)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 208))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : 208 ≤ (bv_unsigned sp))
    (h13 : 17594333495296 ≤ lo)
    (h14 : (length A) = 1)
    (h15 : 2 ≤ (length A))
    (h16 : (bv_unsigned (Z_to_bv 64 (nth 0 A 0))) = (nth 0 A 0))
    (h17 : (length A) = 2) :
    ((bv_unsigned a0) + (8 * (1 + (2 * ((1 : Nat) : Int))))) = ((bv_unsigned a0) + 24) := by
  lia

-- openssl/bignum: lib/BgBnRA/AW_sqr_normal.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (length : list_Z → Nat)
    (bv_unsigned : word → Int)
    (nth : Nat → list_Z → Int → Int)
    (Z_to_bv : Nat → Int → word)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 208))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 208) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : 208 ≤ (bv_unsigned sp))
    (h13 : 17594333495296 ≤ lo)
    (h14 : (length A) = 1)
    (h15 : 2 ≤ (length A))
    (h16 : (bv_unsigned (Z_to_bv 64 (nth 0 A 0))) = (nth 0 A 0))
    (h17 : (length A) = 2) :
    (((((length A) : Nat) : Int) - 1) - ((1 : Nat) : Int)) = ((((length A) : Nat) : Int) + (-2)) := by
  lia

-- openssl/bignum: lib/BgBnRB/AFromMontArr.v (replace)
example
    {word list_Z T3 T4 T5 : Type}
    (sp : word)
    (lo : Int)
    (RP : Int)
    (NP : Int)
    (np : list_Z)
    (nl : Nat)
    (LB : Nat)
    (k : Nat)
    (length : list_Z → Nat)
    (bv_unsigned : word → Int)
    (SHHI : Int)
    (SHLO : Int)
    (le8 : T3 → list_Z)
    (Z_to_bv : Int → Int → T3)
    (v : Int)
    (store_ok : T4 → T5 → T3 → Int → Bool)
    (bgbsegs : T4)
    (m1 : T5)
    (h1 : (length np) = nl)
    (h2 : 1 ≤ nl)
    (h3 : (2 * nl) ≤ LB)
    (h4 : ((LB : Nat) : Int) < (2 ^ (28 : Nat)))
    (h5 : ((NP + (8 * ((nl : Nat) : Int))) ≤ RP ∨ (RP + (8 * ((LB : Nat) : Int))) ≤ NP))
    (h6 : lo ≤ (((bv_unsigned sp) + (-160)) - 128))
    (h7 : SHHI ≤ lo)
    (h8 : (RP + (8 * ((LB : Nat) : Int))) ≤ (((bv_unsigned sp) + (-160)) - 128))
    (h9 : (NP + (8 * ((nl : Nat) : Int))) ≤ (((bv_unsigned sp) + (-160)) - 128))
    (h10 : (RP % 8) = 0)
    (h11 : (0 ≤ RP ∧ (RP + (8 * ((LB : Nat) : Int))) ≤ 140737488355328))
    (h12 : (NP % 8) = 0)
    (h13 : (0 ≤ NP ∧ (NP + (8 * ((nl : Nat) : Int))) ≤ 140737488355328))
    (h14 : 0 < RP)
    (h15 : 0 < NP)
    (h16 : ((RP + (8 * ((LB : Nat) : Int))) ≤ SHLO ∨ SHHI ≤ RP))
    (h17 : (bv_unsigned sp) ≤ 140737488355328)
    (h18 : (length (le8 (Z_to_bv 64 v))) = 8)
    (h19 : (store_ok bgbsegs m1 (Z_to_bv 64 (RP + (8 * ((k : Nat) : Int)))) 8) = true) :
    (RP + (8 * (((k + 1) : Nat) : Int))) = ((RP + (8 * ((k : Nat) : Int))) + (8 * ((1 : Nat) : Int))) := by
  lia

-- openssl/bignum: lib/BgBnRB/ARShiftArr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (T : Int)
    (n : Int)
    (rb : Int)
    (i : Nat)
    (Z_land : Int → Nat → Int)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 2147483648))
    (h2 : (0 ≤ rb ∧ rb < 64))
    (h3 : (Z_land n 63) = rb)
    (h4 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h5 : (T ≤ fp ∨ (fp + (8 * (((length f) : Nat) : Int))) ≤ T))
    (h6 : (fp % 8) = 0)
    (h7 : (T % 8) = 0)
    (h8 : 0 < fp)
    (h9 : 0 < T)
    (h10 : (i + 1) < (length f))
    (h11 : (0 ≤ (nth i f 0) ∧ (nth i f 0) < 18446744073709551616))
    (h12 : (0 ≤ (nth (i + 1) f 0) ∧ (nth (i + 1) f 0) < 18446744073709551616))
    (h13 : (((i : Nat) : Int) + 1) < (((length f) : Nat) : Int)) :
    (8 * (((i + 1) : Nat) : Int)) = ((8 * ((i : Nat) : Int)) + 8) := by
  lia

-- openssl/bignum: lib/BgBnRB/ARShiftArr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (T : Int)
    (n : Int)
    (rb : Int)
    (i : Nat)
    (length : list_Z → Nat)
    (Z_land : Int → Nat → Int)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 2147483648))
    (h2 : (0 ≤ rb ∧ rb < 64))
    (h3 : (Z_land n 63) = rb)
    (h4 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h5 : (T ≤ fp ∨ (fp + (8 * (((length f) : Nat) : Int))) ≤ T))
    (h6 : (fp % 8) = 0)
    (h7 : (T % 8) = 0)
    (h8 : 0 < fp)
    (h9 : 0 < T)
    (h10 : (i + 1) < (length f))
    (h11 : (0 ≤ (nth i f 0) ∧ (nth i f 0) < 18446744073709551616))
    (h12 : (0 ≤ (nth (i + 1) f 0) ∧ (nth (i + 1) f 0) < 18446744073709551616))
    (h13 : (((i : Nat) : Int) + 1) < (((length f) : Nat) : Int)) :
    (((((length f) : Nat) : Int) - 1) - (((i + 1) : Nat) : Int)) = ((((((length f) : Nat) : Int) - 1) - ((i : Nat) : Int)) + (-1)) := by
  lia

-- openssl/bignum: lib/BgBnRB/AShiftArr.v (replace)
example
    {list_Z T2 T3 : Type}
    (f : list_Z)
    (fp : Int)
    (Dr : Int)
    (nw8 : Int)
    (n : Int)
    (lb : Int)
    (i : Nat)
    (Z_land : Int → Nat → Int)
    (length : list_Z → Nat)
    (le8 : T2 → list_Z)
    (Z_to_bv : Nat → T3 → T2)
    (lsh_at : list_Z → Int → Nat → T3)
    (h1 : (0 ≤ n ∧ n < 2147483648))
    (h2 : (0 ≤ lb ∧ lb < 64))
    (h3 : (Z_land n 63) = lb)
    (h4 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h5 : 8 ≤ fp)
    (h6 : 0 ≤ Dr)
    (h7 : 0 ≤ nw8)
    (h8 : (fp ≤ (Dr + nw8) ∨ ((Dr + nw8) + (8 * ((((length f) : Nat) : Int) + 1))) ≤ fp))
    (h9 : (fp % 8) = 0)
    (h10 : ((Dr + nw8) % 8) = 0)
    (h11 : 0 < (Dr + nw8))
    (h12 : 0 < Dr)
    (h13 : 0 ≤ (Dr + nw8))
    (h14 : (length (le8 (Z_to_bv 64 (lsh_at f lb i)))) = 8) :
    i = (min i (i + 1)) := by
  lia

-- openssl/bignum: lib/BgBnRB/AW_sqr_normal.v (replace)
example
    {word list_Z T3 T4 : Type}
    (sp : word)
    (a0 : word)
    (A : list_Z)
    (PA : Int)
    (PT : Int)
    (bv_unsigned : word → Int)
    (k : Nat)
    (length : list_Z → Nat)
    (le8 : T3 → list_Z)
    (Z_to_bv : Nat → T4 → T3)
    (v : T4)
    (h1 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ PA ∨ (PA + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h2 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ PT ∨ (PT + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h3 : ((PA + (8 * (((length A) : Nat) : Int))) ≤ PT ∨ (PT + (8 * (2 * (((length A) : Nat) : Int)))) ≤ PA))
    (h4 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h5 : ((PA + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ PA))
    (h6 : ((PT + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ PT))
    (h7 : (length (le8 (Z_to_bv 64 v))) = 8) :
    ((bv_unsigned a0) + (8 * (((k + 1) : Nat) : Int))) = (((bv_unsigned a0) + (8 * ((k : Nat) : Int))) + (8 * ((1 : Nat) : Int))) := by
  lia

-- openssl/bignum: lib/BgBnRB/AW_sqr_normal.v (replace)
example
    {word list_Z T3 T4 : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (k : Nat)
    (length : list_Z → Nat)
    (bv_unsigned : word → Int)
    (cells_size : T3 → Nat)
    (FB : T4 → T3)
    (jb : T4)
    (j : Nat)
    (nth : Nat → list_Z → Int → Int)
    (Z_to_bv : Nat → Int → word)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 288))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : (((cells_size (FB jb)) : Nat) : Int) = 160)
    (h13 : 288 ≤ (bv_unsigned sp))
    (h14 : (((((length A) : Nat) : Int) - 1) - ((k : Nat) : Int)) = ((j : Nat) : Int))
    (h15 : ((((length A) : Nat) : Int) - ((k : Nat) : Int)) = (((j : Nat) : Int) + 1))
    (h16 : (0 ≤ (nth k A 0) ∧ (nth k A 0) < 18446744073709551616))
    (h17 : (bv_unsigned (Z_to_bv 64 ((j : Nat) : Int))) = ((j : Nat) : Int))
    (h18 : (bv_unsigned (Z_to_bv 64 (nth k A 0))) = (nth k A 0))
    (h19 : (1 ≤ ((j : Nat) : Int) ∧ ((j : Nat) : Int) < 2147483648)) :
    (16 * ((((k + 1) : Nat) : Int) - 1)) = ((16 * (((k : Nat) : Int) - 1)) + 16) := by
  lia

-- openssl/bignum: lib/BgBnRB/AW_sqr_normal.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (length : list_Z → Nat)
    (bv_unsigned : word → Int)
    (nth : Nat → list_Z → Int → Int)
    (Z_to_bv : Nat → Int → word)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 288))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : 288 ≤ (bv_unsigned sp))
    (h13 : 17594333495296 ≤ lo)
    (h14 : (length A) = 1)
    (h15 : 2 ≤ (length A))
    (h16 : (bv_unsigned (Z_to_bv 64 (nth 0 A 0))) = (nth 0 A 0)) :
    1 = (min 1 (length A)) := by
  lia

-- openssl/bignum: lib/BgBnRB/AW_sqr_normal.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (length : list_Z → Nat)
    (bv_unsigned : word → Int)
    (nth : Nat → list_Z → Int → Int)
    (Z_to_bv : Nat → Int → word)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 288))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 288) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : 288 ≤ (bv_unsigned sp))
    (h13 : 17594333495296 ≤ lo)
    (h14 : (length A) = 1)
    (h15 : 2 ≤ (length A))
    (h16 : (bv_unsigned (Z_to_bv 64 (nth 0 A 0))) = (nth 0 A 0))
    (h17 : (length A) = 2) :
    ((((length A) : Nat) : Int) - ((1 : Nat) : Int)) = ((((length A) : Nat) : Int) + (-1)) := by
  lia

-- openssl/bignum: lib/BgBnRB/W_bin2bnA.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (s' : T1)
    (bv_unsigned : T2 → Int)
    (sp : T2)
    (Z_to_bv : Int → Int → T2)
    (bn_dmax : T3 → Nat)
    (br : T3)
    (to_bytes : T1 → T1)
    (bs : T1)
    (zs : T1)
    (n : Nat)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-112)))) = ((bv_unsigned sp) + (-112)))
    (h2 : (bn_dmax br) = 0)
    (h3 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-144)))) = ((bv_unsigned sp) + (-144)))
    (h4 : (length (to_bytes bs)) = (length bs))
    (h5 : (length bs) = ((length zs) + (length s')))
    (h6 : 1 ≤ (length s'))
    (h7 : (((n : Nat) : Int) - 1) = (((((length s') : Nat) : Int) - 1) / 8))
    (h8 : (1 ≤ ((n : Nat) : Int) ∧ ((8 * (((n : Nat) : Int) - 1)) < (((length s') : Nat) : Int) ∧ (((length s') : Nat) : Int) ≤ ((8 * (((n : Nat) : Int) - 1)) + 8)))) :
    ((((length s') : Nat) : Int) - 1) = ((((length s') : Nat) : Int) + (-1)) := by
  lia

-- openssl/bignum: lib/BgBnRB/W_sqrAF.v (replace)
example
    {T1 : Type}
    (Dx : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (Dr : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 Dr)) = Dr)
    (h2 : (bv_unsigned (Z_to_bv 64 Dx)) = Dx) :
    (Dx + 0) = Dx := by
  lia

-- openssl/bignum: lib/BgBnRB/W_sub_wordAF.v (assert)
example (D : Int) (n : Int) (h1 : (0 ≤ D ∧ (D + (8 * n)) ≤ 140737488355328)) :
    (0 ≤ D ∧ (D + (8 * n)) ≤ 140737488355328) := by
  lia

-- openssl/bignum: lib/BgBnW2/SqrKaraX.v (replace)
example
    {T1 : Type}
    (n : Nat)
    (k' : Nat)
    (length : T1 → Nat)
    (a_lo : T1)
    (a_hi : T1)
    (lval : T1 → Int)
    (d : T1)
    (td : T1)
    (t : T1)
    (sgn3 : Int → Int → Int)
    (h1 : (2 ^ (k' + 1)) = (2 * n))
    (h2 : 8 ≤ n)
    (h3 : (length a_lo) = n)
    (h4 : (length a_hi) = n)
    (h5 : (lval a_hi) < (lval a_lo))
    (h6 : (lval d) = ((lval a_lo) - (lval a_hi)))
    (h7 : (length td) = (length t))
    (h8 : (lval a_lo) < (lval a_hi))
    (h9 : (lval d) = ((lval a_hi) - (lval a_lo)))
    (h10 : (sgn3 (lval a_lo) (lval a_hi)) = 0) :
    (4 * n) = ((2 * n) + (2 * n)) := by
  lia

-- openssl/bignum: lib/BgBnW2/W_from_mont_loops.v (replace)
example
    {list_Z : Type}
    (B : list_Z)
    (rtop : Nat)
    (mx : Nat)
    (length : list_Z → Nat)
    (h1 : (1 ≤ mx ∧ mx ≤ (length B)))
    (h2 : ((mx : Nat) : Int) < (2 ^ (31 : Nat)))
    (h3 : ((rtop : Nat) : Int) < (2 ^ (31 : Nat)))
    (h4 : rtop ≤ (length B)) :
    (((0 : Nat) : Int) - ((rtop : Nat) : Int)) = (0 - ((rtop : Nat) : Int)) := by
  lia

-- openssl/bignum: lib/BgBnW2/W_sqr_normal.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (bv_unsigned : word → Int)
    (length : list_Z → Nat)
    (k : Nat)
    (j : Nat)
    (nth : Nat → list_Z → Int → Int)
    (Z_to_bv : Nat → Int → word)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 128))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 128) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 128) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 128) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : (((((length A) : Nat) : Int) - 1) - ((k : Nat) : Int)) = ((j : Nat) : Int))
    (h13 : (0 ≤ (nth k A 0) ∧ (nth k A 0) < 18446744073709551616))
    (h14 : (bv_unsigned (Z_to_bv 64 ((j : Nat) : Int))) = ((j : Nat) : Int))
    (h15 : (bv_unsigned (Z_to_bv 64 (nth k A 0))) = (nth k A 0)) :
    ((bv_unsigned a0) + (8 * ((((length A) : Nat) : Int) + (((k + 1) : Nat) : Int)))) = (((bv_unsigned a0) + (8 * ((((length A) : Nat) : Int) + ((k : Nat) : Int)))) + 8) := by
  lia

-- openssl/bignum: lib/BgBnW2/W_sqr_normal.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (a3 : word)
    (lo : Int)
    (A : list_Z)
    (r0 : list_Z)
    (bv_unsigned : word → Int)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (Z_to_bv : Nat → Int → word)
    (h1 : (length r0) = (2 * (length A)))
    (h2 : 1 ≤ (((length A) : Nat) : Int))
    (h3 : (2 * (((length A) : Nat) : Int)) < 2147483648)
    (h4 : (bv_unsigned a2) = (((length A) : Nat) : Int))
    (h5 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1) ∨ ((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a0)))
    (h6 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ (bv_unsigned a3) ∨ ((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ (bv_unsigned a1)))
    (h8 : lo ≤ ((bv_unsigned sp) - 128))
    (h9 : (((bv_unsigned a0) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 128) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h10 : (((bv_unsigned a1) + (8 * (((length A) : Nat) : Int))) ≤ ((bv_unsigned sp) - 128) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h11 : (((bv_unsigned a3) + (8 * (2 * (((length A) : Nat) : Int)))) ≤ ((bv_unsigned sp) - 128) ∨ (bv_unsigned sp) ≤ (bv_unsigned a3)))
    (h12 : 128 ≤ (bv_unsigned sp))
    (h13 : (length A) = 1)
    (h14 : 2 ≤ (length A))
    (h15 : (bv_unsigned (Z_to_bv 64 (nth 0 A 0))) = (nth 0 A 0))
    (h16 : (length A) = 2) :
    ((bv_unsigned a1) + (8 * (1 + ((1 : Nat) : Int)))) = ((bv_unsigned a1) + 16) := by
  lia

-- openssl/bignum: lib/BgHXA/HxaImgSh.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (IMGSH_LO : Int)
    (i : Int)
    (shad : T1 → Int)
    (gd_beg : T2 → T1)
    (g : T2)
    (to_Z : T3 → Int)
    (of_Z : Int → T3)
    (a : T1)
    (length : T4 → Nat)
    (ushadow : T5 → T4)
    (gd_size : T2 → T5)
    (h1 : (to_Z (of_Z (i / 8))) = (i / 8))
    (h2 : ((IMGSH_LO + (8 * (i / 8))) + (i % 8)) = (IMGSH_LO + i))
    (h3 : (shad a) = (IMGSH_LO + i))
    (h4 : ((IMGSH_LO + i) - (shad (gd_beg g))) < (((length (ushadow (gd_size g))) : Nat) : Int)) :
    (IMGSH_LO + i) = ((shad (gd_beg g)) + ((IMGSH_LO + i) - (shad (gd_beg g)))) := by
  lia

-- openssl/bignum: lib/BgHXA/HxaMain.v (replace)
example {int word : Type} (ri : int) (sp : word) (bv_unsigned : word → Int) (to_Z : int → Int) :
    (bv_unsigned sp) = ((((bv_unsigned sp) - (to_Z ri)) - 262144) + (262144 + (to_Z ri))) := by
  lia

-- openssl/bignum: lib/BgMallocP/RF_ntf.v (replace)
example
    {word mstate aptr T4 T5 T6 T7 : Type}
    (lo : Int)
    (EH : Nat)
    (sp : word)
    (st : mstate)
    (g : aptr)
    (p : aptr)
    (snd : aptr → Int)
    (alloc_ceiling : Int)
    (c_init_done : T4 → Int)
    (ctx : mstate → T4)
    (bv_unsigned : word → Int)
    (stX : mstate)
    (stU : mstate)
    (get_meta_rec : mstate → aptr → T5)
    (m_last_idx : T5 → Int)
    (stG : mstate)
    (m_maplen : T5 → Int)
    (r : T6)
    (sstart_of : T5 → Int → Int)
    (g1 : aptr)
    (i1 : Int)
    (b1 : aptr)
    (get_stride : T5 → Int)
    (round_up_pg : T7 → Int)
    (r_len : T6 → T7)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : (c_init_done (ctx st)) ≠ 0)
    (h3 : (lo + (96 * ((EH : Nat) : Int))) ≤ (bv_unsigned sp))
    (h4 : lo ≤ ((bv_unsigned sp) - 96))
    (h5 : (c_init_done (ctx stX)) ≠ 0)
    (h6 : (c_init_done (ctx stU)) ≠ 0)
    (h7 : (m_maplen (get_meta_rec stG g)) ≠ 0)
    (h8 : (m_maplen (get_meta_rec stG g)) = 0)
    (h9 : (snd p) = (sstart_of (get_meta_rec stX g1) i1))
    (h10 : ((snd b1) + 16) ≤ (snd p))
    (h11 : 0 ≤ ((get_stride (get_meta_rec stX g1)) * i1))
    (h12 : (0 ≤ ((snd p) - 4) ∧ (snd p) < (round_up_pg (r_len r))))
    (h13 : 0 ≤ ((get_stride (get_meta_rec stG g)) * ((m_last_idx (get_meta_rec stG g)) + 1))) :
    ((snd p) - 1) = (((snd p) + (-2)) + 1) := by
  lia

-- openssl/bignum: lib/BgRep/BgRep.v (replace)
example (j : Nat) (BN_CTX_POOL_SIZE : Nat) (k : Nat) (h1 : j < BN_CTX_POOL_SIZE) :
    ((BN_CTX_POOL_SIZE * (k + 1)) + j) = (BN_CTX_POOL_SIZE + ((BN_CTX_POOL_SIZE * k) + j)) := by
  lia

-- openssl/bignum: lib/HX/HxMemSound.v (assert)
example
    {msize T2 : Type}
    (sz : msize)
    (to_Z : T2 → Int)
    (j : T2)
    (nbytes : msize → T2)
    (off : T2)
    (msz_nat : msize → Nat)
    (h1 : (to_Z (nbytes sz)) ≤ 8)
    (h2 : (to_Z j) = ((to_Z off) % 8))
    (h3 : (((to_Z off) % 8) + (((msz_nat sz) : Nat) : Int)) ≤ 8)
    (h4 : (to_Z j) = 0) :
    (to_Z j) = 0 := by
  lia

-- openssl/bignum: lib/Spec/BgExpWord.v (assert)
example
    (w : Int)
    (v : Int)
    (BW : Int)
    (h1 : (1 ≤ w ∧ w < BW))
    (h2 : (1 ≤ v ∧ v < BW))
    (h3 : 1 ≤ (Int.fdiv (w * v) BW))
    (h4 : (Int.fmod (w * v) BW) ≤ ((w * v) - BW))
    (h5 : (BW * 1) ≤ (BW * (Int.fdiv (w * v) BW)))
    (h6 : (v * w) ≤ ((w * v) - BW)) :
    BW ≤ 0 := by
  lia

-- openssl/bignum: lib/Spec/BgInvSpec.v (replace)
example
    {T1 T2 T3 : Type}
    (num_bits_pure : T1 → Int)
    (n : T1)
    (N_1 : Int)
    (Bp : Int → Int)
    (NFIX : Nat)
    (u : Nat)
    (g7 : T2)
    (length : T3 → Nat)
    (st_bns : T2 → T3)
    (rA : Nat)
    (rB : Nat)
    (rX : Nat)
    (rY : Nat)
    (rn : Nat)
    (ra : Nat)
    (rR : Nat)
    (s11 : T2)
    (s12 : T2)
    (Zpow : Int → Int → Int)
    (h1 : N_1 < (Bp 1))
    (h2 : rA < (length (st_bns g7)))
    (h3 : rB < (length (st_bns g7)))
    (h4 : rX < (length (st_bns g7)))
    (h5 : rY < (length (st_bns g7)))
    (h6 : ra < (length (st_bns g7)))
    (h7 : rn < (length (st_bns g7)))
    (h8 : rR < (length (st_bns g7)))
    (h9 : (length (st_bns s11)) = (length (st_bns g7)))
    (h10 : (length (st_bns s12)) = (length (st_bns g7)))
    (h11 : 0 < N_1)
    (h12 : rA < (NFIX + (u + 7)))
    (h13 : rB < (NFIX + (u + 7)))
    (h14 : rX < (NFIX + (u + 7)))
    (h15 : rY < (NFIX + (u + 7)))
    (h16 : ((N_1 * N_1) + N_1) < (Bp 2))
    (h17 : ((N_1 * N_1) + N_1) = (N_1 * (N_1 + 1)))
    (h18 : (N_1 * (N_1 + 1)) ≤ (((Bp 1) - 1) * (Bp 1)))
    (h19 : 0 < (Bp 1))
    (h20 : (1 * 1) ≤ (N_1 * N_1))
    (h21 : (N_1 * N_1) < (Zpow 2 (2 * (num_bits_pure n)))) :
    ((num_bits_pure n) + (num_bits_pure n)) = (2 * (num_bits_pure n)) := by
  lia

-- openssl/bignum: lib/Spec/BgLibSpec.v (replace)
example
    {T1 : Type}
    (n : Int)
    (Z_lor : Int → Int → Int)
    (BW : Int)
    (lval : T1 → Int)
    (l : T1)
    (x : Int)
    (Z_testbit : Int → Int → Bool)
    (h1 : (Z_lor (BW * (lval l)) x) = ((BW * (lval l)) + x))
    (h2 : (n / 64) = 0)
    (h3 : (Z_testbit x n) = false) :
    ((n - 64) + (1 * 64)) = n := by
  lia

-- openssl/bignum: lib/Spec/BgSqrCorrect.v (replace)
example {T1 : Type} (length : T1 → Nat) (seg : T1) (off : Nat) :
    (length seg) = ((off + (length seg)) - off) := by
  lia

-- openssl/bignum: lib/Spec/BgSqrCorrect.v (replace)
example {T1 : Type} (a : T1) (m : Nat) (length : T1 → Nat) (h1 : (length a) = m) :
    (m + m) = (2 * m) := by
  lia

-- openssl/bignum: lib/Spec/BnDivWords.v (assert)
example
    (h_1 : Int)
    (HW : Int)
    (dh : Int)
    (dl : Int)
    (BW : Int)
    (h1 : (dh * HW) ≤ h_1)
    (h2 : ((HW - 1) * dh) ≤ h_1)
    (h3 : (0 ≤ ((HW - 1) * dl) ∧ ((HW - 1) * dl) < BW))
    (h4 : 0 ≤ ((HW - 1) * dh))
    (h5 : h_1 < (dh * HW))
    (h6 : (Int.fdiv h_1 HW) < (dh + 1)) :
    (Int.fdiv h_1 HW) < dh := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanSMiz.v (replace)
example
    {list_Segment Model word T4 T5 : Type}
    (segs : list_Segment)
    (b : Int)
    (model0 : Model)
    (beg : word)
    (size : Int)
    (sp0 : word)
    (k : Int)
    (bv_unsigned : word → Int)
    (ae : Int)
    (words_ok : list_Segment → Int → T4 → Bool)
    (MIZ_WORDS : T4)
    (vm_backing_used : Model → Int)
    (vm_limit : T5 → Int)
    (m_vmmaps : Model → T5)
    (h1 : (words_ok segs b MIZ_WORDS) = true)
    (h2 : (0 ≤ size ∧ size ≤ (2 ^ (40 : Nat))))
    (h3 : (((bv_unsigned beg) + size) + 8) ≤ (2 ^ (64 : Nat)))
    (h4 : ((vm_backing_used model0) + (4096 * size)) ≤ (vm_limit (m_vmmaps model0)))
    (h5 : 16 ≤ (bv_unsigned sp0))
    (h6 : ((bv_unsigned sp0) ≤ (bv_unsigned beg) ∨ ((bv_unsigned beg) + size) ≤ ((bv_unsigned sp0) - 8)))
    (h7 : (0 ≤ k ∧ k ≤ size))
    (h8 : ((bv_unsigned beg) ≤ ae → k ≤ (ae - (bv_unsigned beg)))) :
    ((bv_unsigned beg) + (ae - (bv_unsigned beg))) = ae := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanSMzero.v (replace)
example
    {list_Segment Model machine_state T4 T5 T6 T7 : Type}
    (segs : list_Segment)
    (model0 : Model)
    (ms0 : machine_state)
    (dst : Int)
    (c : Int)
    (i : Int)
    (n : Int)
    (store_ok : list_Segment → T4 → T5 → Nat → Bool)
    (ms_mem : machine_state → T4)
    (Z_to_bv : Nat → Int → T5)
    (vm_backing_used : Model → Int)
    (length : T6 → Nat)
    (L : T6)
    (page_size : Int)
    (vm_limit : T7 → Int)
    (m_vmmaps : Model → T7)
    (h1 : 0 ≤ dst)
    (h2 : (32 ≤ c ∧ c < (2 ^ (63 : Nat))))
    (h3 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h4 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h5 : ((vm_backing_used model0) + ((((length L) : Nat) : Int) * page_size)) ≤ (vm_limit (m_vmmaps model0))) :
    ((dst + i) + ((8 : Nat) : Int)) = (dst + (i + 8)) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanSMzero.v (replace)
example
    {list_Segment Model machine_state T4 T5 T6 T7 : Type}
    (segs : list_Segment)
    (model0 : Model)
    (ms0 : machine_state)
    (dst : Int)
    (c : Int)
    (i : Int)
    (n : Int)
    (store_ok : list_Segment → T4 → T5 → Nat → Bool)
    (ms_mem : machine_state → T4)
    (Z_to_bv : Nat → Int → T5)
    (vm_backing_used : Model → Int)
    (length : T6 → Nat)
    (L : T6)
    (page_size : Int)
    (vm_limit : T7 → Int)
    (m_vmmaps : Model → T7)
    (h1 : 0 ≤ dst)
    (h2 : (32 ≤ c ∧ c < (2 ^ (63 : Nat))))
    (h3 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h4 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h5 : ((vm_backing_used model0) + ((((length L) : Nat) : Int) * page_size)) ≤ (vm_limit (m_vmmaps model0))) :
    (dst + (i + 8)) = ((dst + i) + 8) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMcM0.v (replace)
example
    {list_Segment Model machine_state T4 T5 T6 T7 T8 : Type}
    (segs : list_Segment)
    (model0 : Model)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (r : Int)
    (ms_mem : machine_state → T4)
    (Z_to_bv : Nat → Int → T5)
    (store_ok : list_Segment → T4 → T5 → Nat → Bool)
    (vm_backing_used : Model → Int)
    (length : T6 → Nat)
    (L : T6)
    (page_size : Int)
    (vm_limit : T7 → Int)
    (m_vmmaps : Model → T7)
    (bv_unsigned : T8 → Int)
    (rg : machine_state → Int → T8)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((vm_backing_used model0) + ((((length L) : Nat) : Int) * page_size)) ≤ (vm_limit (m_vmmaps model0)))
    (h9 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h10 : (0 ≤ r ∧ r < 32))
    (h11 : 0 ≤ k)
    (h12 : (k + (r % 4)) = n) :
    (dst + (k + ((1 : Nat) : Int))) = ((dst + k) + 1) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMcM0.v (replace)
example
    {list_Segment Model machine_state T4 T5 T6 T7 T8 : Type}
    (segs : list_Segment)
    (model0 : Model)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (r : Int)
    (ms_mem : machine_state → T4)
    (Z_to_bv : Nat → Int → T5)
    (store_ok : list_Segment → T4 → T5 → Nat → Bool)
    (vm_backing_used : Model → Int)
    (length : T6 → Nat)
    (L : T6)
    (page_size : Int)
    (vm_limit : T7 → Int)
    (m_vmmaps : Model → T7)
    (bv_unsigned : T8 → Int)
    (rg : machine_state → Int → T8)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((vm_backing_used model0) + ((((length L) : Nat) : Int) * page_size)) ≤ (vm_limit (m_vmmaps model0)))
    (h9 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h10 : (0 ≤ r ∧ r < 16))
    (h11 : 0 ≤ k)
    (h12 : (k + r) = n) :
    (dst + (k + ((4 : Nat) : Int))) = ((dst + k) + 4) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMcM0.v (replace)
example
    {list_Segment Model machine_state T4 T5 T6 T7 T8 : Type}
    (segs : list_Segment)
    (model0 : Model)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (ms_mem : machine_state → T4)
    (Z_to_bv : Nat → Int → T5)
    (store_ok : list_Segment → T4 → T5 → Nat → Bool)
    (vm_backing_used : Model → Int)
    (length : T6 → Nat)
    (L : T6)
    (page_size : Int)
    (vm_limit : T7 → Int)
    (m_vmmaps : Model → T7)
    (bv_unsigned : T8 → Int)
    (rg : machine_state → Int → T8)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((vm_backing_used model0) + ((((length L) : Nat) : Int) * page_size)) ≤ (vm_limit (m_vmmaps model0)))
    (h9 : ((bv_unsigned (rg ms0 1)) % 2) = 0) :
    (dst + (((k + ((4 : Nat) : Int)) + ((4 : Nat) : Int)) + ((4 : Nat) : Int))) = ((dst + k) + 12) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMemcpy.v (replace)
example
    {list_Segment machine_state T3 T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (r : Int)
    (ms_mem : machine_state → T3)
    (Z_to_bv : Nat → Int → T4)
    (store_ok : list_Segment → T3 → T4 → Nat → Bool)
    (bv_unsigned : T5 → Int)
    (rg : machine_state → Int → T5)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h9 : (0 ≤ r ∧ r < 32))
    (h10 : 0 ≤ k)
    (h11 : (k + (r % 4)) = n) :
    (dst + (k + ((1 : Nat) : Int))) = ((dst + k) + 1) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMemcpy.v (replace)
example
    {list_Segment machine_state T3 T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (r : Int)
    (ms_mem : machine_state → T3)
    (Z_to_bv : Nat → Int → T4)
    (store_ok : list_Segment → T3 → T4 → Nat → Bool)
    (bv_unsigned : T5 → Int)
    (rg : machine_state → Int → T5)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h9 : (0 ≤ r ∧ r < 32))
    (h10 : 0 ≤ k)
    (h11 : (k + (r % 4)) = n) :
    (src + (k + ((1 : Nat) : Int))) = ((src + k) + 1) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMemcpy.v (replace)
example
    {list_Segment machine_state T3 T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (r : Int)
    (ms_mem : machine_state → T3)
    (Z_to_bv : Nat → Int → T4)
    (store_ok : list_Segment → T3 → T4 → Nat → Bool)
    (bv_unsigned : T5 → Int)
    (rg : machine_state → Int → T5)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h9 : (0 ≤ r ∧ r < 16))
    (h10 : 0 ≤ k)
    (h11 : (k + r) = n) :
    (dst + (k + ((4 : Nat) : Int))) = ((dst + k) + 4) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMemcpy.v (replace)
example
    {list_Segment machine_state T3 T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (ms_mem : machine_state → T3)
    (Z_to_bv : Nat → Int → T4)
    (store_ok : list_Segment → T3 → T4 → Nat → Bool)
    (bv_unsigned : T5 → Int)
    (rg : machine_state → Int → T5)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((bv_unsigned (rg ms0 1)) % 2) = 0) :
    (dst + (k + ((4 : Nat) : Int))) = ((dst + k) + 4) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMemcpy.v (replace)
example
    {list_Segment machine_state T3 T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (ms_mem : machine_state → T3)
    (Z_to_bv : Nat → Int → T4)
    (store_ok : list_Segment → T3 → T4 → Nat → Bool)
    (bv_unsigned : T5 → Int)
    (rg : machine_state → Int → T5)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((bv_unsigned (rg ms0 1)) % 2) = 0) :
    (dst + ((k + ((4 : Nat) : Int)) + ((4 : Nat) : Int))) = ((dst + k) + 8) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AsanWMemcpy.v (replace)
example
    {list_Segment machine_state T3 T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (ms_mem : machine_state → T3)
    (Z_to_bv : Nat → Int → T4)
    (store_ok : list_Segment → T3 → T4 → Nat → Bool)
    (bv_unsigned : T5 → Int)
    (rg : machine_state → Int → T5)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((bv_unsigned (rg ms0 1)) % 2) = 0) :
    (dst + (((k + ((4 : Nat) : Int)) + ((4 : Nat) : Int)) + ((4 : Nat) : Int))) = ((dst + k) + 12) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AxSumStdio.v (assert)
example (cnt : Int) (h1 : (cnt = 1 ∨ cnt = 2)) :
    (((Int.toNat (16 * cnt)) : Nat) : Int) = (16 * cnt) := by
  lia

-- openssl/bignum: lib/VCommon/Ax/AxSumStdio.v (assert)
example
    (cnt : Int)
    (h1 : (cnt = 1 ∨ cnt = 2))
    (h2 : (((Int.toNat (16 * cnt)) : Nat) : Int) = (16 * cnt)) :
    (1 ≤ (Int.toNat (16 * cnt)) ∧ (Int.toNat (16 * cnt)) < 1000) := by
  lia

-- openssl/bndiv: lib/A/F_vfprintf_stdout.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (Z_land : Int → Int → Int)
    (Z_to_bv : Int → Int → T1)
    (sx32 : T2 → T1)
    (flags : T2)
    (h1 : (Z_land (bv_unsigned (Z_to_bv 64 (Z_land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104) = 0) :
    ((bv_unsigned sp) + (-360)) = (((bv_unsigned sp) + (-368)) + ((8 : Nat) : Int)) := by
  lia

-- openssl/bndiv: lib/A/I_pck.v (replace)
example
    {T1 T2 T3 : Type}
    (s : Int)
    (k : Nat)
    (length : T1 → Nat)
    (str : T1)
    (strchr_res : Int → T2 → T1 → Int)
    (c : T2)
    (bv_unsigned : T3 → Int)
    (Z_to_bv : Int → Int → T3)
    (h1 : k = (length str))
    (h2 : (strchr_res s c str) = 0)
    (h3 : (bv_unsigned (Z_to_bv 64 (s + ((k : Nat) : Int)))) = (s + ((k : Nat) : Int))) :
    ((s + ((k : Nat) : Int)) + 1) = (s + (((k : Nat) : Int) + 1)) := by
  lia

-- openssl/bndiv: lib/AxA/AxExportA.v (replace)
example
    {list_byte : Type}
    (bs : list_byte)
    (off : Nat)
    (k : Nat)
    (length : list_byte → Nat)
    (h1 : (off + k) ≤ (length bs)) :
    off = (min off (length bs)) := by
  lia

-- openssl/bndiv: lib/BnAsan/AW_lshift_arr.v (replace)
example
    {T1 : Type}
    (fp : Int)
    (length : T1 → Nat)
    (f : T1)
    (h1 : (length f) = 1)
    (h2 : ((length f) - 1) = (((length f) - 2) + 1)) :
    (fp + (8 * ((((length f) - 2) : Nat) : Int))) = ((fp + (8 * (((length f) : Nat) : Int))) + (-16)) := by
  lia

-- openssl/bndiv: lib/BnAsan/AW_lshift_arr.v (replace)
example
    {T1 : Type}
    (length : T1 → Nat)
    (f : T1)
    (h1 : (length f) = 1)
    (h2 : ((length f) - 1) = (((length f) - 2) + 1)) :
    (((((length f) - 2) : Nat) : Int) + 3) = ((((length f) : Nat) : Int) + 1) := by
  lia

-- openssl/bndiv: lib/BnAsan/AW_rshift_arr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (T : Int)
    (n : Int)
    (i : Nat)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 64))
    (h2 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h3 : ((fp + (8 * (((length f) : Nat) : Int))) ≤ T ∨ (T + (8 * (((length f) : Nat) : Int))) ≤ fp))
    (h4 : (fp % 8) = 0)
    (h5 : (T % 8) = 0)
    (h6 : (i + 1) < (length f))
    (h7 : (0 ≤ (nth i f 0) ∧ (nth i f 0) < 18446744073709551616))
    (h8 : (0 ≤ (nth (i + 1) f 0) ∧ (nth (i + 1) f 0) < 18446744073709551616)) :
    (fp + (8 * ((((i + 1) + 1) : Nat) : Int))) = ((fp + (8 * (((i + 1) : Nat) : Int))) + 8) := by
  lia

-- openssl/bndiv: lib/BnAsan/AW_rshift_arr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (T : Int)
    (n : Int)
    (i : Nat)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 64))
    (h2 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h3 : ((fp + (8 * (((length f) : Nat) : Int))) ≤ T ∨ (T + (8 * (((length f) : Nat) : Int))) ≤ fp))
    (h4 : (fp % 8) = 0)
    (h5 : (T % 8) = 0)
    (h6 : (i + 1) < (length f))
    (h7 : (0 ≤ (nth i f 0) ∧ (nth i f 0) < 18446744073709551616))
    (h8 : (0 ≤ (nth (i + 1) f 0) ∧ (nth (i + 1) f 0) < 18446744073709551616)) :
    (((((length f) : Nat) : Int) - 1) - (((i + 1) : Nat) : Int)) = ((((((length f) : Nat) : Int) - 1) - ((i : Nat) : Int)) + (-1)) := by
  lia

-- openssl/bndiv: lib/BnAsan/AW_rshift_arr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (T : Int)
    (n : Int)
    (i : Nat)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 64))
    (h2 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h3 : ((fp + (8 * (((length f) : Nat) : Int))) ≤ T ∨ (T + (8 * (((length f) : Nat) : Int))) ≤ fp))
    (h4 : (fp % 8) = 0)
    (h5 : (T % 8) = 0)
    (h6 : (i + 1) < (length f))
    (h7 : (0 ≤ (nth i f 0) ∧ (nth i f 0) < 18446744073709551616))
    (h8 : (0 ≤ (nth (i + 1) f 0) ∧ (nth (i + 1) f 0) < 18446744073709551616))
    (h9 : ((i + 1) + 1) = (length f)) :
    ((length f) - 1) = (i + 1) := by
  lia

-- openssl/bndiv: lib/BnAsan/W_bin2bnA.v (replace)
example (D : Int) (t : Nat) :
    ((D + (8 * ((t : Nat) : Int))) + (-8)) = ((D + (8 * ((t : Nat) : Int))) + (-8)) := by
  lia

-- openssl/bndiv: lib/BnAsan/W_bin2bnA.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (s' : T1)
    (bv_unsigned : T2 → Int)
    (sp : T2)
    (bn_dmax : T3 → Nat)
    (br : T3)
    (Z_to_bv : Int → Int → T2)
    (to_bytes : T1 → T1)
    (bs : T1)
    (zs : T1)
    (n : Nat)
    (h1 : (bn_dmax br) = 0)
    (h2 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-112)))) = ((bv_unsigned sp) + (-112)))
    (h3 : (length (to_bytes bs)) = (length bs))
    (h4 : (length bs) = ((length zs) + (length s')))
    (h5 : 1 ≤ (length s'))
    (h6 : (((n : Nat) : Int) - 1) = (((((length s') : Nat) : Int) - 1) / 8))
    (h7 : (1 ≤ ((n : Nat) : Int) ∧ ((8 * (((n : Nat) : Int) - 1)) < (((length s') : Nat) : Int) ∧ (((length s') : Nat) : Int) ≤ ((8 * (((n : Nat) : Int) - 1)) + 8)))) :
    ((((length s') : Nat) : Int) - 1) = ((((length s') : Nat) : Int) + (-1)) := by
  lia

-- openssl/bndiv: lib/BnP/LshiftArr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (T : Int)
    (n : Int)
    (nn : Int)
    (j : Nat)
    (j' : Nat)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 64))
    (h2 : (0 ≤ nn ∧ nn < 18446744073709551616))
    (h3 : (nn % 64) = ((64 - n) % 64))
    (h4 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h5 : 8 ≤ fp)
    (h6 : ((fp + (8 * (((length f) : Nat) : Int))) ≤ T ∨ (T + (8 * ((((length f) : Nat) : Int) + 1))) ≤ fp))
    (h7 : (j + 1) < (length f))
    (h8 : 0 ≤ T)
    (h9 : (0 ≤ (nth (j + 1) f 0) ∧ (nth (j + 1) f 0) < 18446744073709551616))
    (h10 : (0 ≤ (nth j f 0) ∧ (nth j f 0) < 18446744073709551616)) :
    (T + (8 * (((j' + 1) : Nat) : Int))) = ((T + (8 * ((((j' + 1) + 1) : Nat) : Int))) + (-8)) := by
  lia

-- openssl/bndiv: lib/BnP/RshiftArr.v (replace)
example
    {list_Z : Type}
    (f : list_Z)
    (fp : Int)
    (T : Int)
    (n : Int)
    (i : Nat)
    (length : list_Z → Nat)
    (nth : Nat → list_Z → Int → Int)
    (h1 : (0 ≤ n ∧ n < 64))
    (h2 : (1 ≤ (((length f) : Nat) : Int) ∧ (((length f) : Nat) : Int) < 2147483647))
    (h3 : ((fp + (8 * (((length f) : Nat) : Int))) ≤ T ∨ (T + (8 * (((length f) : Nat) : Int))) ≤ fp))
    (h4 : (i + 1) < (length f))
    (h5 : 0 ≤ T)
    (h6 : (0 ≤ (nth i f 0) ∧ (nth i f 0) < 18446744073709551616))
    (h7 : (0 ≤ (nth (i + 1) f 0) ∧ (nth (i + 1) f 0) < 18446744073709551616)) :
    (fp + (8 * ((((i + 1) + 1) : Nat) : Int))) = ((fp + (8 * (((i + 1) : Nat) : Int))) + 8) := by
  lia

-- openssl/bndiv: lib/BnP/W_ctx_get.v (assert)
example
    {T1 T2 T3 T4 : Type}
    (cx_pused : T1 → Nat)
    (c : T1)
    (cx_psize : T1 → Nat)
    (AD : T2)
    (i : Nat)
    (cx_used : T1 → Nat)
    (H : Int)
    (bn_flags : T3 → Int)
    (b : T3)
    (length : T4 → Nat)
    (cx_vals : T1 → T4)
    (Cu : Int)
    (ad_ctx : T2 → Int)
    (D : Int)
    (bn_dmax : T3 → Nat)
    (h1 : ((cx_psize c) = 0 ∨ (cx_psize c) = 16))
    (h2 : (cx_psize c) = 16)
    (h3 : i < 16)
    (h4 : i = (cx_used c))
    (h5 : (0 ≤ (bn_flags b) ∧ (bn_flags b) ≤ 1))
    (h6 : (length (cx_vals c)) = 16)
    (h7 : (((ad_ctx AD) + 72) ≤ D ∨ (D + (8 * (((bn_dmax b) : Nat) : Int))) ≤ (ad_ctx AD)))
    (h8 : Cu = H)
    (h9 : i ≠ 0)
    (h10 : (cx_used c) = 0) :
    (cx_pused c) = 0 := by
  lia

-- openssl/bndiv: lib/BnP/W_fuzz.v (assert)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (B : Int)
    (bv_unsigned : word → Int)
    (alloc_ceiling : Int)
    (GLOBALS_TOP : Int)
    (h1 : alloc_ceiling ≤ lo)
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : lo ≤ ((bv_unsigned sp) - (64 + 32768)))
    (h4 : (bv_unsigned sp) ≤ B)
    (h5 : ((bv_unsigned sp) % 16) = 0)
    (h6 : lo ≤ (((bv_unsigned sp) + (-64)) - 16)) :
    ((bv_unsigned sp) + (-64)) ≤ (bv_unsigned sp) := by
  lia

-- openssl/bndiv: lib/BnU/W_top.v (replace)
example
    {T1 T2 : Type}
    (D : Int)
    (bn_top : T1 → Nat)
    (b : T1)
    (length : T2 → Nat)
    (wlimbs : T2 → T2)
    (bn_buf : T1 → T2)
    (bn_dmax : T1 → Nat)
    (h1 : (((length (wlimbs (bn_buf b))) : Nat) : Int) = (((bn_dmax b) : Nat) : Int))
    (h2 : (0 < (((bn_top b) : Nat) : Int) → (0 < D ∧ ((D % 8) = 0 ∧ (D + (8 * (((length (bn_buf b)) : Nat) : Int))) ≤ (2 ^ (47 : Nat))))))
    (h3 : (bn_top b) = 0) :
    (D + (8 * (((bn_top b) : Nat) : Int))) = ((8 * (((bn_top b) : Nat) : Int)) + D) := by
  lia

-- openssl/bndiv: lib/BnW/BnKaraPX.v (replace)
example
    {T1 T2 : Type}
    (k : Nat)
    (n : Nat)
    (length : T1 → Nat)
    (firstn : Nat → T2 → T1)
    (a : T2)
    (b : T2)
    (slice : T2 → Nat → Nat → T1)
    (tna : Nat)
    (tnb : Nat)
    (lval : T1 → Int)
    (Bp : Nat → Int)
    (rh1 : T1)
    (h1 : 16 ≤ n)
    (h2 : (length (firstn n a)) = n)
    (h3 : (length (firstn n b)) = n)
    (h4 : (length (slice a n tna)) = tna)
    (h5 : (length (slice b n tnb)) = tnb)
    (h6 : (0 ≤ (lval (slice a n tna)) ∧ (lval (slice a n tna)) < (Bp n)))
    (h7 : (0 ≤ (lval (slice b n tnb)) ∧ (lval (slice b n tnb)) < (Bp n)))
    (h8 : n = (2 * (2 ^ (k - 1))))
    (h9 : (length rh1) = (2 * n))
    (h10 : 16 ≤ (max tna tnb))
    (h11 : 1 ≤ (k - 1))
    (h12 : (2 ^ (k - 1)) = (2 * (2 ^ ((k - 1) - 1)))) :
    (((k - 1) - 1) + 1) = (k - 1) := by
  lia

-- openssl/bndiv: lib/BnW/BnKaraPX.v (replace)
example
    {T1 T2 : Type}
    (n : Nat)
    (length : T1 → Nat)
    (firstn : Nat → T1 → T1)
    (a : T1)
    (b : T1)
    (slice : T1 → Nat → Nat → T1)
    (tna : Nat)
    (tnb : Nat)
    (lval : T1 → Int)
    (Bp : Nat → Int)
    (splice : T1 → Int → T2 → T1)
    (t : T1)
    (t0 : T2)
    (td : T1)
    (mul_normal : T1 → T1 → T1)
    (Zs : T1)
    (r : T1)
    (mul_comba8 : T1 → T1 → T2)
    (h1 : 8 ≤ n)
    (h2 : (length (firstn n a)) = n)
    (h3 : (length (firstn n b)) = n)
    (h4 : (length (slice a n tna)) = tna)
    (h5 : (length (slice b n tnb)) = tnb)
    (h6 : (0 ≤ (lval (slice a n tna)) ∧ (lval (slice a n tna)) < (Bp n)))
    (h7 : (0 ≤ (lval (slice b n tnb)) ∧ (lval (slice b n tnb)) < (Bp n)))
    (h8 : (length (splice t 0 t0)) = (length t))
    (h9 : (length td) = (length t))
    (h10 : (length (mul_normal (slice a n tna) (slice b n tnb))) = (tna + tnb))
    (h11 : (length Zs) = (((2 * n) - tna) - tnb))
    (h12 : (length (splice r 0 (mul_comba8 (firstn n a) (firstn n b)))) = (length r)) :
    (4 * n) = (2 * (2 * n)) := by
  lia

-- openssl/bndiv: lib/HX/HxQuery.v (replace)
example
    {valuation int region list_kb T5 : Type}
    (rho : valuation)
    (t : int)
    (rg : region)
    (ks : list_kb)
    (off : Int)
    (rbase : valuation → int → region → Int)
    (i : Int)
    (kb_check : region → Int → list_kb → Bool)
    (length : list_kb → Nat)
    (to_Z : T5 → Int)
    (rg_size : region → T5)
    (bs : list_kb)
    (h1 : (kb_check rg off ks) = true)
    (h2 : 0 ≤ off)
    (h3 : (off + (((length ks) : Nat) : Int)) ≤ (to_Z (rg_size rg)))
    (h4 : (length bs) = (length ks)) :
    (((rbase rho t rg) + off) + i) = (((rbase rho t rg) + (off + 1)) + (i - 1)) := by
  lia

-- openssl/bndiv: lib/Spec/BnKaraCorrect.v (replace)
example
    {T1 : Type}
    (k' : Nat)
    (n : Nat)
    (length : T1 → Nat)
    (a_lo : T1)
    (b_lo : T1)
    (a_hi : T1)
    (tna : Nat)
    (b_hi : T1)
    (tnb : Nat)
    (lval : T1 → Int)
    (a : T1)
    (Bp : Nat → Int)
    (b : T1)
    (splice : T1 → Int → T1 → T1)
    (t : T1)
    (t0 : T1)
    (td : T1)
    (n2 : Nat)
    (mul_normal : T1 → T1 → T1)
    (Zs : T1)
    (r : T1)
    (mul_comba8 : T1 → T1 → T1)
    (p : T1)
    (rh : T1)
    (i : Nat)
    (h1 : 8 ≤ n)
    (h2 : (length a_lo) = n)
    (h3 : (length b_lo) = n)
    (h4 : (length a_hi) = tna)
    (h5 : (length b_hi) = tnb)
    (h6 : (lval a) = ((lval a_lo) + ((Bp n) * (lval a_hi))))
    (h7 : (lval b) = ((lval b_lo) + ((Bp n) * (lval b_hi))))
    (h8 : (0 ≤ (lval a_hi) ∧ (lval a_hi) < (Bp n)))
    (h9 : (0 ≤ (lval b_hi) ∧ (lval b_hi) < (Bp n)))
    (h10 : (length (splice t 0 t0)) = (length t))
    (h11 : (length td) = (length t))
    (h12 : n2 = 16)
    (h13 : (length (mul_normal a_hi b_hi)) = (tna + tnb))
    (h14 : (length Zs) = ((n2 - tna) - tnb))
    (h15 : (length (splice r 0 (mul_comba8 a_lo b_lo))) = (length r))
    (h16 : n = (2 * (2 ^ k')))
    (h17 : (length p) = ((length t) - (2 * n2)))
    (h18 : (length rh) = n2)
    (h19 : (4 * i) = n2)
    (h20 : 16 ≤ (max tna tnb))
    (h21 : 1 ≤ k')
    (h22 : i = (2 * (2 ^ (k' - 1)))) :
    ((k' - 1) + 1) = k' := by
  lia

-- openssl/bndiv: lib/VCommon/Ax/AsanSMemchr.v (assert)
example
    {list_Segment machine_state word list_byte T5 T6 T7 : Type}
    (segs : list_Segment)
    (b : Int)
    (cM : Int)
    (cH : Int)
    (wam : Int)
    (wlm : Int)
    (wah : Int)
    (wlh : Int)
    (ms0 : machine_state)
    (s : word)
    (bs : list_byte)
    (n : Int)
    (length : list_byte → Nat)
    (j : Int)
    (words_ok : list_Segment → Int → T5 → Bool)
    (MEMCHR_WORDS : T5)
    (Z_to_bv : Nat → Int → T6)
    (is_ecall : T6 → Bool)
    (const_ok : list_Segment → Int → T7 → Bool)
    (Mc : T7)
    (Hc : T7)
    (bv_unsigned : word → Int)
    (WE : Int)
    (rg : machine_state → Int → word)
    (h1 : (words_ok segs b MEMCHR_WORDS) = true)
    (h2 : (is_ecall (Z_to_bv 32 wam)) = false)
    (h3 : (is_ecall (Z_to_bv 32 wlm)) = false)
    (h4 : (is_ecall (Z_to_bv 32 wah)) = false)
    (h5 : (is_ecall (Z_to_bv 32 wlh)) = false)
    (h6 : (const_ok segs cM Mc) = true)
    (h7 : (const_ok segs cH Hc) = true)
    (h8 : (0 ≤ cM ∧ ((cM + 8) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ cH ∧ (cH + 8) ≤ (2 ^ (64 : Nat))))))
    (h9 : ((bv_unsigned s) + WE) ≤ (2 ^ (64 : Nat)))
    (h10 : (((((length bs) : Nat) : Int) + 8) ≤ n ∧ n < (2 ^ (64 : Nat))))
    (h11 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h12 : (((length bs) : Nat) : Int) < (j + 8))
    (h13 : (j + 8) ≤ (((length bs) : Nat) : Int)) :
    ((((length bs) : Nat) : Int) - (j + 8)) = (((((length bs) : Nat) : Int) - j) + ((-1) * 8)) := by
  lia

-- openssl/bndiv: lib/VCommon/Ax/AsanSMemchr.v (replace)
example
    {list_Segment machine_state word list_byte T5 T6 T7 : Type}
    (segs : list_Segment)
    (b : Int)
    (cM : Int)
    (cH : Int)
    (wam : Int)
    (wlm : Int)
    (wah : Int)
    (wlh : Int)
    (ms0 : machine_state)
    (s : word)
    (bs : list_byte)
    (n : Int)
    (bv_unsigned : word → Int)
    (j : Int)
    (words_ok : list_Segment → Int → T5 → Bool)
    (MEMCHR_WORDS : T5)
    (Z_to_bv : Nat → Int → T6)
    (is_ecall : T6 → Bool)
    (const_ok : list_Segment → Int → T7 → Bool)
    (Mc : T7)
    (Hc : T7)
    (WE : Int)
    (length : list_byte → Nat)
    (rg : machine_state → Int → word)
    (h1 : (words_ok segs b MEMCHR_WORDS) = true)
    (h2 : (is_ecall (Z_to_bv 32 wam)) = false)
    (h3 : (is_ecall (Z_to_bv 32 wlm)) = false)
    (h4 : (is_ecall (Z_to_bv 32 wah)) = false)
    (h5 : (is_ecall (Z_to_bv 32 wlh)) = false)
    (h6 : (const_ok segs cM Mc) = true)
    (h7 : (const_ok segs cH Hc) = true)
    (h8 : (0 ≤ cM ∧ ((cM + 8) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ cH ∧ (cH + 8) ≤ (2 ^ (64 : Nat))))))
    (h9 : ((bv_unsigned s) + WE) ≤ (2 ^ (64 : Nat)))
    (h10 : (((((length bs) : Nat) : Int) + 8) ≤ n ∧ n < (2 ^ (64 : Nat))))
    (h11 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h12 : (((length bs) : Nat) : Int) < (j + 8))
    (h13 : (j + 8) ≤ (((length bs) : Nat) : Int))
    (h14 : ((((length bs) : Nat) : Int) - (j + 8)) = (((((length bs) : Nat) : Int) - j) + ((-1) * 8))) :
    (((bv_unsigned s) + j) + (1 * 8)) = ((bv_unsigned s) + (j + 8)) := by
  lia

-- openssl/bndiv: lib/VCommon/Ax/AsanSMemchr.v (replace)
example
    {list_Segment machine_state word list_byte T5 T6 T7 : Type}
    (segs : list_Segment)
    (b : Int)
    (cM : Int)
    (cH : Int)
    (wam : Int)
    (wlm : Int)
    (wah : Int)
    (wlh : Int)
    (ms0 : machine_state)
    (s : word)
    (bs : list_byte)
    (n : Int)
    (bv_unsigned : word → Int)
    (j : Int)
    (words_ok : list_Segment → Int → T5 → Bool)
    (MEMCHR_WORDS : T5)
    (Z_to_bv : Nat → Int → T6)
    (is_ecall : T6 → Bool)
    (const_ok : list_Segment → Int → T7 → Bool)
    (Mc : T7)
    (Hc : T7)
    (WE : Int)
    (length : list_byte → Nat)
    (rg : machine_state → Int → word)
    (h1 : (words_ok segs b MEMCHR_WORDS) = true)
    (h2 : (is_ecall (Z_to_bv 32 wam)) = false)
    (h3 : (is_ecall (Z_to_bv 32 wlm)) = false)
    (h4 : (is_ecall (Z_to_bv 32 wah)) = false)
    (h5 : (is_ecall (Z_to_bv 32 wlh)) = false)
    (h6 : (const_ok segs cM Mc) = true)
    (h7 : (const_ok segs cH Hc) = true)
    (h8 : (0 ≤ cM ∧ ((cM + 8) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ cH ∧ (cH + 8) ≤ (2 ^ (64 : Nat))))))
    (h9 : ((bv_unsigned s) + WE) ≤ (2 ^ (64 : Nat)))
    (h10 : (((((length bs) : Nat) : Int) + 8) ≤ n ∧ n < (2 ^ (64 : Nat))))
    (h11 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h12 : (((bv_unsigned s) + (j + 1)) % 8) = 0)
    (h13 : (((bv_unsigned s) + (j + 1)) % 8) = ((((bv_unsigned s) + j) % 8) + 1)) :
    (((bv_unsigned s) + j) + 1) = ((bv_unsigned s) + (j + 1)) := by
  lia

-- openssl/bndiv: lib/VCommon/Ax/AsanWMemset.v (replace)
example
    {list_Segment machine_state word T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (n : Int)
    (c : word)
    (i : Int)
    (bv_unsigned : word → Int)
    (rg : machine_state → Int → word)
    (store_ok : list_Segment → T4 → T5 → Nat → Bool)
    (ms_mem : machine_state → T4)
    (Z_to_bv : Nat → Int → T5)
    (h1 : (bv_unsigned c) < 256)
    (h2 : 0 ≤ dst)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h6 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true) :
    ((dst + (i + 8)) + ((8 : Nat) : Int)) = (dst + (i + 16)) := by
  lia

-- openssl/bndiv: lib/VCommon/Ax/AxVal.v (replace)
example
    (lo : Int)
    (hi : Int)
    (u : Int)
    (i : Int)
    (k : Int)
    (two64 : Int)
    (Z_lxor : Int → Int → Int)
    (Zpow : Int → Int → Int)
    (Z_testbit : Int → Int → Bool)
    (h1 : (0 ≤ lo ∧ lo ≤ u))
    (h2 : (u ≤ hi ∧ hi < two64))
    (h3 : 0 ≤ k)
    (h4 : 0 ≤ (Z_lxor lo hi))
    (h5 : (Int.fdiv lo (Zpow 2 k)) = (Int.fdiv hi (Zpow 2 k)))
    (h6 : (Z_testbit (Z_lxor lo hi) (i + k)) = false)
    (h7 : (Int.fdiv u (Zpow 2 k)) = (Int.fdiv lo (Zpow 2 k))) :
    ((i - k) + k) = i := by
  lia

-- openssl/bndiv: lib/VCommon/Ax/AxVal.v (replace)
example
    {T1 : Type}
    (k : Int)
    (bv_unsigned : T1 → Int)
    (a : T1)
    (Zpow : Int → Int → Int)
    (h1 : (Int.fmod (bv_unsigned a) (Zpow 2 k)) = 0)
    (h2 : (bv_unsigned a) = ((Zpow 2 k) * (Int.fdiv (bv_unsigned a) (Zpow 2 k))))
    (h3 : (Int.fdiv (bv_unsigned a) (Zpow 2 k)) < (Zpow 2 (64 - k))) :
    64 = (k + (64 - k)) := by
  lia

-- openssl/bndiv: lib/VCommon/Ax/ExMem.v (replace)
example
    {region int : Type}
    (R : region)
    (x : int)
    (n : Nat)
    (to_Z : int → Int)
    (rg_lo : region → int)
    (i : Nat)
    (h1 : (to_Z (rg_lo R)) ≤ (to_Z x))
    (h2 : ((to_Z x) + ((n : Nat) : Int)) < (2 ^ (47 : Nat)))
    (h3 : ((to_Z x) - (to_Z (rg_lo R))) = ((8 * (((to_Z x) - (to_Z (rg_lo R))) / 8)) + (((to_Z x) - (to_Z (rg_lo R))) % 8)))
    (h4 : ((((to_Z x) + ((i : Nat) : Int)) - (to_Z (rg_lo R))) % 8) = ((((to_Z x) - (to_Z (rg_lo R))) % 8) + ((i : Nat) : Int)))
    (h5 : ((((to_Z x) + ((i : Nat) : Int)) - (to_Z (rg_lo R))) / 8) = (((to_Z x) - (to_Z (rg_lo R))) / 8)) :
    (((((to_Z x) - (to_Z (rg_lo R))) % 8) + ((i : Nat) : Int)) + ((((to_Z x) - (to_Z (rg_lo R))) / 8) * 8)) = (((to_Z x) + ((i : Nat) : Int)) - (to_Z (rg_lo R))) := by
  lia

-- openssl/bndiv: lib/VCommon/BootWitness/BootLayout.v (replace)
example
    {ProcInput T2 T3 : Type}
    (sp0 : Int)
    (inp : ProcInput)
    (strbytesZ : ProcInput → Int)
    (sp_window_lo : Int)
    (entry_stack_span : T2 → T3 → Int)
    (in_argv : ProcInput → T2)
    (in_envp : ProcInput → T3)
    (sp_window_hi : Int)
    (h1 : sp_window_lo ≤ sp0)
    (h2 : (sp0 + (entry_stack_span (in_argv inp) (in_envp inp))) ≤ sp_window_hi) :
    8 = (((strbytesZ inp) % 8) + (8 - ((strbytesZ inp) % 8))) := by
  lia

-- openssl/ct: lib/B/SegRw.v (replace)
example
    {T1 T2 T3 : Type}
    (bv_unsigned : T1 → Int)
    (b : T1)
    (bytes_le_to_Z : T2 → Int)
    (bs : T2)
    (Z_lor : Int → T3 → Int)
    (Z_shiftl : Int → Int → T3)
    (h1 : (Z_lor (bv_unsigned b) (Z_shiftl (bytes_le_to_Z bs) 8)) = ((bv_unsigned b) + (256 * (bytes_le_to_Z bs)))) :
    ((bv_unsigned b) + ((bytes_le_to_Z bs) * 256)) = ((bv_unsigned b) + (256 * (bytes_le_to_Z bs))) := by
  lia

-- openssl/ct: lib/CtB/D_trwalk.v (replace)
example
    {T1 : Type}
    (sp : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (bv_swrap : Int → Int → Int)
    (k : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 (sp - 80))) = (sp - 80))
    (h2 : (bv_swrap 32 ((bv_unsigned (Z_to_bv 64 k)) + (-1))) = (k - 1)) :
    sp = ((sp - 80) + 80) := by
  lia

-- openssl/ct: lib/CtB/F_snpf_dir.v (replace)
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
    (k2 : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (i : Int)
    (n3 : Nat)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 5685248)
    (h5 : ((6189768 ≤ Fp ∧ (Fp + 232) ≤ 6956608) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((12567160 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 12574720)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (i + 1) < (zlength fmt))
    (h12 : 0 ≤ ((k2 + 1) + ((n3 : Nat) : Int)))
    (h13 : (k2 + 2) < (zlength fmt)) :
    (A + (k2 + 2)) = ((A + k2) + 2) := by
  lia

-- openssl/ct: lib/CtB/F_snpf_dir.v (replace)
example
    {list_Z list_word T3 : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (k : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (i : Int)
    (d' : T3)
    (k2 : Int)
    (n3 : Nat)
    (d_w : T3 → Int)
    (k2' : Int)
    (k1 : Int)
    (length : list_word → Nat)
    (wv : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 5685248)
    (h5 : ((6189768 ≤ Fp ∧ (Fp + 232) ≤ 6956608) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((12567160 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 12574720)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (i + 1) < (zlength fmt))
    (h12 : 0 ≤ ((k2 + 1) + ((n3 : Nat) : Int)))
    (h13 : (k2 + 2) < (zlength fmt))
    (h14 : k2' = k2)
    (h15 : k2 = (k1 + 1))
    (h16 : (0 < Fp ∧ Fp < (2 ^ (64 : Nat))))
    (h17 : (Int.toNat k) < (length slots))
    (h18 : 0 ≤ wv)
    (h19 : wv = (d_w d')) :
    ((VA + (8 * k)) + 8) = (VA + (8 * (k + 1))) := by
  lia

-- openssl/ct: lib/CtB/F_snpf_dir.v (replace)
example
    {list_Z list_word T3 : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (k : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (i : Int)
    (d' : T3)
    (k2 : Int)
    (n3 : Nat)
    (d_w : T3 → Int)
    (k2' : Int)
    (k1 : Int)
    (length : list_word → Nat)
    (wv : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 5685248)
    (h5 : ((6189768 ≤ Fp ∧ (Fp + 232) ≤ 6956608) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((12567160 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 12574720)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (i + 1) < (zlength fmt))
    (h12 : 0 ≤ ((k2 + 1) + ((n3 : Nat) : Int)))
    (h13 : (k2 + 2) < (zlength fmt))
    (h14 : k2' = k2)
    (h15 : k2 = (k1 + 1))
    (h16 : (0 < Fp ∧ Fp < (2 ^ (64 : Nat))))
    (h17 : (Int.toNat k) < (length slots))
    (h18 : 0 ≤ wv)
    (h19 : wv = (d_w d'))
    (h20 : wv < 0)
    (h21 : (-wv) = (d_w d')) :
    ((VA + (8 * k)) + 8) = (VA + (8 * (k + 1))) := by
  lia

-- openssl/ct: lib/CtB/I_strncmpw.v (replace)
example
    {T1 : Type}
    (k : Nat)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (n : Int)
    (p1 : Int)
    (p2 : Int)
    (x : T1)
    (y : T1)
    (h1 : (bv_unsigned (Z_to_bv 64 ((k : Nat) : Int))) = ((k : Nat) : Int))
    (h2 : (bv_unsigned (Z_to_bv 64 (((k : Nat) : Int) + 1))) = (((k : Nat) : Int) + 1))
    (h3 : (bv_unsigned (Z_to_bv 64 n)) = n)
    (h4 : (bv_unsigned (Z_to_bv 64 p1)) = p1)
    (h5 : (bv_unsigned (Z_to_bv 64 p2)) = p2)
    (h6 : (bv_unsigned (Z_to_bv 64 (bv_unsigned x))) = (bv_unsigned x))
    (h7 : (bv_unsigned (Z_to_bv 64 (bv_unsigned y))) = (bv_unsigned y)) :
    (((k + 1) : Nat) : Int) = (((k : Nat) : Int) + 1) := by
  lia

-- openssl/ct: lib/CtColP/W_collect.v (replace)
example
    {word : Type}
    (sp : word)
    (B : Int)
    (bv_unsigned : word → Int)
    (OFS : Int)
    (h1 : (bv_unsigned sp) ≤ B)
    (h2 : B < (2 ^ (63 : Nat)))
    (h3 : ((bv_unsigned sp) % 16) = 0) :
    (((bv_unsigned sp) + OFS) + (-112)) = (((((bv_unsigned sp) + OFS) + (-144)) + 16) + 16) := by
  lia

-- openssl/ct: lib/CtColP/W_d2i_octet.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (Z_to_bv : Int → Int → T1)
    (h1 : ((-320) : Int) ≤ 0)
    (h2 : (((-320) % 16) : Int) = 0)
    (h3 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-128)))) = ((bv_unsigned sp) + (-128))) :
    ((bv_unsigned sp) + (-320)) = ((bv_unsigned sp) - ((320 : Nat) : Int)) := by
  lia

-- openssl/ct: lib/CtColP/W_d2i_octet.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (errno_addr : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (RATP : Int)
    (W_d2i_octet_D_CONS_STK : Int)
    (STK : Int)
    (lo : Int)
    (h1 : (errno_addr (Z_to_bv 64 RATP)) = 3069508)
    (h2 : W_d2i_octet_D_CONS_STK ≤ STK)
    (h3 : lo ≤ (((bv_unsigned sp) + (-320)) - STK))
    (h4 : 0 ≤ STK)
    (h5 : ((-320) : Int) ≤ 0)
    (h6 : (((-320) % 16) : Int) = 0)
    (h7 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-320)))) = ((bv_unsigned sp) + (-320))) :
    ((bv_unsigned sp) + (-320)) = (((bv_unsigned sp) + (-128)) - ((192 : Nat) : Int)) := by
  lia

-- openssl/ct: lib/CtColP/W_d2i_octet.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (errno_addr : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (RATP : Int)
    (W_d2i_octet_D_CONS_STK : Int)
    (STK : Int)
    (lo : Int)
    (h1 : (errno_addr (Z_to_bv 64 RATP)) = 3069508)
    (h2 : W_d2i_octet_D_CONS_STK ≤ STK)
    (h3 : lo ≤ (((bv_unsigned sp) + (-320)) - STK))
    (h4 : 0 ≤ STK)
    (h5 : ((-320) : Int) ≤ 0)
    (h6 : (((-320) % 16) : Int) = 0)
    (h7 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-320)))) = ((bv_unsigned sp) + (-320))) :
    ((bv_unsigned sp) + (-260)) = (((((((bv_unsigned sp) + (-320)) + 32) + 8) + 5) + 1) + 14) := by
  lia

-- openssl/ct: lib/CtEncP/W_i2o_list.v (replace)
example (P : Int) :
    (P + (1 + 32)) = (P + 33) := by
  lia

-- openssl/ct: lib/CtHXB/HxbHooks.v (replace)
example
    {int T2 : Type}
    (t : int)
    (n : int)
    (A : Int)
    (i : Int)
    (to_Z : int → Int)
    (rho : int → Int)
    (shsz : Int → Int)
    (two63 : Int)
    (rg_size : T2 → int)
    (ushadow_region : int → T2)
    (q : int)
    (d : Nat)
    (Zpow : Int → Int → Int)
    (h1 : (rho t) = A)
    (h2 : 0 ≤ A)
    (h3 : (A + (shsz (to_Z n))) < two63)
    (h4 : (0 < (to_Z n) ∧ (to_Z n) ≤ 64512))
    (h5 : (to_Z (rg_size (ushadow_region n))) < (2 ^ (62 : Nat)))
    (h6 : ((to_Z n) % 8) = 0)
    (h7 : ((to_Z n) % 8) ≠ 0)
    (h8 : (to_Z q) = ((to_Z n) / 8))
    (h9 : (i ≤ ((to_Z n) / 8) ∧ ((to_Z n) / 8) < (shsz (to_Z n))))
    (h10 : (((to_Z n) / 8) / 8) < (Zpow 2 ((d : Nat) : Int)))
    (h11 : (0 ≤ (((to_Z n) / 8) % 8) ∧ (((to_Z n) / 8) % 8) < 8))
    (h12 : (Zpow 2 ((((to_Z n) / 8) % 8) + 1)) ≤ (2 ^ (8 : Nat)))
    (h13 : (0 ≤ (i % 8) ∧ (i % 8) ≤ (((to_Z n) / 8) % 8)))
    (h14 : (0 ≤ (((to_Z n) % 8) * (Zpow 2 (8 * (((to_Z n) / 8) % 8)))) ∧ (((to_Z n) % 8) * (Zpow 2 (8 * (((to_Z n) / 8) % 8)))) < (2 ^ (62 : Nat))))
    (h15 : (i % 8) < (((to_Z n) / 8) % 8)) :
    ((8 * (i % 8)) + (8 * ((((to_Z n) / 8) % 8) - (i % 8)))) = (8 * (((to_Z n) / 8) % 8)) := by
  lia

-- openssl/ct: lib/CtHXP/HxpGetState.v (replace)
example
    {ap_env T2 : Type}
    (E : ap_env)
    (lo : Int)
    (sp0 : Int)
    (rho : T2 → Int)
    (T_MK : T2)
    (e_mk : ap_env → Int)
    (T_SA : T2)
    (e_sa : ap_env → Int)
    (T_ND : T2)
    (e_nd : ap_env → Int)
    (T_ES : T2)
    (e_es : ap_env → Int)
    (T_GSTK : T2)
    (GET_STATE_STACK : Int)
    (GLOBALS_TOP : Int)
    (alloc_ceiling : Int)
    (h1 : (rho T_MK) = (e_mk E))
    (h2 : (rho T_SA) = (e_sa E))
    (h3 : (rho T_ND) = (e_nd E))
    (h4 : (rho T_ES) = (e_es E))
    (h5 : (rho T_GSTK) = (sp0 - GET_STATE_STACK))
    (h6 : lo ≤ (sp0 - GET_STATE_STACK))
    (h7 : GLOBALS_TOP ≤ lo)
    (h8 : alloc_ceiling ≤ lo)
    (h9 : sp0 < (2 ^ (63 : Nat)))
    (h10 : (sp0 % 16) = 0) :
    sp0 = ((sp0 - 1024) + (64 * 16)) := by
  lia

-- openssl/ct: lib/CtMallocP/RF_aligned_H.v (replace)
example
    (last_idx : Int)
    (freeable : Int)
    (sc : Int)
    (maplen : Int)
    (mword : Int)
    (P : Int)
    (Z_shiftr : Int → Int → Int)
    (stride : Int)
    (size_class : Int → Int)
    (Z_land : Int → Int → Int)
    (h1 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h2 : (0 < P ∧ P < (2 ^ (63 : Nat))))
    (h3 : (Z_shiftr mword 12) = maplen)
    (h4 : stride = (16 * (size_class sc)))
    (h5 : sc < 48)
    (h6 : (Z_land mword 31) = last_idx)
    (h7 : stride = ((4096 * maplen) - 16))
    (h8 : (mword - (mword % 4096)) = (4096 * maplen)) :
    (((last_idx + (32 * freeable)) + (64 * sc)) + (maplen * 4096)) = (((last_idx + (32 * freeable)) + (64 * sc)) + (4096 * maplen)) := by
  lia

-- openssl/ct: lib/CtPrnP/W_bio_hex_string.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (lo : Int)
    (out : Int)
    (len : Int)
    (bs : list_byte)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : 3207168 ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 6656))
    (h3 : (bv_unsigned sp) < (2 ^ (63 : Nat)))
    (h4 : (0 < out ∧ ((out + 128) ≤ lo ∧ ((out + 128) ≤ 65536 ∨ 3207168 ≤ out))))
    (h5 : (0 < len ∧ len < (2 ^ (31 : Nat))))
    (h6 : (((length bs) : Nat) : Int) = len) :
    (bv_unsigned sp) = (((bv_unsigned sp) + (-128)) + ((128 : Nat) : Int)) := by
  lia

-- openssl/ct: lib/CtPrnP/W_sct_print_B1.v (replace)
example (x : Int) :
    (((Int.fmod x (2 ^ (32 : Nat))) - (2 ^ (31 : Nat))) + (1 * (2 ^ (32 : Nat)))) = ((Int.fmod x (2 ^ (32 : Nat))) + (2 ^ (31 : Nat))) := by
  lia

-- openssl/ct: lib/CtRepP/W_c2i_ibuf2.v (replace)
example
    {word list_Z list_byte : Type}
    (sp : word)
    (lo : Int)
    (D : Int)
    (d : list_Z)
    (cont : Int)
    (plen : Int)
    (r : Int)
    (C : Int)
    (PNEG : Int)
    (junk : list_byte)
    (i : Int)
    (bv_unsigned : word → Int)
    (zlength : list_Z → Int)
    (length : list_byte → Nat)
    (h1 : (0 ≤ lo ∧ lo ≤ ((bv_unsigned sp) - 16)))
    (h2 : (0 < D ∧ (D + (zlength d)) ≤ lo))
    (h3 : 0 ≤ cont)
    (h4 : (1 ≤ plen ∧ plen < (2 ^ (31 : Nat))))
    (h5 : (cont + plen) ≤ (zlength d))
    (h6 : (length junk) = (Int.toNat r))
    (h7 : (0 < C ∧ (C + r) ≤ lo))
    (h8 : ((D + (zlength d)) ≤ C ∨ (C + r) ≤ D))
    (h9 : ((bv_unsigned sp) ≤ PNEG ∧ (PNEG + 4) ≤ (2 ^ (63 : Nat)))) :
    ((D + cont) + (i + 1)) = (((D + cont) + i) + 1) := by
  lia

-- openssl/ct: lib/CtRepP/W_c2i_int.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (B : Int)
    (d : list_Z)
    (cont : Int)
    (plen : Int)
    (PV : Int)
    (PCONT : Int)
    (bv_unsigned : word → Int)
    (RATP : Int)
    (zlength : list_Z → Int)
    (errno_addr : word → Int)
    (Z_to_bv : Int → Int → word)
    (r : Int)
    (h1 : 0 < (zlength d))
    (h2 : 0 ≤ cont)
    (h3 : (0 ≤ plen ∧ plen < (2 ^ (31 : Nat))))
    (h4 : (cont + plen) ≤ (zlength d))
    (h5 : ((bv_unsigned sp) + 64) ≤ PV)
    (h6 : ((bv_unsigned sp) + 64) ≤ PCONT)
    (h7 : ((PV + 8) ≤ PCONT ∨ (PCONT + 8) ≤ PV))
    (h8 : (PV + 8) ≤ B)
    (h9 : (PCONT + 8) ≤ B)
    (h10 : (errno_addr (Z_to_bv 64 RATP)) = 3069508)
    (h11 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-64)))) = ((bv_unsigned sp) + (-64)))
    (h12 : ((r = plen ∨ (r = (plen - 1) ∧ 2 ≤ plen)) ∧ 1 ≤ r)) :
    ((bv_unsigned sp) + (-60)) = (((bv_unsigned sp) + (-64)) + 4) := by
  lia

-- openssl/ct: lib/CtRepP/W_get_object_walk.v (replace)
example (b : Int) (h1 : (0 ≤ b ∧ b < 256)) :
    (((b - 256) + (2 ^ (63 : Nat))) + (1 * (2 ^ (64 : Nat)))) = (((b - 256) + (1 * (2 ^ (64 : Nat)))) + (2 ^ (63 : Nat))) := by
  lia

-- openssl/ct: lib/CtRepP/W_get_object_walk.v (replace)
example
    {T1 T2 : Type}
    (D : Int)
    (op : Int)
    (Z_land : T1 → Int → Int)
    (znth : T2 → Int → T1)
    (d : T2)
    (h1 : (0 ≤ (Z_land (znth d op) 31) ∧ (Z_land (znth d op) 31) ≤ 31)) :
    ((D + (op + 1)) + 1) = ((D + op) + 2) := by
  lia

-- openssl/ct: lib/CtRtB/F_strcpyA.v (replace)
example (P : Int) (Q : Int) (h1 : (0 ≤ Q ∧ Q ≤ P)) :
    (min (Int.toNat Q) (Int.toNat P)) = (Int.toNat Q) := by
  lia

-- openssl/ct: lib/CtSctP/W_o2i_sct.v (replace)
example
    {T1 T2 T3 : Type}
    (p : Int)
    (c : T1)
    (to_bytes : T2 → T3)
    (slice : T1 → Int → Int → T2)
    (length : T3 → Nat)
    (h1 : (length (to_bytes (slice c (p + 1) 32))) = (Int.toNat 32)) :
    (p + 34) = ((p + 33) + 1) := by
  lia

-- openssl/ct: lib/CtSctP/W_o2i_sig.v (replace)
example
    {word sctr_bptr list_Z T4 : Type}
    (sp : word)
    (B : Int)
    (x : sctr_bptr)
    (c : list_Z)
    (D : Int)
    (p : Int)
    (len : Int)
    (PIN : Int)
    (RATP : Int)
    (zlength : list_Z → Int)
    (adr : T4 → Int)
    (sc_blk : sctr_bptr → T4)
    (SCT_SIZE : Int)
    (sc_version : sctr_bptr → Int)
    (bv_unsigned : word → Int)
    (errno_addr : word → Int)
    (Z_to_bv : Int → Int → word)
    (h1 : 0 < (zlength c))
    (h2 : 0 ≤ p)
    (h3 : 0 ≤ len)
    (h4 : (p + len) ≤ (zlength c))
    (h5 : ((D + (zlength c)) ≤ (adr (sc_blk x)) ∨ ((adr (sc_blk x)) + SCT_SIZE) ≤ D))
    (h6 : (sc_version x) = 0)
    (h7 : (bv_unsigned sp) ≤ PIN)
    (h8 : (PIN + 8) ≤ B)
    (h9 : (errno_addr (Z_to_bv 64 RATP)) = 3069508)
    (h10 : ((adr (sc_blk x)) + 104) ≤ ((bv_unsigned sp) - (64 + (((80 + 80) + 48) + 8192))))
    (h11 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-64)))) = ((bv_unsigned sp) + (-64))) :
    (p + 3) = ((p + 2) + 1) := by
  lia

-- openssl/ct: lib/CtSctP/W_o2i_sig.v (replace)
example
    {word sctr_bptr list_Z T4 T5 T6 : Type}
    (sp : word)
    (B : Int)
    (x : sctr_bptr)
    (c : list_Z)
    (D : Int)
    (p : Int)
    (len : Int)
    (PIN : Int)
    (siglen : Int)
    (RATP : Int)
    (zlength : list_Z → Int)
    (adr : T4 → Int)
    (sc_blk : sctr_bptr → T4)
    (SCT_SIZE : Int)
    (sc_version : sctr_bptr → Int)
    (bv_unsigned : word → Int)
    (errno_addr : word → Int)
    (Z_to_bv : Int → Int → word)
    (u16be : list_Z → Int → Int)
    (to_bytes : T5 → T6)
    (slice : list_Z → Int → Int → T5)
    (length : T6 → Nat)
    (C : Int)
    (h1 : 0 < (zlength c))
    (h2 : 0 ≤ p)
    (h3 : 0 ≤ len)
    (h4 : (p + len) ≤ (zlength c))
    (h5 : ((D + (zlength c)) ≤ (adr (sc_blk x)) ∨ ((adr (sc_blk x)) + SCT_SIZE) ≤ D))
    (h6 : (sc_version x) = 0)
    (h7 : (bv_unsigned sp) ≤ PIN)
    (h8 : (PIN + 8) ≤ B)
    (h9 : (errno_addr (Z_to_bv 64 RATP)) = 3069508)
    (h10 : ((adr (sc_blk x)) + 104) ≤ ((bv_unsigned sp) - (64 + (((80 + 80) + 48) + 8192))))
    (h11 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) + (-64)))) = ((bv_unsigned sp) + (-64)))
    (h12 : (u16be c (p + 2)) ≤ (len - 4))
    (h13 : (length (to_bytes (slice c (p + 4) siglen))) = (Int.toNat siglen))
    (h14 : (C + siglen) ≤ ((bv_unsigned sp) - (64 + (((80 + 80) + 48) + 8192)))) :
    (((D + p) + 4) + siglen) = ((D + p) + (len - ((len - 4) - siglen))) := by
  lia

-- openssl/ct: lib/CtTimeB/W_gentime_set_stringA.v (replace)
example
    (fq : Int)
    (i : Int)
    (h1 : ((2 ^ (63 : Nat)) : Int) = 9223372036854775808)
    (h2 : ((2 ^ (64 : Nat)) : Int) = 18446744073709551616)
    (h3 : ((fq + 32) % 8) = 0) :
    (fq + (52 + i)) = ((fq + 52) + i) := by
  lia

-- openssl/ct: lib/CtTimeP/TimeToTmDefs.v (assert)
example (k : Int) (h1 : (0 ≤ k ∧ k ≤ 11)) (h2 : k ≠ 1) :
    (k = 0 ∨ (k = 2 ∨ (k = 3 ∨ (k = 4 ∨ (k = 5 ∨ (k = 6 ∨ (k = 7 ∨ (k = 8 ∨ (k = 9 ∨ (k = 10 ∨ k = 11)))))))))) := by
  lia

-- openssl/ct: lib/Spec/MI_WCreate.v (replace)
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
    (h7 : (sc' < 48 → ((stride' ≤ (UNIT * (size_class sc')) ∨ 34 ≤ sc') ∧ ((last' = 0 → ((m_maplen mr') ≠ 0 ∧ 27 ≤ sc')) ∧ (stride' * cnt) < (2 ^ (20 : Nat))))))
    (h8 : (16 ≤ stride' ∧ (stride' % 16) = 0))
    (h9 : (0 ≤ (snd p) ∧ (Int.fmod (snd p) UNIT) = 0))
    (h10 : (0 ≤ (c_mmap_counter (s_ctx st')) ∧ (c_mmap_counter (s_ctx st')) < (2 ^ (32 : Nat))))
    (h11 : (stride' * 1) ≤ (stride' * i)) :
    ((snd b) + (14 - 16)) = ((snd b) - 2) := by
  lia

-- openssl/ct: lib/VCommon/Ax/AsanWMcM1.v (replace)
example
    {list_Segment Model machine_state T4 T5 T6 T7 T8 : Type}
    (segs : list_Segment)
    (model0 : Model)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (r : Int)
    (ms_mem : machine_state → T4)
    (Z_to_bv : Nat → Int → T5)
    (store_ok : list_Segment → T4 → T5 → Nat → Bool)
    (vm_backing_used : Model → Int)
    (length : T6 → Nat)
    (L : T6)
    (page_size : Int)
    (vm_limit : T7 → Int)
    (m_vmmaps : Model → T7)
    (bv_unsigned : T8 → Int)
    (rg : machine_state → Int → T8)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((vm_backing_used model0) + ((((length L) : Nat) : Int) * page_size)) ≤ (vm_limit (m_vmmaps model0)))
    (h9 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h10 : (0 ≤ r ∧ r < 32))
    (h11 : 0 ≤ k)
    (h12 : ((k + 4) + (r % 4)) = n) :
    ((((k + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) = (k + 4) := by
  lia

-- openssl/ct: lib/VCommon/Ax/AsanWMemcpyF1.v (replace)
example
    {list_Segment machine_state T3 T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (r : Int)
    (ms_mem : machine_state → T3)
    (Z_to_bv : Nat → Int → T4)
    (store_ok : list_Segment → T3 → T4 → Nat → Bool)
    (bv_unsigned : T5 → Int)
    (rg : machine_state → Int → T5)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h9 : (0 ≤ r ∧ r < 32))
    (h10 : 0 ≤ k)
    (h11 : ((k + 4) + (r % 4)) = n) :
    ((((k + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) = (k + 4) := by
  lia

-- openssl/ct: lib/VCommon/Ax/AsanWMemcpyF1.v (replace)
example
    {list_Segment machine_state T3 T4 T5 : Type}
    (segs : list_Segment)
    (ms0 : machine_state)
    (dst : Int)
    (src : Int)
    (n : Int)
    (k : Int)
    (r : Int)
    (ms_mem : machine_state → T3)
    (Z_to_bv : Nat → Int → T4)
    (store_ok : list_Segment → T3 → T4 → Nat → Bool)
    (bv_unsigned : T5 → Int)
    (rg : machine_state → Int → T5)
    (h1 : 0 ≤ dst)
    (h2 : 0 ≤ src)
    (h3 : 0 ≤ n)
    (h4 : (dst + n) ≤ (2 ^ (47 : Nat)))
    (h5 : (src + n) ≤ (2 ^ (47 : Nat)))
    (h6 : ((src + n) ≤ dst ∨ (dst + n) ≤ src))
    (h7 : (store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Int.toNat n)) = true)
    (h8 : ((bv_unsigned (rg ms0 1)) % 2) = 0)
    (h9 : (0 ≤ r ∧ r < 32))
    (h10 : 0 ≤ k)
    (h11 : ((k + 8) + (r % 8)) = n) :
    ((((((((k + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) + ((1 : Nat) : Int)) = (k + 8) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AG_RecycleModel.v (replace)
example
    {astate chunk T3 : Type}
    (st : astate)
    (ch : chunk)
    (region_beg : astate → Int → Int)
    (c : Int)
    (m : Int)
    (ch_primary : chunk → Bool)
    (as_cache_inited : astate → Bool)
    (Z_land : Int → Int → Int)
    (U : Int)
    (addr_is_in_mem : Int → Bool)
    (round_up : T3 → Int → Int)
    (ch_used : chunk → T3)
    (kNumClasses : Int)
    (class_size : Int → Int)
    (kChunkHeaderSize : Int)
    (p : Int)
    (ch_rz : chunk → Int)
    (class_of_addr : astate → Int → Int)
    (h1 : (ch_primary ch) = true)
    (h2 : (as_cache_inited st) = true)
    (h3 : ((Z_land U 7) = 0 ∧ ((addr_is_in_mem U) = true ∧ (addr_is_in_mem ((U + (round_up (ch_used ch) 8)) - 8)) = true)))
    (h4 : (0 ≤ c ∧ c < kNumClasses))
    (h5 : (class_size c) ≠ 0)
    (h6 : 1 ≤ c)
    (h7 : (m + kChunkHeaderSize) = U)
    (h8 : U = (p + (ch_rz ch)))
    (h9 : (p ≤ m ∧ m < (p + (class_size c))))
    (h10 : ((Int.fdiv (m - (region_beg st c)) (class_size c)) * (class_size c)) = (p - (region_beg st c)))
    (h11 : c = (class_of_addr st m)) :
    ((region_beg st c) + (m - (region_beg st c))) = m := by
  lia

-- openssl/echconfiglist_parser: lib/As/AS_AllocSec1.v (replace)
example
    {Model word list_Z depot T5 list___word_word : Type}
    (mo : Model)
    (sp : word)
    (lo : Int)
    (size : Int)
    (pa : Int)
    (nres : Int)
    (nch : Int)
    (r8 : Int)
    (nT : Int)
    (chunks : list_Z)
    (d : depot)
    (bv_unsigned : word → Int)
    (aceil : Int)
    (zlen : list_Z → Int)
    (d_ids : depot → Int)
    (d_frames : depot → Int)
    (d_nb : depot → Int)
    (d_sb : depot → Int)
    (vm_reserved : T5 → list___word_word)
    (m_vmmaps : Model → T5)
    (vm_maps : T5 → list___word_word)
    (region_free : list___word_word → word → word → Bool)
    (map_contains : list___word_word → word → word → Bool)
    (wz : Int → word)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 768) ≤ (bv_unsigned sp))
    (h3 : ((bv_unsigned sp) + 16) ≤ (2 ^ (47 : Nat)))
    (h4 : (64512 < size ∧ size < (2 ^ (32 : Nat))))
    (h5 : (0 ≤ r8 ∧ r8 < 8))
    (h6 : ((0 ≤ nch ∧ nch ≤ nres) ∧ (nres + 16384) ≤ (2 ^ (20 : Nat))))
    (h7 : (zlen chunks) = nch)
    (h8 : (1 ≤ nT ∧ nT ≤ 254))
    (h9 : (((d_ids d) + 1) < 65536 ∧ (((d_frames d) + nT) + 1) ≤ 131072))
    (h10 : (((d_nb d) + (16 * 65536)) ≤ lo ∧ ((d_sb d) + (8 * 131072)) ≤ lo))
    (h11 : (nch = nres → (map_contains (vm_maps (m_vmmaps mo)) (wz (pa + (8 * nres))) (wz 131072)) = true))
    (h12 : (nch = nres → (region_free (vm_reserved (m_vmmaps mo)) (wz (pa + (8 * nres))) (wz 131072)) = true)) :
    ((bv_unsigned sp) + ((-8) * 16)) = ((bv_unsigned sp) + (-128)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AS_LargeAlloc.v (replace)
example
    {Model word list_Z T4 list___word_word T6 : Type}
    (mo : Model)
    (sp : word)
    (lo : Int)
    (size : Int)
    (msz : Int)
    (size8 : Int)
    (pa : Int)
    (nres : Int)
    (nch : Int)
    (chunks : list_Z)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (wz : Int → word)
    (zlen : list_Z → Int)
    (vm_reserved : T4 → list___word_word)
    (m_vmmaps : Model → T4)
    (vm_maps : T4 → list___word_word)
    (sh : Int → Int)
    (map_contains : list___word_word → word → word → Bool)
    (region_free : list___word_word → word → word → Bool)
    (Z_log2 : Int → Int)
    (a : Int)
    (mq : Int)
    (length : T6 → Nat)
    (wlist : list_Z → T6)
    (page_round_up_Z : Int → Int)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 464) ≤ (bv_unsigned sp))
    (h3 : ((bv_unsigned sp) + 16) ≤ (2 ^ (47 : Nat)))
    (h4 : (65536 < size ∧ (size ≤ (2 ^ (41 : Nat)) ∧ size = (8 * size8))))
    (h5 : ((0 ≤ nch ∧ nch ≤ nres) ∧ (nres + 16384) ≤ (2 ^ (20 : Nat))))
    (h6 : (zlen chunks) = nch)
    (h7 : (nch = nres → (map_contains (vm_maps (m_vmmaps mo)) (wz (pa + (8 * nres))) (wz 131072)) = true))
    (h8 : (nch = nres → (region_free (vm_reserved (m_vmmaps mo)) (wz (pa + (8 * nres))) (wz 131072)) = true))
    (h9 : nch = nres)
    (h10 : (16 ≤ (Z_log2 msz) ∧ (Z_log2 msz) ≤ 41))
    (h11 : (2148314624 ≤ (sh a) ∧ (((sh a) + (msz / 8)) ≤ 17594332446720 ∧ ((sh ((a + 4096) + size)) = (((sh a) + 512) + size8) ∧ (msz / 8) = (512 * mq)))))
    (h12 : ((pa + (8 * nres)) % 4096) = 0)
    (h13 : (12386304 ≤ a ∧ ((a + msz) ≤ aceil ∧ 140735332483072 ≤ aceil)))
    (h14 : (((length (wlist chunks)) : Nat) : Int) = nch)
    (h15 : (page_round_up_Z (bv_unsigned (wz 131072))) = 131072) :
    (pa + (8 * nch)) = (pa + (8 * nres)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AS_Refill1.v (replace)
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
    (P : Int)
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
    (FAB : Int)
    (take : Nat → list_Z → list_Z)
    (rf_mu' : Int → Int → Int → Int → Int)
    (rf_nnew : Int → Int → Int → Int → Int)
    (rf_mfa' : Int → Int → Int → Int → Int → Int)
    (rf_nf1 : Int → Int → Int → Int → Int)
    (rf_au' : Int → Int → Int → Int → Int)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 672) ≤ (bv_unsigned sp))
    (h3 : ((bv_unsigned sp) + 16) ≤ (2 ^ (47 : Nat)))
    (h4 : (1 ≤ c ∧ c ≤ 30))
    (h5 : CA = (TH + 208))
    (h6 : (AHI_LO ≤ sb ∧ ((sb + kSpaceSize) + kPageSize) ≤ aceil))
    (h7 : (11899400 ≤ (bv_unsigned tp) ∧ ((bv_unsigned tp) + 4096) ≤ AIMG_TOP))
    (h8 : (0 ≤ nf ∧ ((4 * nf) ≤ mfa ∧ mfa ≤ kFreeArraySize)))
    (h9 : ((0 ≤ au ∧ au ≤ mu) ∧ (mu + kUserMapSize) ≤ kFreeArrayOffset))
    (h10 : (length fl) = (Int.toNat nf))
    (h11 : (((length (wlist (rev fl))) : Nat) : Int) = nf)
    (h12 : n ≤ nf)
    (h13 : (AHI_LO ≤ FAB ∧ ((FAB + (4 * ((nf - n) + n))) ≤ aceil ∧ (FAB % 4096) = 0)))
    (h14 : (((length (wlist (rev (take (Int.toNat n) fl)))) : Nat) : Int) = n)
    (h15 : (rf_mu' c nf au mu) = mu)
    (h16 : (rf_nnew c nf au mu) = 0)
    (h17 : (rf_mfa' c nf mfa au mu) = mfa)
    (h18 : (rf_nf1 c nf au mu) = nf)
    (h19 : (rf_au' c nf au mu) = au) :
    ((P + 16) + 64) = (P + 80) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AS_Refill2.v (replace)
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
    (h2 : (lo + 672) ≤ (bv_unsigned sp))
    (h3 : ((bv_unsigned sp) + 16) ≤ (2 ^ (47 : Nat)))
    (h4 : (1 ≤ c ∧ c ≤ 30))
    (h5 : CA = (TH + 208))
    (h6 : (AHI_LO ≤ sb ∧ ((sb + kSpaceSize) + kPageSize) ≤ aceil))
    (h7 : (11899400 ≤ (bv_unsigned tp) ∧ ((bv_unsigned tp) + 4096) ≤ AIMG_TOP))
    (h8 : (0 ≤ nf ∧ ((4 * nf) ≤ mfa ∧ mfa ≤ kFreeArraySize)))
    (h9 : ((0 ≤ au ∧ au ≤ mu) ∧ (mu + kUserMapSize) ≤ kFreeArrayOffset))
    (h10 : (length fl) = (Int.toNat nf))
    (h11 : (((length (wlist (rev fl))) : Nat) : Int) = nf)
    (h12 : nf < n) :
    (R + 8) = (R + ((8 : Nat) : Int)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_Alloc4.v (replace)
example
    (needed : Int)
    (rz : Int)
    (size : Int)
    (rz_log : Int → Int)
    (Z_shiftl : Int → Int → Int)
    (h1 : (8 ≤ (max size 8) ∧ (size ≤ (max size 8) ∧ (max size 8) ≤ needed)))
    (h2 : ((0 ≤ (rz_log size) ∧ (rz_log size) ≤ 7) ∧ rz = (Z_shiftl 16 (rz_log size)))) :
    needed = ((needed - rz) + rz) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_LargeAlloc3.v (replace)
example
    {word list_Z T3 : Type}
    (sp : word)
    (lo : Int)
    (size : Int)
    (msz : Int)
    (a : Int)
    (pa : Int)
    (PS : Int)
    (BSL : Int)
    (nresv : Int)
    (nch : Int)
    (chunks : list_Z)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (zlen : list_Z → Int)
    (Z_log2 : Int → Int)
    (length : T3 → Nat)
    (wlist : list_Z → T3)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 416) ≤ (bv_unsigned sp))
    (h3 : (65536 < size ∧ size ≤ (2 ^ (41 : Nat))))
    (h4 : ((size + 4096) ≤ msz ∧ msz < (size + 8192)))
    (h5 : ((0 ≤ nch ∧ nch < nresv) ∧ nresv ≤ (2 ^ (20 : Nat))))
    (h6 : (zlen chunks) = nch)
    (h7 : PS = (pa + (8 * nch)))
    (h8 : BSL = (6765824 + (8 * (Z_log2 msz))))
    (h9 : (16 ≤ (Z_log2 msz) ∧ (Z_log2 msz) ≤ 41))
    (h10 : (aceil ≤ lo ∧ (12386304 ≤ a ∧ ((a + msz) ≤ aceil ∧ (12386304 ≤ pa ∧ ((pa + 8388608) ≤ aceil ∧ (140735332483072 ≤ aceil ∧ ((pa + (8 * nch)) = PS ∧ ((PS + 8) ≤ (pa + 8388608) ∧ (6765952 ≤ BSL ∧ (BSL + 8) ≤ 6766160))))))))))
    (h11 : (((length (wlist chunks)) : Nat) : Int) = nch) :
    8 = ((a + 32) - (a + 24)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_LargeAlloc3.v (replace)
example
    {word list_Z T3 : Type}
    (sp : word)
    (lo : Int)
    (size : Int)
    (msz : Int)
    (a : Int)
    (pa : Int)
    (PS : Int)
    (BSL : Int)
    (nresv : Int)
    (nch : Int)
    (chunks : list_Z)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (zlen : list_Z → Int)
    (Z_log2 : Int → Int)
    (length : T3 → Nat)
    (wlist : list_Z → T3)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 416) ≤ (bv_unsigned sp))
    (h3 : (65536 < size ∧ size ≤ (2 ^ (41 : Nat))))
    (h4 : ((size + 4096) ≤ msz ∧ msz < (size + 8192)))
    (h5 : ((0 ≤ nch ∧ nch < nresv) ∧ nresv ≤ (2 ^ (20 : Nat))))
    (h6 : (zlen chunks) = nch)
    (h7 : PS = (pa + (8 * nch)))
    (h8 : BSL = (6765824 + (8 * (Z_log2 msz))))
    (h9 : (16 ≤ (Z_log2 msz) ∧ (Z_log2 msz) ≤ 41))
    (h10 : (aceil ≤ lo ∧ (12386304 ≤ a ∧ ((a + msz) ≤ aceil ∧ (12386304 ≤ pa ∧ ((pa + 8388608) ≤ aceil ∧ (140735332483072 ≤ aceil ∧ ((pa + (8 * nch)) = PS ∧ ((PS + 8) ≤ (pa + 8388608) ∧ (6765952 ≤ BSL ∧ (BSL + 8) ≤ 6766160))))))))))
    (h11 : (((length (wlist chunks)) : Nat) : Int) = nch) :
    PS = (pa + (nch * 8)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_LargeAlloc3.v (replace)
example
    {word list_Z T3 : Type}
    (sp : word)
    (lo : Int)
    (size : Int)
    (msz : Int)
    (a : Int)
    (pa : Int)
    (PS : Int)
    (BSL : Int)
    (nresv : Int)
    (nch : Int)
    (chunks : list_Z)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (zlen : list_Z → Int)
    (Z_log2 : Int → Int)
    (length : T3 → Nat)
    (wlist : list_Z → T3)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 416) ≤ (bv_unsigned sp))
    (h3 : (65536 < size ∧ size ≤ (2 ^ (41 : Nat))))
    (h4 : ((size + 4096) ≤ msz ∧ msz < (size + 8192)))
    (h5 : ((0 ≤ nch ∧ nch < nresv) ∧ nresv ≤ (2 ^ (20 : Nat))))
    (h6 : (zlen chunks) = nch)
    (h7 : PS = (pa + (8 * nch)))
    (h8 : BSL = (6765824 + (8 * (Z_log2 msz))))
    (h9 : (16 ≤ (Z_log2 msz) ∧ (Z_log2 msz) ≤ 41))
    (h10 : (aceil ≤ lo ∧ (12386304 ≤ a ∧ ((a + msz) ≤ aceil ∧ (12386304 ≤ pa ∧ ((pa + 8388608) ≤ aceil ∧ (140735332483072 ≤ aceil ∧ ((pa + (8 * nch)) = PS ∧ ((PS + 8) ≤ (pa + 8388608) ∧ (6765952 ≤ BSL ∧ (BSL + 8) ≤ 6766160))))))))))
    (h11 : (((length (wlist chunks)) : Nat) : Int) = nch)
    (h12 : ((6766360 % 8) : Int) = 0)
    (h13 : ((0 : Int) ≤ 6766360 ∧ (6766360 : Int) < (2 ^ (64 : Nat))))
    (h14 : ((6766368 % 8) : Int) = 0)
    (h15 : ((0 : Int) ≤ 6766368 ∧ (6766368 : Int) < (2 ^ (64 : Nat)))) :
    (a + 24) = (a + ((24 : Nat) : Int)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_LargeAlloc4.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (size : Int)
    (msz : Int)
    (pa : Int)
    (nres : Int)
    (bv_unsigned : word → Int)
    (aceil : Int)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 464) ≤ (bv_unsigned sp))
    (h3 : (65536 < size ∧ size ≤ (2 ^ (41 : Nat))))
    (h4 : ((size + 4096) ≤ msz ∧ msz < (size + 8192)))
    (h5 : (0 ≤ nres ∧ (nres + 16384) ≤ (2 ^ (20 : Nat))))
    (h6 : ((pa + (8 * nres)) % 4096) = 0)
    (h7 : (aceil ≤ lo ∧ (12386304 ≤ pa ∧ ((pa + 8388608) ≤ aceil ∧ 140735332483072 ≤ aceil)))) :
    ((bv_unsigned sp) + (-192)) = (((bv_unsigned sp) + (-96)) + (-96)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_LargeDealloc1.v (replace)
example
    {T1 T2 : Type}
    (nch : Int)
    (length : T1 → Nat)
    (wlist : T2 → T1)
    (chunks : T2)
    (h1 : (((length (wlist chunks)) : Nat) : Int) = nch)
    (h2 : ((6766336 % 4) : Int) = 0)
    (h3 : ((0 : Int) ≤ 6766336 ∧ (6766336 : Int) < (2 ^ (64 : Nat)))) :
    (nch + (-1)) = (nch - 1) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_PoisonShadow.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (lo : Int)
    (addr : Int)
    (size : Int)
    (sbs : list_byte)
    (length : list_byte → Nat)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (AHI_LO : Int)
    (ALOWSH_LO : Int)
    (sh : Int → Int)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 64) ≤ (bv_unsigned sp))
    (h3 : (((AHI_LO ≤ addr ∧ (AHI_LO + 8) ≤ (addr + size)) ∨ (0 ≤ addr ∧ (8 ≤ (addr + size) ∧ (addr + size) ≤ ALOWSH_LO))) ∧ ((addr + size) ≤ aceil ∧ ((addr % 8) = 0 ∧ ((size % 8) = 0 ∧ 0 ≤ size)))))
    (h4 : (((length sbs) : Nat) : Int) = (size / 8))
    (h5 : (0 ≤ (sh addr) ∧ ((sh addr) + (size / 8)) ≤ 17594333495296)) :
    (length sbs) = (Int.toNat (size / 8)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_PoisonShadow.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (lo : Int)
    (addr : Int)
    (size : Int)
    (sbs : list_byte)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (AHI_LO : Int)
    (ALOWSH_LO : Int)
    (length : list_byte → Nat)
    (h1 : aceil ≤ lo)
    (h2 : (lo + 64) ≤ (bv_unsigned sp))
    (h3 : (((AHI_LO ≤ addr ∧ (AHI_LO + 8) ≤ (addr + size)) ∨ (0 ≤ addr ∧ (8 ≤ (addr + size) ∧ (addr + size) ≤ ALOWSH_LO))) ∧ ((addr + size) ≤ aceil ∧ ((addr % 8) = 0 ∧ ((size % 8) = 0 ∧ 0 ≤ size)))))
    (h4 : (((length sbs) : Nat) : Int) = (size / 8))
    (h5 : AHI_LO ≤ addr)
    (h6 : (AHI_LO ≤ addr ∧ (AHI_LO + 8) ≤ (addr + size))) :
    0 = (addr % 8) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AW_Rta2.v (replace)
example (D : Int) (i : Int) :
    4 = (((D + (4 * i)) + 4) - (D + (4 * i))) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AllocKit.v (replace)
example
    {T1 : Type}
    (st : T1)
    (c : Int)
    (off : Int)
    (as_space_beg : T1 → Int)
    (h1 : (0 ≤ c ∧ c < 32))
    (h2 : (0 ≤ off ∧ off < (2 ^ (32 : Nat)))) :
    (off + (c * (2 ^ (32 : Nat)))) = ((((as_space_beg st) + (c * (2 ^ (32 : Nat)))) + off) - (as_space_beg st)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AsDepotInv.v (replace)
example
    {T1 : Type}
    (d_nb : T1 → Int)
    (d : T1)
    (d_ids : T1 → Int)
    (id_1 : Int)
    (h1 : (1 ≤ id_1 ∧ id_1 ≤ (d_ids d))) :
    (((d_nb d) + (16 * ((d_ids d) + 1))) + 12) = (((d_nb d) + (16 * ((d_ids d) + 1))) + ((12 : Nat) : Int)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/AsScLib.v (replace)
example
    {word : Type}
    (x : word)
    (c1 : Int)
    (c2 : Int)
    (bv_unsigned : word → Int)
    (h1 : (Int.fmod (c1 - c2) (2 ^ (64 : Nat))) ≠ 0) :
    (((bv_unsigned x) + c1) - ((bv_unsigned x) + c2)) = (c1 - c2) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC13_entry.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (aceil : Int)
    (x : T2)
    (en_exts : T2 → Int)
    (h1 : aceil ≤ (bv_unsigned sp))
    (h2 : aceil ≤ ((bv_unsigned sp) + (-32)))
    (h3 : (0 ≤ (en_exts x) ∧ (en_exts x) < (2 ^ (64 : Nat)))) :
    (((bv_unsigned sp) + (-32)) + 16) = ((bv_unsigned sp) - 16) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC14_bio2buf_seg.v (replace)
example
    (Z_shiftr : Int → Int → Int)
    (ff : Int)
    (h1 : (0 ≤ (Z_shiftr ff 3) ∧ (Z_shiftr ff 3) ≤ ff)) :
    ((Z_shiftr ff 3) + 2147450888) = (((Z_shiftr ff 3) + 2147450880) + 8) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC14_entry_seg.v (replace)
example (src : Int) (Bb : Int) (i : Int) (ns : Int) (h1 : i = ns) (h2 : i < ns) :
    (Int.toNat (((src - Bb) + (4 * i)) + 0)) = (Int.toNat ((src - Bb) + (4 * i))) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC14_entry_seg.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (e3 : T1) (e2 : T1) :
    ((bv_unsigned e3) + (256 * (bv_unsigned e2))) = ((256 * (bv_unsigned e2)) + (bv_unsigned e3)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC14_fcc.v (replace)
example
    {asr word list_fframe libmid entrep list_____Z_Z_Z as_St_H T8 T9 : Type}
    (H : asr)
    (ra : word)
    (sp : word)
    (LF : list_fframe)
    (M : libmid)
    (lo : Int)
    (B : Int)
    (E : entrep)
    (rows : list_____Z_Z_Z)
    (sn : Int)
    (s00 : as_St_H)
    (M' : T8)
    (spent : Int)
    (r : Int)
    (d : Int)
    (en_nsuites : entrep → Int)
    (zlength : list_____Z_Z_Z → Int)
    (mid_flag : libmid → Int)
    (bv_unsigned : word → Int)
    (aceil : Int)
    (FCC_STACK : libmid → Int)
    (length : list_fframe → Nat)
    (mid_LF : libmid → Nat)
    (AFS_MAXLIVE : Nat)
    (FCC_COST : asr → libmid → Int → Int)
    (as_AL : asr → as_St_H → Int)
    (lb_bytes : T9 → Int)
    (mid_errblocks : libmid → T9)
    (as_Cf : asr → Int → Int)
    (VPM_SIZE : Int)
    (ADD1HOST_BYTES : Int)
    (FCC_SPENT : asr → libmid → T8 → Int → Int)
    (L2 : Int)
    (ls' : list_fframe)
    (h1 : (1 ≤ (en_nsuites E) ∧ (en_nsuites E) < (2 ^ (31 : Nat))))
    (h2 : (zlength rows) = (en_nsuites E))
    (h3 : (6 * (en_nsuites E)) ≤ sn)
    (h4 : (mid_flag M) = 1)
    (h5 : (bv_unsigned sp) ≤ B)
    (h6 : B < (2 ^ (64 : Nat)))
    (h7 : ((bv_unsigned sp) % 16) = 0)
    (h8 : aceil ≤ lo)
    (h9 : lo ≤ ((bv_unsigned sp) - (FCC_STACK M)))
    (h10 : ((bv_unsigned ra) % 2) = 0)
    (h11 : ((length LF) + (mid_LF M)) ≤ AFS_MAXLIVE)
    (h12 : (FCC_COST H M (en_nsuites E)) ≤ (as_AL H s00))
    (h13 : 0 ≤ (lb_bytes (mid_errblocks M)))
    (h14 : (r = 0 ∨ r = 1))
    (h15 : (spent + (as_Cf H (VPM_SIZE + ADD1HOST_BYTES))) ≤ (FCC_SPENT H M M' (en_nsuites E)))
    (h16 : (1 ≤ L2 ∧ L2 ≤ 255))
    (h17 : ((0 ≤ d ∧ d ≤ 1) ∧ d < L2))
    (h18 : (((length ls') : Nat) : Int) = (L2 - d)) :
    (((Int.toNat d) : Nat) : Int) = d := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC5_popfree.v (replace)
example
    {T1 : Type}
    (estack : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (lo : Int)
    (CFREE_STACK : Int)
    (aceil : Int)
    (spi : T1)
    (h1 : (lo ≤ ((((bv_unsigned sp) - 112) - 16) - estack) ∧ lo ≤ ((((bv_unsigned sp) - 112) - 16) - CFREE_STACK)))
    (h2 : 0 ≤ lo)
    (h3 : 0 ≤ CFREE_STACK)
    (h4 : aceil ≤ (bv_unsigned sp))
    (h5 : aceil ≤ ((bv_unsigned sp) + (-112)))
    (h6 : (bv_unsigned spi) = ((bv_unsigned sp) + (-112))) :
    (((bv_unsigned sp) + (-112)) + 96) = ((bv_unsigned sp) - 16) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC7_read.v (replace)
example
    {T1 T2 T3 : Type}
    (mb_len : T1 → Int)
    (R : T1)
    (mb_pos : T1 → Int)
    (mb_rdn : T1 → Int → Int)
    (outl : Int)
    (length : T2 → Nat)
    (mb_take : T1 → T3 → Int → T2)
    (ds : T3)
    (h1 : ((0 ≤ (mb_rdn R outl) ∧ (mb_rdn R outl) ≤ outl) ∧ (mb_rdn R outl) ≤ ((mb_len R) - (mb_pos R))))
    (h2 : (length (mb_take R ds (mb_rdn R outl))) = (Int.toNat (mb_rdn R outl))) :
    (((mb_len R) - (mb_pos R)) + (-(mb_rdn R outl))) = ((mb_len R) - ((mb_pos R) + (mb_rdn R outl))) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC8_block.v (replace)
example
    {list_byte : Type}
    (a : Int)
    (f0 : Int)
    (t : Int)
    (q : Int)
    (raw : list_byte)
    (tj : list_byte)
    (g : Int)
    (j : Nat)
    (aceil : Int)
    (length : list_byte → Nat)
    (ALOWSH_LO : Int)
    (AHI_LO : Int)
    (h1 : f0 = (a + 4))
    (h2 : (0 < a ∧ ((a % 16) = 0 ∧ (a + 92) ≤ aceil)))
    (h3 : ((t + (((length tj) : Nat) : Int)) ≤ ALOWSH_LO ∨ AHI_LO ≤ t))
    (h4 : (length raw) = 80)
    (h5 : (1 ≤ q ∧ q ≤ 16))
    (h6 : (3 * q) ≤ (((length tj) : Nat) : Int))
    (h7 : ((f0 + 80) ≤ t ∨ (t + (((length tj) : Nat) : Int)) ≤ f0))
    (h8 : (0 ≤ t ∧ (t + (((length tj) : Nat) : Int)) ≤ (2 ^ (64 : Nat))))
    (h9 : (0 ≤ g ∧ g < q)) :
    ((3 * (Int.toNat g)) + j) = ((Int.toNat (3 * g)) + j) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC8_block.v (replace)
example
    {list_byte : Type}
    (a : Int)
    (f0 : Int)
    (t : Int)
    (q : Int)
    (raw : list_byte)
    (tj : list_byte)
    (g : Int)
    (aceil : Int)
    (length : list_byte → Nat)
    (ALOWSH_LO : Int)
    (AHI_LO : Int)
    (h1 : f0 = (a + 4))
    (h2 : (0 < a ∧ ((a % 16) = 0 ∧ (a + 92) ≤ aceil)))
    (h3 : ((t + (((length tj) : Nat) : Int)) ≤ ALOWSH_LO ∨ AHI_LO ≤ t))
    (h4 : (length raw) = 80)
    (h5 : (1 ≤ q ∧ q ≤ 16))
    (h6 : (3 * q) ≤ (((length tj) : Nat) : Int))
    (h7 : ((f0 + 80) ≤ t ∨ (t + (((length tj) : Nat) : Int)) ≤ f0))
    (h8 : (0 ≤ t ∧ (t + (((length tj) : Nat) : Int)) ≤ (2 ^ (64 : Nat))))
    (h9 : (0 ≤ g ∧ g < q)) :
    (Int.toNat (4 * g)) = (4 * (Int.toNat g)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC8_block.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (t : Int)
    (length : T1 → Nat)
    (raw : T1)
    (a : Int)
    (aceil : Int)
    (q : Int)
    (map : T2 → T3 → T1)
    (b8 : T2)
    (groups_bytes : T4 → T3)
    (vs : Int → T1 → T4)
    (h1 : (length raw) = 80)
    (h2 : (0 < a ∧ ((a % 16) = 0 ∧ (a + 92) ≤ aceil)))
    (h3 : (length (map b8 (groups_bytes (vs q raw)))) = (3 * (Int.toNat q))) :
    t = (t + (3 * (1 - 1))) := by
  lia

-- openssl/echconfiglist_parser: lib/As/ECH_AC9_bioread.v (replace)
example
    (ff : Int)
    (ASHADOW_BASE : Int)
    (sh : Int → Int)
    (AHI_LO : Int)
    (h1 : (ASHADOW_BASE ≤ (sh ff) ∧ ((sh ff) + 8) < AHI_LO)) :
    (ff + 40) = ((ff + ((32 : Nat) : Int)) + ((8 : Nat) : Int)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/F_strcpy.v (replace)
example
    {T1 : Type}
    (D : Int)
    (j : Int)
    (length : T1 → Nat)
    (str : T1)
    (h1 : j = (((length str) : Nat) : Int))
    (h2 : j ≠ (((length str) : Nat) : Int)) :
    ((D + (j + 1)) + (-1)) = (D + j) := by
  lia

-- openssl/echconfiglist_parser: lib/As/F_strspn.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a0 : word)
    (str : list_byte)
    (acc : list_byte)
    (lo : Int)
    (spn : list_byte → list_byte → Nat)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : 2 ≤ (length acc))
    (h2 : 12386304 ≤ lo)
    (h3 : lo ≤ ((bv_unsigned sp) - 48))
    (h4 : ((bv_unsigned sp) + 8) ≤ (2 ^ (64 : Nat))) :
    (((spn str acc) : Nat) : Int) = (((bv_unsigned a0) + (((spn str acc) : Nat) : Int)) - (bv_unsigned a0)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/N6_imemcpy.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (src : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (aceil : Int)
    (AINTRIN_STACK : Int)
    (q1 : Int)
    (sh : Int → Int)
    (qj : list_byte)
    (h1 : (length src) = (Int.toNat (bv_unsigned a2)))
    (h2 : (((bv_unsigned a1) + (bv_unsigned a2)) ≤ (bv_unsigned a0) ∨ ((bv_unsigned a0) + (bv_unsigned a2)) ≤ (bv_unsigned a1)))
    (h3 : aceil ≤ lo)
    (h4 : lo ≤ ((bv_unsigned sp) - AINTRIN_STACK))
    (h5 : (bv_unsigned a2) ≤ (2 ^ (40 : Nat)))
    (h6 : (((bv_unsigned a0) + (bv_unsigned a2)) ≤ lo ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h7 : (((bv_unsigned a1) + (bv_unsigned a2)) ≤ lo ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h8 : (1 ≤ (bv_unsigned a2) ∧ (bv_unsigned a2) ≤ 64))
    (h9 : ((8 * q1) ≤ (sh (bv_unsigned a1)) ∧ (sh (((bv_unsigned a1) + (bv_unsigned a2)) - 1)) < ((8 * q1) + (((length qj) : Nat) : Int))))
    (h10 : (2147450880 ≤ (sh (bv_unsigned a1)) ∧ (sh (((bv_unsigned a1) + (bv_unsigned a2)) - 1)) < 17594333495296)) :
    (((bv_unsigned a1) + (bv_unsigned a2)) - 1) = (((bv_unsigned a1) + (bv_unsigned a2)) + (-1)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/N6_mem_is_zero.v (replace)
example
    {word : Type}
    (sp : word)
    (A : Int)
    (n : Int)
    (lo : Int)
    (i : Int)
    (bv_unsigned : word → Int)
    (h1 : (0 ≤ n ∧ n ≤ (2 ^ (40 : Nat))))
    (h2 : (lo + 16) ≤ (bv_unsigned sp))
    (h3 : ((A + n) ≤ lo ∨ (bv_unsigned sp) ≤ A))
    (h4 : ((A + n) + 8) ≤ (2 ^ (64 : Nat))) :
    ((A + (i + 1)) + 1) = ((A + i) + 2) := by
  lia

-- openssl/echconfiglist_parser: lib/As/N6_memset.v (replace)
example
    {word T2 : Type}
    (sp : word)
    (a0 : word)
    (a2 : word)
    (lo : Int)
    (q1 : Int)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (AINTRIN_STACK : Int)
    (sh : Int → Int)
    (length : T2 → Nat)
    (qj : T2)
    (h1 : aceil ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - AINTRIN_STACK))
    (h3 : (bv_unsigned a2) ≤ (2 ^ (40 : Nat)))
    (h4 : (((bv_unsigned a0) + (bv_unsigned a2)) ≤ lo ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h5 : (1 ≤ (bv_unsigned a2) ∧ (bv_unsigned a2) ≤ 64))
    (h6 : ((8 * q1) ≤ (sh (bv_unsigned a0)) ∧ (sh (((bv_unsigned a0) + (bv_unsigned a2)) - 1)) < ((8 * q1) + (((length qj) : Nat) : Int))))
    (h7 : (2147450880 ≤ (sh (bv_unsigned a0)) ∧ (sh (((bv_unsigned a0) + (bv_unsigned a2)) - 1)) < 17594333495296)) :
    ((8 * q1) + 8) = (8 * (q1 + 1)) := by
  lia

-- openssl/echconfiglist_parser: lib/As/N6_rip.v (replace)
example (a : Int) (n : Int) (h1 : (0 ≤ n ∧ n ≤ (2 ^ (40 : Nat)))) (h2 : 0 < n) :
    (a + n) = (n + a) := by
  lia

-- openssl/echconfiglist_parser: lib/As/N6_strncmp.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a1 : word)
    (e : list_Z)
    (t : list_Z)
    (n : Int)
    (lo : Int)
    (i : Int)
    (C1 : Int)
    (C2 : Int)
    (sh : Int → Int)
    (bv_unsigned : word → Int)
    (j : Int)
    (length : list_Z → Nat)
    (aceil : Int)
    (AINTRIN_STACK : Int)
    (zstrncmp : list_Z → list_Z → Nat → Int)
    (h1 : 0 ≤ n)
    (h2 : (((length e) : Nat) : Int) ≤ n)
    (h3 : aceil ≤ lo)
    (h4 : lo ≤ ((bv_unsigned sp) - AINTRIN_STACK))
    (h5 : n ≤ (2 ^ (40 : Nat)))
    (h6 : ((0 ≤ C1 ∧ C1 < 256) ∧ (0 ≤ C2 ∧ C2 < 256)))
    (h7 : ((0 ≤ i ∧ i ≤ n) ∧ (i ≤ (((length e) : Nat) : Int) ∧ i ≤ (((length t) : Nat) : Int))))
    (h8 : (((zstrncmp e t (Int.toNat n)) = 0 ↔ C1 = C2) ∧ ((zstrncmp e t (Int.toNat n)) < 0 ↔ C1 < C2)))
    (h9 : (1 ≤ (min (i + 1) n) ∧ (min (i + 1) n) ≤ 64))
    (h10 : (2147450880 ≤ (sh (bv_unsigned a1)) ∧ (sh (((bv_unsigned a1) + (min (i + 1) n)) - 1)) < 17594333495296)) :
    ((sh (bv_unsigned a1)) + (j + 1)) = (((sh (bv_unsigned a1)) + j) + 1) := by
  lia

-- openssl/echconfiglist_parser: lib/As/N6_strncmp.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (a1 : word)
    (e : list_Z)
    (t : list_Z)
    (n : Int)
    (lo : Int)
    (i : Int)
    (C1 : Int)
    (C2 : Int)
    (q1 : Int)
    (length : list_Z → Nat)
    (aceil : Int)
    (bv_unsigned : word → Int)
    (AINTRIN_STACK : Int)
    (zstrncmp : list_Z → list_Z → Nat → Int)
    (sh : Int → Int)
    (qj : list_Z)
    (h1 : 0 ≤ n)
    (h2 : (((length e) : Nat) : Int) ≤ n)
    (h3 : aceil ≤ lo)
    (h4 : lo ≤ ((bv_unsigned sp) - AINTRIN_STACK))
    (h5 : n ≤ (2 ^ (40 : Nat)))
    (h6 : ((0 ≤ C1 ∧ C1 < 256) ∧ (0 ≤ C2 ∧ C2 < 256)))
    (h7 : ((0 ≤ i ∧ i ≤ n) ∧ (i ≤ (((length e) : Nat) : Int) ∧ i ≤ (((length t) : Nat) : Int))))
    (h8 : (((zstrncmp e t (Int.toNat n)) = 0 ↔ C1 = C2) ∧ ((zstrncmp e t (Int.toNat n)) < 0 ↔ C1 < C2)))
    (h9 : (1 ≤ (min (i + 1) n) ∧ (min (i + 1) n) ≤ 64))
    (h10 : ((8 * q1) ≤ (sh (bv_unsigned a1)) ∧ (sh (((bv_unsigned a1) + (min (i + 1) n)) - 1)) < ((8 * q1) + (((length qj) : Nat) : Int))))
    (h11 : (2147450880 ≤ (sh (bv_unsigned a1)) ∧ (sh (((bv_unsigned a1) + (min (i + 1) n)) - 1)) < 17594333495296)) :
    ((8 * q1) + 8) = (8 * (q1 + 1)) := by
  lia

-- openssl/echconfiglist_parser: lib/AsMainIfaceDepot.v (replace)
example {env T2 T3 : Type} (E : env) (ps_b21 : T2 → Int) (Xof : T3 → env → T2) (g : T3) :
    ((ps_b21 (Xof g E)) + 16) = ((ps_b21 (Xof g E)) + (16 * 1)) := by
  lia

-- openssl/echconfiglist_parser: lib/Common/Br/BrKeep.v (replace)
example
    {T1 T2 : Type}
    (t : T1)
    (o : Int)
    (n : T2)
    (x : Int)
    (kf_wr : T1 → Int → T2 → Bool)
    (h1 : (kf_wr t o n) = true) :
    x = (o + (x - o)) := by
  lia

-- openssl/echconfiglist_parser: lib/Common/Br/BrPart.v (replace)
example
    {vtab itrie_region ttab T4 T5 : Type}
    (VT : vtab)
    (M : itrie_region)
    (TL : ttab)
    (a : T4)
    (n : T5)
    (P : Int)
    (o : Int)
    (tl_ok : vtab → itrie_region → ttab → Bool)
    (kzero_okP : T4 → T5 → Bool)
    (h1 : (tl_ok VT M TL) = true)
    (h2 : (kzero_okP a n) = true) :
    P = (o + (P - o)) := by
  lia

-- openssl/echconfiglist_parser: lib/Common/Cfg/LedgerCfg.v (replace)
example
    {T1 T2 : Type}
    (nZ : Int)
    (l : T1)
    (e_sz : T2 → Int)
    (p : T2)
    (live_bytes : T1 → Int)
    (length : T1 → Nat)
    (h1 : 0 ≤ nZ)
    (h2 : ((((e_sz p) + nZ) / 4096) + (((live_bytes l) + ((((length l) : Nat) : Int) * nZ)) / 4096)) ≤ ((((e_sz p) + (live_bytes l)) + (((((length l) : Nat) : Int) + 1) * nZ)) / 4096)) :
    (((e_sz p) + nZ) + ((live_bytes l) + ((((length l) : Nat) : Int) * nZ))) = (((e_sz p) + (live_bytes l)) + (((((length l) : Nat) : Int) + 1) * nZ)) := by
  lia

-- openssl/echconfiglist_parser: lib/Common/FX/FxSys.v (replace)
example {T1 : Type} (to_Z : T1 → Int) (pn : T1) (ci : T1) (j : Nat) :
    (((to_Z pn) * 4096) + (((to_Z ci) * 8) + ((j : Nat) : Int))) = ((((to_Z pn) * 4096) + ((to_Z ci) * 8)) + ((j : Nat) : Int)) := by
  lia

-- openssl/echconfiglist_parser: lib/Common/FX/FxSys.v (assert)
example
    {word int : Type}
    (a : word)
    (len : int)
    (to_Z : int → Int)
    (bv_unsigned : word → Int)
    (h1 : ((bv_unsigned a) % 4096) = 0)
    (h2 : 0 < (bv_unsigned a))
    (h3 : ((bv_unsigned a) + (to_Z len)) ≤ (2 ^ (47 : Nat))) :
    (to_Z len) ≤ (2 ^ (47 : Nat)) := by
  lia

-- openssl/echconfiglist_parser: lib/I2/FxHandoff2.v (replace)
example
    {fimage list_hfact T3 T4 T5 T6 : Type}
    (IM : fimage)
    (facts : list_hfact)
    (r : T3)
    (p : T4)
    (to_Z : T5 → Int)
    (pd_pn : T4 → T5)
    (ci : T5)
    (j : Nat)
    (page_ok_b2 : fimage → list_hfact → T3 → T4 → Bool)
    (blim : T6 → T5 → Int)
    (region_of : T3 → T6)
    (plim : T3 → T5 → T5)
    (h1 : (page_ok_b2 IM facts r p) = true)
    (h2 : (blim (region_of r) (pd_pn p)) = (8 * (to_Z (plim r (pd_pn p)))))
    (h3 : ((8 * (to_Z (plim r (pd_pn p)))) / 8) = (to_Z (plim r (pd_pn p)))) :
    ((((to_Z (pd_pn p)) * 4096) + ((to_Z ci) * 8)) + ((j : Nat) : Int)) = (((to_Z (pd_pn p)) * 4096) + (((to_Z ci) * 8) + ((j : Nat) : Int))) := by
  lia

-- openssl/echconfiglist_parser: lib/I2/I2Canon.v (replace)
example
    {T1 : Type}
    (k : Nat)
    (is_x0 : T1 → Bool)
    (Z_to_bv : Int → Int → T1)
    (h1 : (is_x0 (Z_to_bv 5 (((k : Nat) : Int) + 1))) = false) :
    k = (Int.toNat ((((k : Nat) : Int) + 1) - 1)) := by
  lia

-- openssl/echconfiglist_parser: lib/LazyRestrict.v (replace)
example (q2 : Int) (q1 : Int) (page_size : Int) :
    ((q2 - q1) * page_size) = ((q2 * page_size) - (q1 * page_size)) := by
  lia

-- openssl/echconfiglist_parser: lib/Ref/ECH_C7_read.v (replace)
example {T1 : Type} (mb_len : T1 → Int) (R : T1) (mb_pos : T1 → Int) (n : Int) :
    (((mb_len R) - (mb_pos R)) + (-n)) = ((mb_len R) - ((mb_pos R) + n)) := by
  lia

-- openssl/echconfiglist_parser: lib/Ref/ECH_C8_block.v (replace)
example
    {list_byte : Type}
    (f0 : Int)
    (t : Int)
    (q : Int)
    (raw : list_byte)
    (tj : list_byte)
    (g : Int)
    (j : Nat)
    (length : list_byte → Nat)
    (h1 : (length raw) = 80)
    (h2 : (1 ≤ q ∧ q ≤ 16))
    (h3 : (3 * q) ≤ (((length tj) : Nat) : Int))
    (h4 : ((f0 + 80) ≤ t ∨ (t + (((length tj) : Nat) : Int)) ≤ f0))
    (h5 : (0 ≤ f0 ∧ (f0 + 80) ≤ (2 ^ (64 : Nat))))
    (h6 : (0 ≤ t ∧ (t + (((length tj) : Nat) : Int)) ≤ (2 ^ (64 : Nat))))
    (h7 : (0 ≤ g ∧ g < q)) :
    ((3 * (Int.toNat g)) + j) = ((Int.toNat (3 * g)) + j) := by
  lia

-- openssl/echconfiglist_parser: lib/Ref/ECH_C8_update.v (replace)
example (inl : Int) (i : Int) :
    (inl - (i + 1)) = ((inl - i) - 1) := by
  lia

-- openssl/echconfiglist_parser: lib/Ref/RF_ntf.v (replace)
example
    {word aptr mstate T4 T5 T6 : Type}
    (lo : Int)
    (EH : Nat)
    (sp : word)
    (g : aptr)
    (p : aptr)
    (snd : aptr → Int)
    (hceil : Int)
    (bv_unsigned : word → Int)
    (get_meta_rec : mstate → aptr → T4)
    (stX : mstate)
    (m_last_idx : T4 → Int)
    (stG : mstate)
    (m_maplen : T4 → Int)
    (r : T5)
    (sstart_of : T4 → Int → Int)
    (g1 : aptr)
    (i1 : Int)
    (b1 : aptr)
    (get_stride : T4 → Int)
    (round_up_pg : T6 → Int)
    (r_len : T5 → T6)
    (h1 : hceil ≤ lo)
    (h2 : (lo + (96 * ((EH : Nat) : Int))) ≤ (bv_unsigned sp))
    (h3 : lo ≤ ((bv_unsigned sp) - 96))
    (h4 : (m_maplen (get_meta_rec stG g)) ≠ 0)
    (h5 : (m_maplen (get_meta_rec stG g)) = 0)
    (h6 : (snd p) = (sstart_of (get_meta_rec stX g1) i1))
    (h7 : ((snd b1) + 16) ≤ (snd p))
    (h8 : 0 ≤ ((get_stride (get_meta_rec stX g1)) * i1))
    (h9 : (0 ≤ ((snd p) - 4) ∧ (snd p) < (round_up_pg (r_len r))))
    (h10 : 0 ≤ ((get_stride (get_meta_rec stG g)) * ((m_last_idx (get_meta_rec stG g)) + 1))) :
    ((snd p) - 1) = (((snd p) + (-2)) + 1) := by
  lia

-- openssl/echconfiglist_parser: lib/Spec/KBudgetA.v (replace)
example
    {T1 T2 : Type}
    (st : T1)
    (gb : Int)
    (gk : Int)
    (mb : Int)
    (mk : Int)
    (c_meta_alloc_shift : T2 → Int)
    (ctx : T1 → T2)
    (Z_shiftl : Int → Int → Int)
    (PGSZ : Int)
    (mmap_len : Int → Int)
    (Zpow : Int → Int → Int)
    (h1 : 0 ≤ gb)
    (h2 : 0 ≤ gk)
    (h3 : 0 ≤ (c_meta_alloc_shift (ctx st)))
    (h4 : ((Z_shiftl 2 (c_meta_alloc_shift (ctx st))) * PGSZ) ≤ mb)
    (h5 : 1 ≤ mk)
    (h6 : (mmap_len ((Zpow 2 ((c_meta_alloc_shift (ctx st)) + 1)) * PGSZ)) = ((Zpow 2 ((c_meta_alloc_shift (ctx st)) + 1)) * PGSZ)) :
    (gk + (mk - 1)) = ((gk + mk) - 1) := by
  lia

-- openssl/echconfiglist_parser: lib/Ub/ECH_C14_entry_seg.v (replace)
example
    {T1 : Type}
    (rem : Int)
    (bv_unsigned : T1 → Int)
    (c0 : T1)
    (h1 : rem = 0)
    (h2 : 1 ≤ rem)
    (h3 : (1 + (bv_unsigned c0)) ≤ rem) :
    ((rem - 1) - (bv_unsigned c0)) = ((rem + (-1)) - (bv_unsigned c0)) := by
  lia

-- openssl/echconfiglist_parser: lib/Ub/ECH_C14_entry_seg.v (replace)
example (sq : Int) (Bb : Int) (i : Int) (ns : Int) (h1 : i = ns) (h2 : i < ns) :
    (Int.toNat (((sq - Bb) + (4 * i)) + 1)) = ((Int.toNat (((sq - Bb) + (4 * i)) + 0)) + 1) := by
  lia

-- openssl/echconfiglist_parser: lib/Ub/ECH_C14_fcc.v (replace)
example
    {hsr word list_block libmid entrep list_____Z_Z_Z T7 : Type}
    (H : hsr)
    (ra : word)
    (sp : word)
    (LB : list_block)
    (M : libmid)
    (lo : Int)
    (B : Int)
    (E : entrep)
    (rows : list_____Z_Z_Z)
    (sn : Int)
    (d : Int)
    (en_nsuites : entrep → Int)
    (zlength : list_____Z_Z_Z → Int)
    (mid_flag : libmid → Int)
    (lb_bytes : list_block → Int)
    (errph_bytes : T7 → Int)
    (mid_err : libmid → T7)
    (FCC_BYTES : Int)
    (ERRSTR_BYTES : Int)
    (hs_LIVE_MAX : hsr → Int)
    (length : list_block → Nat)
    (errph_cnt : T7 → Int)
    (FCC_CNT : Int)
    (ERRSTR_CNT : Int)
    (hs_LIVE_CNT_MAX : hsr → Int)
    (lb_big : list_block → Int)
    (errph_big : T7 → Int)
    (hs_LIVE_BIG_MAX : hsr → Int)
    (bv_unsigned : word → Int)
    (hceil : Int)
    (FCC_STACK : libmid → Int)
    (L2 : Int)
    (LL : Int)
    (ls' : list_block)
    (h1 : (1 ≤ (en_nsuites E) ∧ (en_nsuites E) < (2 ^ (31 : Nat))))
    (h2 : (zlength rows) = (en_nsuites E))
    (h3 : (6 * (en_nsuites E)) ≤ sn)
    (h4 : (mid_flag M) = 1)
    (h5 : ((((lb_bytes LB) + (errph_bytes (mid_err M))) + FCC_BYTES) + ERRSTR_BYTES) ≤ (hs_LIVE_MAX H))
    (h6 : ((((((length LB) : Nat) : Int) + (errph_cnt (mid_err M))) + FCC_CNT) + ERRSTR_CNT) ≤ (hs_LIVE_CNT_MAX H))
    (h7 : ((lb_big LB) + (errph_big (mid_err M))) ≤ (hs_LIVE_BIG_MAX H))
    (h8 : (bv_unsigned sp) ≤ B)
    (h9 : B < (2 ^ (64 : Nat)))
    (h10 : ((bv_unsigned sp) % 16) = 0)
    (h11 : hceil ≤ lo)
    (h12 : lo ≤ ((bv_unsigned sp) - (FCC_STACK M)))
    (h13 : ((bv_unsigned ra) % 2) = 0)
    (h14 : (1 ≤ L2 ∧ L2 ≤ 255))
    (h15 : (LL + 4) ≤ (2 ^ (64 : Nat)))
    (h16 : ((0 ≤ d ∧ d ≤ 1) ∧ d < L2))
    (h17 : (((length ls') : Nat) : Int) = (L2 - d)) :
    (((Int.toNat d) : Nat) : Int) = d := by
  lia

-- openssl/echconfiglist_parser: lib/Ub/ECH_C14_ladder.v (replace)
example (n : Int) (K : Int) :
    (n - (Int.fmod (-K) (2 ^ (64 : Nat)))) = (n + (-(Int.fmod (-K) (2 ^ (64 : Nat))))) := by
  lia

-- openssl/echconfiglist_parser: lib/Ub/ECH_C5_reserve.v (replace)
example
    {T1 T2 : Type}
    (A' : Int)
    (sk_cap : T1 → Int)
    (K : T1)
    (length : T2 → Nat)
    (sk_elems : T1 → T2)
    (sk_num : T1 → Int)
    (sk_grow : Int → Int)
    (h1 : (sk_num K) = 0)
    (h2 : (((length (sk_elems K)) : Nat) : Int) = (sk_cap K))
    (h3 : (5 * (sk_grow (sk_cap K))) ≤ ((sk_cap K) * 8)) :
    (A' + ((((Int.toNat (8 * (sk_cap K))) + 0) : Nat) : Int)) = (A' + (8 * (((length (sk_elems K)) : Nat) : Int))) := by
  lia

-- openssl/echconfiglist_parser: lib/Ub/ECH_C7_biofree.v (assert)
example (xa : Int) (q : Int) :
    (((xa + 4) ≤ q ∧ q < (xa + 8)) ∨ (¬ ((xa + 4) ≤ q ∧ q < (xa + 8)))) := by
  lia

-- openssl/echconfiglist_parser: lib/Ub/ECH_C8_block.v (replace)
example
    {list_byte : Type}
    (f0 : Int)
    (t : Int)
    (q : Int)
    (raw : list_byte)
    (tj : list_byte)
    (g : Int)
    (length : list_byte → Nat)
    (h1 : (length raw) = 80)
    (h2 : (1 ≤ q ∧ q ≤ 16))
    (h3 : (3 * q) ≤ (((length tj) : Nat) : Int))
    (h4 : ((f0 + 80) ≤ t ∨ (t + (((length tj) : Nat) : Int)) ≤ f0))
    (h5 : (0 < f0 ∧ (f0 + 80) ≤ (2 ^ (64 : Nat))))
    (h6 : (0 < t ∧ (t + (((length tj) : Nat) : Int)) ≤ (2 ^ (64 : Nat))))
    (h7 : (0 ≤ g ∧ g < q)) :
    (Int.toNat (4 * g)) = (4 * (Int.toNat g)) := by
  lia

-- openssl/echconfiglist_parser: lib/Ub/RF_realloc.v (replace)
example (i : Int) (bk_res : Int) :
    (i + ((min bk_res 5) * 32)) = (i + (32 * (min bk_res 5))) := by
  lia

-- openssl/hashtable: lib/Common/Cx/CxBits.v (assert)
example
    (V : Int)
    (m' : Int)
    (j : Int)
    (Zpow : Int → Int → Int)
    (Z_land : Int → Int → Int)
    (h1 : (0 ≤ V ∧ V < (2 ^ (64 : Nat))))
    (h2 : (0 < j ∧ j ≤ 63))
    (h3 : (((2 ^ (64 : Nat)) - (Zpow 2 j)) ≤ m' ∧ m' < (2 ^ (64 : Nat))))
    (h4 : 0 < (Zpow 2 j))
    (h5 : 0 ≤ m')
    (h6 : (Zpow 2 j) ≤ (2 ^ (64 : Nat)))
    (h7 : (Int.fmod (Z_land V m') (Zpow 2 j)) = (Z_land (Int.fmod V (Zpow 2 j)) (Int.fmod m' (Zpow 2 j))))
    (h8 : (Int.fdiv (Z_land V m') (Zpow 2 j)) = (Int.fdiv V (Zpow 2 j)))
    (h9 : (2 ^ (64 : Nat)) = ((Zpow 2 (64 - j)) * (Zpow 2 j))) :
    (((Zpow 2 (64 - j)) - 1) * (Zpow 2 j)) ≤ m' := by
  lia

-- openssl/hashtable: lib/Common/Cx/CxBits.v (assert)
example
    (V : Int)
    (m' : Int)
    (j : Int)
    (Zpow : Int → Int → Int)
    (Z_land : Int → Int → Int)
    (h1 : (0 ≤ V ∧ V < (2 ^ (64 : Nat))))
    (h2 : (0 < j ∧ j ≤ 63))
    (h3 : (((2 ^ (64 : Nat)) - (Zpow 2 j)) ≤ m' ∧ m' < (2 ^ (64 : Nat))))
    (h4 : 0 < (Zpow 2 j))
    (h5 : 0 ≤ m')
    (h6 : (Zpow 2 j) ≤ (2 ^ (64 : Nat)))
    (h7 : (Int.fmod (Z_land V m') (Zpow 2 j)) = (Z_land (Int.fmod V (Zpow 2 j)) (Int.fmod m' (Zpow 2 j))))
    (h8 : (Int.fdiv (Z_land V m') (Zpow 2 j)) = (Int.fdiv V (Zpow 2 j)))
    (h9 : (2 ^ (64 : Nat)) = ((Zpow 2 (64 - j)) * (Zpow 2 j)))
    (h10 : (((Zpow 2 (64 - j)) - 1) * (Zpow 2 j)) ≤ m') :
    m' < ((((Zpow 2 (64 - j)) - 1) + 1) * (Zpow 2 j)) := by
  lia

-- openssl/hashtable: lib/Common/Cx/CxBits.v (replace)
example
    (V : Int)
    (m' : Int)
    (j : Int)
    (Zpow : Int → Int → Int)
    (Z_land : Int → Int → Int)
    (h1 : (0 ≤ V ∧ V < (2 ^ (64 : Nat))))
    (h2 : (0 < j ∧ j ≤ 63))
    (h3 : (((2 ^ (64 : Nat)) - (Zpow 2 j)) ≤ m' ∧ m' < (2 ^ (64 : Nat))))
    (h4 : 0 < (Zpow 2 j))
    (h5 : 0 ≤ m')
    (h6 : (Zpow 2 j) ≤ (2 ^ (64 : Nat)))
    (h7 : (Int.fmod (Z_land V m') (Zpow 2 j)) = (Z_land (Int.fmod V (Zpow 2 j)) (Int.fmod m' (Zpow 2 j))))
    (h8 : (Int.fdiv (Z_land V m') (Zpow 2 j)) = (Int.fdiv V (Zpow 2 j)))
    (h9 : (2 ^ (64 : Nat)) = ((Zpow 2 (64 - j)) * (Zpow 2 j)))
    (h10 : (((Zpow 2 (64 - j)) - 1) * (Zpow 2 j)) ≤ m')
    (h11 : m' < ((((Zpow 2 (64 - j)) - 1) + 1) * (Zpow 2 j))) :
    64 = (j + (64 - j)) := by
  lia

-- openssl/hashtable: lib/Common/Cx/CxNodesArgSound.v (replace)
example
    {atable bv_32 T3 T4 T5 T6 word T8 T9 : Type}
    (A : atable)
    (nx0 : Nat)
    (ISP : Int)
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
    (E : T3)
    (allkn : T4)
    (k : T4)
    (b : T5)
    (off : Int)
    (n : T6)
    (bv_unsigned : word → Int)
    (edenot : T3 → T5 → word)
    (wb : T5)
    (wk : Int)
    (CAP_expr_vars_lt : Nat → T8 → Bool)
    (e_spw : T8)
    (g_istrlen : T9 → Int)
    (G : T9)
    (is_ecall : bv_32 → Bool)
    (L0 : Int)
    (STR1 : Int)
    (L1 : Int)
    (img_lo : atable → Int)
    (g_ro_lo : T9 → Int)
    (g_ro_hi : T9 → Int)
    (img_hi : atable → Int)
    (kwritable_x : T4 → T4 → T5 → Int → T6 → Bool)
    (h1 : (CAP_expr_vars_lt nx0 e_spw) = true)
    (h2 : (0 ≤ (g_istrlen G) ∧ ((g_istrlen G) + 28) < (2 ^ (64 : Nat))))
    (h3 : ((is_ecall wi0) = false ∧ ((is_ecall wi1) = false ∧ ((is_ecall wi2) = false ∧ ((is_ecall wi3) = false ∧ ((is_ecall wi4) = false ∧ ((is_ecall wi5) = false ∧ (is_ecall wi6) = false)))))))
    (h4 : (140735340871680 ≤ usp ∧ ((usp + 192) ≤ STR0 ∧ (((STR0 + L0) + 1) ≤ TOP ∧ ((2 ≤ argc → ((STR1 + L1) + 1) ≤ TOP) ∧ ((TOP % 8) = 0 ∧ ((TOP + 16) ≤ (2 ^ (47 : Nat)) ∧ (L0 ≤ 131071 ∧ (L1 ≤ 131071 ∧ (1 ≤ argc ∧ argc ≤ 1024))))))))))
    (h5 : ISP = usp)
    (h6 : ((img_lo A) ≤ (g_ro_lo G) ∧ (g_ro_hi G) ≤ (img_hi A)))
    (h7 : (kwritable_x allkn k b off n) = true) :
    (((bv_unsigned (edenot E wb)) + wk) + (((bv_unsigned (edenot E b)) + off) - ((bv_unsigned (edenot E wb)) + wk))) = ((bv_unsigned (edenot E b)) + off) := by
  lia

-- openssl/hashtable: lib/Common/Cx/CxNodesArgSound.v (replace)
example
    {list_Segment atable bv_32 T4 T5 T6 T7 word T9 T10 T11 : Type}
    (SEGS : list_Segment)
    (A : atable)
    (nx0 : Nat)
    (ISP : Int)
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
    (E : T4)
    (M : T5)
    (allkn : T6)
    (k : T6)
    (b : T7)
    (off : Int)
    (n : Int)
    (bv_unsigned : word → Int)
    (edenot : T4 → T7 → word)
    (wb : T7)
    (wk : Int)
    (CAP_expr_vars_lt : Nat → T9 → Bool)
    (e_spw : T9)
    (g_istrlen : T10 → Int)
    (G : T10)
    (Z_to_bv : Int → Int → word)
    (is_ecall : bv_32 → Bool)
    (L0 : Int)
    (STR1 : Int)
    (L1 : Int)
    (img_lo : atable → Int)
    (g_ro_lo : T10 → Int)
    (g_ro_hi : T10 → Int)
    (img_hi : atable → Int)
    (kwritable : T6 → T6 → T7 → Int → Int → Bool)
    (elenZ : T4 → T11 → Int)
    (wn : T11)
    (store_ok : list_Segment → T5 → word → Nat → Bool)
    (h1 : (CAP_expr_vars_lt nx0 e_spw) = true)
    (h2 : (0 ≤ (g_istrlen G) ∧ ((g_istrlen G) + 28) < (2 ^ (64 : Nat))))
    (h3 : ((is_ecall wi0) = false ∧ ((is_ecall wi1) = false ∧ ((is_ecall wi2) = false ∧ ((is_ecall wi3) = false ∧ ((is_ecall wi4) = false ∧ ((is_ecall wi5) = false ∧ (is_ecall wi6) = false)))))))
    (h4 : (140735340871680 ≤ usp ∧ ((usp + 192) ≤ STR0 ∧ (((STR0 + L0) + 1) ≤ TOP ∧ ((2 ≤ argc → ((STR1 + L1) + 1) ≤ TOP) ∧ ((TOP % 8) = 0 ∧ ((TOP + 16) ≤ (2 ^ (47 : Nat)) ∧ (L0 ≤ 131071 ∧ (L1 ≤ 131071 ∧ (1 ≤ argc ∧ argc ≤ 1024))))))))))
    (h5 : ISP = usp)
    (h6 : ((img_lo A) ≤ (g_ro_lo G) ∧ (g_ro_hi G) ≤ (img_hi A)))
    (h7 : (kwritable allkn k b off n) = true)
    (h8 : 0 ≤ n)
    (h9 : (((bv_unsigned (edenot E wb)) + wk) ≤ ((bv_unsigned (edenot E b)) + off) → ((((bv_unsigned (edenot E b)) + off) + n) ≤ (((bv_unsigned (edenot E wb)) + wk) + (elenZ E wn)) → ((store_ok SEGS M (Z_to_bv 64 ((bv_unsigned (edenot E b)) + off)) (Int.toNat n)) = true ∧ (0 ≤ ((bv_unsigned (edenot E b)) + off) ∧ (((bv_unsigned (edenot E b)) + off) + n) ≤ (2 ^ (64 : Nat))))))) :
    (((bv_unsigned (edenot E wb)) + wk) + (((bv_unsigned (edenot E b)) + off) - ((bv_unsigned (edenot E wb)) + wk))) = ((bv_unsigned (edenot E b)) + off) := by
  lia

-- openssl/hashtable: lib/Common/Cx/CxNodesRPSound.v (replace)
example
    {word T2 : Type}
    (nx0 : Nat)
    (spw : word)
    (bv_unsigned : word → Int)
    (CAP_expr_vars_lt : Nat → T2 → Bool)
    (e_spw : T2)
    (h1 : (CAP_expr_vars_lt nx0 e_spw) = true)
    (h2 : 72 ≤ (bv_unsigned spw)) :
    (((bv_unsigned spw) - 72) + (1 * (2 ^ (64 : Nat)))) = ((bv_unsigned spw) + ((2 ^ (64 : Nat)) - 72)) := by
  lia

-- openssl/hashtable: lib/Common/Cx/CxPlanSound.v (assert)
example
    {T1 T2 T3 word T5 : Type}
    (nx0 : Nat)
    (E : T1)
    (k : T2)
    (a : T3)
    (e : T3)
    (bv_unsigned : word → Int)
    (edenot : T1 → T3 → word)
    (CAP_expr_vars_lt : Nat → T5 → Bool)
    (e_spw : T5)
    (respell_ok : T2 → T3 → T3 → Bool)
    (h1 : (CAP_expr_vars_lt nx0 e_spw) = true)
    (h2 : (respell_ok k a e) = true)
    (h3 : (Int.fmod ((bv_unsigned (edenot E a)) - (bv_unsigned (edenot E e))) (2 ^ (64 : Nat))) = 0) :
    (Int.fmod ((bv_unsigned (edenot E a)) - (bv_unsigned (edenot E e))) (2 ^ (64 : Nat))) = 0 := by
  lia

-- openssl/hashtable: lib/HA/HARpU.v (replace)
example
    {T1 : Type}
    (nx0 : Nat)
    (q : Int)
    (uu : Int)
    (bk : Int)
    (n : Int)
    (CAP_expr_vars_lt : Nat → T1 → Bool)
    (e_spw : T1)
    (usp : Int)
    (beg : Int)
    (Q : Int)
    (bbu : Int)
    (h1 : (CAP_expr_vars_lt nx0 e_spw) = true)
    (h2 : Q = (usp - 72))
    (h3 : beg = ((bbu + uu) + bk))
    (h4 : (Int.fmod (beg - (bbu + uu)) (2 ^ (64 : Nat))) = ((beg - (bbu + uu)) + (2 ^ (64 : Nat))))
    (h5 : (beg / 8) = (q + ((uu + bk) / 8)))
    (h6 : (((beg + n) - 1) / 8) = (q + ((((uu + bk) + n) - 1) / 8))) :
    ((q * 8) + (((uu + bk) + n) - 1)) = (((((8 * q) + uu) + bk) + n) - 1) := by
  lia

-- openssl/hashtable: lib/HA/HARpU.v (assert)
example
    {T1 : Type}
    (nx0 : Nat)
    (q : Int)
    (bk : Int)
    (ulo : Int)
    (beg : Int)
    (CAP_expr_vars_lt : Nat → T1 → Bool)
    (e_spw : T1)
    (n : Int)
    (usp : Int)
    (Q : Int)
    (bbu : Int)
    (uu : Int)
    (uhi : Int)
    (nhi : Int)
    (h1 : (CAP_expr_vars_lt nx0 e_spw) = true)
    (h2 : Q = (usp - 72))
    (h3 : beg = ((bbu + uu) + bk))
    (h4 : (Int.fmod (beg - (bbu + uu)) (2 ^ (64 : Nat))) = ((beg - (bbu + uu)) + (2 ^ (64 : Nat))))
    (h5 : (beg / 8) = (q + ((uu + bk) / 8)))
    (h6 : (((beg + n) - 1) / 8) = (q + ((((uu + bk) + n) - 1) / 8)))
    (h7 : ((((uu + bk) + n) - 1) / 8) ≤ ((((bk + uhi) + nhi) - 1) / 8))
    (h8 : ((bk + ulo) / 8) ≤ ((uu + bk) / 8))
    (h9 : (bbu / 8) = q)
    (h10 : 0 ≤ q)
    (h11 : (q + ((bk + ulo) / 8)) < (2 ^ (61 : Nat))) :
    (q + ((bk + ulo) / 8)) ≤ (beg / 8) := by
  lia

-- openssl/hashtable: lib/T/hashtable/H0PilotOOM.v (replace)
example
    {word list_byte list_list_byte : Type}
    (sp0 : word)
    (a0s : list_byte)
    (path : list_byte)
    (envv : list_list_byte)
    (tid : word)
    (vals : list_byte)
    (bv_unsigned : word → Int)
    (p1 : word → list_byte → list_byte → list_list_byte → word)
    (length : list_byte → Nat)
    (path_has_slash : list_byte → Bool)
    (path_is_dirref : list_byte → Bool)
    (vals' : list_byte)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h2 : (bv_unsigned sp0) ≤ (bv_unsigned (p1 sp0 a0s path envv)))
    (h3 : (((bv_unsigned (p1 sp0 a0s path envv)) + (((length path) : Nat) : Int)) + 1) ≤ 140737488355328)
    (h4 : (path_has_slash path) = false)
    (h5 : (path_is_dirref path) = false)
    (h6 : (length path) ≤ 4095)
    (h7 : (length vals) = 74)
    (h8 : (length vals') = 106) :
    ((bv_unsigned sp0) + (-272)) = (((bv_unsigned sp0) - 128) - 144) := by
  lia

-- openssl/hashtable: lib/T/hashtable/H0ReadF1.v (replace)
example
    {word list_byte T3 : Type}
    (sp0 : word)
    (content : list_byte)
    (B : word)
    (bv_unsigned : word → Int)
    (L : Int)
    (length : list_byte → Nat)
    (vals : list_byte)
    (pref : Nat → T3 → list_byte)
    (dropz : Nat → list_byte → T3)
    (h1 : 33554432 ≤ L)
    (h2 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ 140737488355328))
    (h3 : L = (((length content) : Nat) : Int))
    (h4 : (length vals) = 42)
    (h5 : ((bv_unsigned B) + 33558528) ≤ ((bv_unsigned sp0) - 8388608))
    (h6 : (((length (pref 16777216 (dropz 16777216 content))) : Nat) : Int) = 16777216) :
    (((bv_unsigned B) + 176) + 16777216) = ((bv_unsigned B) + 16777392) := by
  lia

-- openssl/hashtable: lib/T/hashtable/H0ReadF1.v (replace)
example
    {word list_byte T3 : Type}
    (sp0 : word)
    (content : list_byte)
    (B : word)
    (length : list_byte → Nat)
    (pref : Nat → T3 → list_byte)
    (dropz : Nat → list_byte → T3)
    (L : Int)
    (bv_unsigned : word → Int)
    (vals : list_byte)
    (h1 : 67108864 ≤ L)
    (h2 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ 140737488355328))
    (h3 : L = (((length content) : Nat) : Int))
    (h4 : (length vals) = 42)
    (h5 : ((bv_unsigned B) + 67112960) ≤ ((bv_unsigned sp0) - 8388608))
    (h6 : (((length (pref 33554432 (dropz 33554432 content))) : Nat) : Int) = 33554432) :
    (Int.toNat 33554432) = (length (pref 33554432 (dropz 33554432 content))) := by
  lia

-- openssl/hashtable: lib/T/hashtable/H0ReadG1.v (replace)
example
    {word list_byte T3 T4 : Type}
    (sp0 : word)
    (mb : word)
    (content : list_byte)
    (B : word)
    (bv_unsigned : word → Int)
    (L : Int)
    (length : T3 → Nat)
    (vals : T3)
    (pref : Nat → T4 → T3)
    (dropz : Nat → list_byte → T4)
    (B' : word)
    (h1 : 524288 ≤ L)
    (h2 : 4096 ≤ (bv_unsigned mb))
    (h3 : ((bv_unsigned mb) + 8192) ≤ ((bv_unsigned sp0) - 8388608))
    (h4 : ((bv_unsigned mb) % 4096) = 0)
    (h5 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ 140737488355328))
    (h6 : (length vals) = 42)
    (h7 : (length (pref 262144 (dropz 262144 content))) = (Int.toNat 262144))
    (h8 : 3203072 ≤ (bv_unsigned B'))
    (h9 : (((bv_unsigned B') + 1052672) ≤ (bv_unsigned B) ∨ ((bv_unsigned B) + 528384) ≤ (bv_unsigned B')))
    (h10 : (((bv_unsigned B') + 1052672) ≤ ((bv_unsigned mb) + 4096) ∨ ((bv_unsigned mb) + 8192) ≤ (bv_unsigned B'))) :
    ((bv_unsigned mb) + 4136) = (((bv_unsigned mb) + 4120) + 16) := by
  lia

-- openssl/hashtable: lib/T/hashtable/H0ReadG7.v (replace)
example
    {word list_byte T3 T4 : Type}
    (sp0 : word)
    (mb : word)
    (content : list_byte)
    (bv_unsigned : word → Int)
    (d : Int)
    (L : Int)
    (length : T3 → Nat)
    (vals : T3)
    (pref : Nat → T4 → T3)
    (dropz : Nat → list_byte → T4)
    (h1 : 33554432 ≤ L)
    (h2 : 4096 ≤ (bv_unsigned mb))
    (h3 : ((bv_unsigned mb) + 8192) ≤ ((bv_unsigned sp0) - 8388608))
    (h4 : ((bv_unsigned mb) % 4096) = 0)
    (h5 : (140735340871680 ≤ (bv_unsigned sp0) ∧ (bv_unsigned sp0) ≤ 140737488355328))
    (h6 : (length vals) = 42)
    (h7 : (length (pref 16777216 (dropz 16777216 content))) = (Int.toNat 16777216)) :
    ((bv_unsigned sp0) + ((-8388608) + d)) = (((bv_unsigned sp0) - 8388608) + d) := by
  lia

-- openssl/hashtable: lib/T/hashtable/H0W65x.v (replace)
example
    {list_byte word : Type}
    (path : list_byte)
    (tid : word)
    (vals : list_byte)
    (bv_unsigned : word → Int)
    (gm : word)
    (length : list_byte → Nat)
    (h1 : (0 < (bv_unsigned tid) ∧ (bv_unsigned tid) < (2 ^ (22 : Nat))))
    (h2 : (length path) ≤ 4095)
    (h3 : (length vals) = 76) :
    ((bv_unsigned gm) + 13) = (((bv_unsigned gm) + 16) - 3) := by
  lia

-- openssl/pem: lib/B/Fz_I1_getrn.v (assert)
example
    {T1 : Type}
    (idx : Int)
    (length : T1 → Nat)
    (bks : T1)
    (h1 : (Int.toNat idx) < (length bks)) :
    (Int.toNat idx) < (length bks) := by
  lia

-- openssl/pem: lib/B/Fz_I1_insert.v (replace)
example
    {T1 T2 : Type}
    (na : Int)
    (lh : Int)
    (nn : Int)
    (items : Int)
    (lo : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (IMG_UT_HI : Int)
    (data : Int)
    (B1 : Int)
    (na1 : Int)
    (i : Int)
    (length : T2 → Nat)
    (bks1 : T2)
    (B : Int)
    (p : Int)
    (pmax : Int)
    (bks : T2)
    (mcost : Int → Int)
    (h1 : (lh % 8) = 0)
    (h2 : (0 < nn ∧ nn < (2 ^ (31 : Nat))))
    (h3 : (0 ≤ items ∧ items < (2 ^ (40 : Nat))))
    (h4 : (lh + 104) ≤ lo)
    (h5 : lo ≤ ((bv_unsigned sp) - 192))
    (h6 : (bv_unsigned sp) ≤ (2 ^ (47 : Nat)))
    (h7 : 17594333495296 ≤ lo)
    (h8 : lo ≤ ((bv_unsigned sp) - 304))
    (h9 : IMG_UT_HI ≤ lo)
    (h10 : (data + 8) ≤ lo)
    (h11 : ((data + 8) ≤ lh ∨ (lh + 104) ≤ data))
    (h12 : (B1 % 8) = 0)
    (h13 : (B1 + (8 * na1)) ≤ lo)
    (h14 : (Int.toNat i) < (length bks1))
    (h15 : (Int.toNat i) < (length bks))
    (h16 : (2 * nn) ≤ items)
    (h17 : (B % 8) = 0)
    (h18 : (Int.toNat p) < (length bks))
    (h19 : pmax = (p + 1))
    (h20 : nn = (na - 1))
    (h21 : na ≤ 4000)
    (h22 : (mcost ((2 * na) * 8)) = 0) :
    (8 * (2 * na)) = ((2 * na) * 8) := by
  lia

-- openssl/pem: lib/B/Fz_K_pstrt.v (replace)
example
    {T1 : Type}
    (usp : Int)
    (pd : Int)
    (ps_RB : T1 → Int)
    (sp : T1)
    (h1 : (pd = 0 ∨ pd = 16))
    (h2 : (usp % 32) = pd)
    (h3 : (ps_RB sp) = ((usp + (-160)) - pd)) :
    (usp - 16) = ((usp + (-160)) + ((144 : Nat) : Int)) := by
  lia

-- openssl/pem: lib/B/Fz_T_rcuw.v (replace)
example
    {T1 : Type}
    (p : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (f : Int)
    (SP : Int)
    (pad : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 f)) = f)
    (h2 : (bv_unsigned (Z_to_bv 64 p)) = p)
    (h3 : (bv_unsigned (Z_to_bv 64 ((SP + (-160)) - pad))) = ((SP + (-160)) - pad)) :
    (p + 128) = (((p + 48) + 40) + 40) := by
  lia

-- openssl/pem: lib/B/Fz_W3_j0g.v (replace)
example
    {T1 : Type}
    (LB1 : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp1 : Int)
    (f : Int)
    (fl : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 sp1)) = sp1)
    (h2 : (bv_unsigned (Z_to_bv 64 f)) = f)
    (h3 : (bv_unsigned (Z_to_bv 64 fl)) = fl)
    (h4 : (bv_unsigned (Z_to_bv 64 LB1)) = LB1) :
    (((2 ^ (64 : Nat)) - 1) - LB1) = (18446744073709551615 - LB1) := by
  lia

-- openssl/pem: lib/B/Fz_W3_sanitize.v (replace)
example (i : Int) :
    (Int.toNat i) = (Int.toNat ((i + 1) - 1)) := by
  lia

-- openssl/pem: lib/B/Fz_W7_inv.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (a_sp : T2 → T1)
    (en : T2)
    (a_lo : T2 → Int)
    (a_sp1 : T2 → Int)
    (h1 : (a_lo en) ≤ (a_sp1 en)) :
    ((bv_unsigned (a_sp en)) - 16) = (((bv_unsigned (a_sp en)) + (-104)) + 88) := by
  lia

-- openssl/pem: lib/B/I_pcseg.v (replace)
example
    {T1 T2 : Type}
    (p : Int)
    (length : T1 → Nat)
    (txt : T1)
    (bv_unsigned : T2 → Int)
    (Z_to_bv : Int → Int → T2)
    (c : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 p)) = p)
    (h2 : (bv_unsigned (Z_to_bv 8 c)) = c) :
    ((p + 1) + (((length txt) : Nat) : Int)) = (p + ((((length txt) : Nat) : Int) + 1)) := by
  lia

-- openssl/pem: lib/B/I_ut.v (replace)
example
    {T1 : Type}
    (bs : T1)
    (A : Int)
    (i : Nat)
    (img_bytes_b : Int → T1 → Bool)
    (IMG_UT_LO : Int)
    (length : T1 → Nat)
    (IMG_UT_HI : Int)
    (h1 : (img_bytes_b A bs) = true)
    (h2 : IMG_UT_LO ≤ A)
    (h3 : (A + (((length bs) : Nat) : Int)) ≤ IMG_UT_HI)
    (h4 : (0 ≤ A ∧ (A + (((length bs) : Nat) : Int)) ≤ (2 ^ (64 : Nat)))) :
    ((A + 1) + ((i : Nat) : Int)) = (A + (((i + 1) : Nat) : Int)) := by
  lia

-- openssl/pem: lib/B/RT_init_mem.v (replace)
example
    {atable acs T3 T4 : Type}
    (A : atable)
    (ISP : Int)
    (ch : acs)
    (b : Int)
    (n : Int)
    (a : Int)
    (img_hi : atable → Int)
    (SEGTOP_A : Int)
    (sp_window_lo : Int)
    (sp_window_hi : Int)
    (hs_vis_ok : atable → acs → Bool)
    (kwritable : T3 → T3 → T4 → Int → Int → Bool)
    (kn : acs → T3)
    (ELit : Int → T4)
    (h1 : (img_hi A) = SEGTOP_A)
    (h2 : (sp_window_lo ≤ ISP ∧ ISP ≤ sp_window_hi))
    (h3 : (hs_vis_ok A ch) = true)
    (h4 : (kwritable (kn ch) (kn ch) (ELit 0) b n) = true)
    (h5 : 0 ≤ b)
    (h6 : 0 ≤ n)
    (h7 : (b + n) ≤ (2 ^ (47 : Nat)))
    (h8 : SEGTOP_A ≤ b) :
    a = (b + (a - b)) := by
  lia

-- openssl/pem: lib/B/Str_stpcpy.v (replace)
example
    {word list_byte : Type}
    (a0 : word)
    (a1 : word)
    (str : list_byte)
    (slack : list_byte)
    (bv_unsigned : word → Int)
    (i : Int)
    (length : list_byte → Nat)
    (h1 : ((-(((bv_unsigned a1) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int)) :
    ((bv_unsigned a0) + (i + 1)) = (((bv_unsigned a0) + i) + 1) := by
  lia

-- openssl/pem: lib/B/XR_regrun.v (replace)
example (d : Nat) :
    (Int.toNat (4 * ((d : Nat) : Int))) = (4 * d) := by
  lia

-- openssl/pem: lib/B/XR_regrun.v (replace)
example
    (B : Int)
    (b : Int)
    (hm : Bool)
    (N_1 : Int)
    (SHW_LO : Int)
    (SHW_HI : Int)
    (cur : Int)
    (na : Int)
    (fp : Int)
    (h1 : (hm = true → ((8 ≤ N_1 ∧ N_1 ≤ (2 ^ (20 : Nat))) ∧ (0 < B ∧ ((B + (32 * N_1)) ≤ (2 ^ (47 : Nat)) ∧ (((B + (32 * N_1)) ≤ 65536 ∨ 12550144 ≤ B) ∧ (((B + (32 * N_1)) ≤ SHW_LO ∨ SHW_HI ≤ B) ∧ (((B + (32 * N_1)) ≤ cur ∨ (cur + (16 * na)) ≤ B) ∧ ((B + (32 * N_1)) ≤ ((fp - 4336) - 32) ∨ fp ≤ B)))))))))
    (h2 : hm = true) :
    (B + (8 * (4 * b))) = (B + (32 * b)) := by
  lia

-- openssl/pem: lib/Common/AxSymExec3K.v (replace)
example
    {T1 T2 T3 Z_Z_bool : Type}
    (bc : T1)
    (c : T2)
    (d : Int)
    (ts : T3)
    (T : Z_Z_bool)
    (hi : Int)
    (hi0 : Int)
    (lin_test_relB : T1 → T2 → T3 → Z_Z_bool → Bool)
    (h1 : (lin_test_relB bc c ts T) = true) :
    ((hi + hi0) + d) = ((hi + d) + hi0) := by
  lia

-- openssl/pem: lib/MallocP/RF_aligned_head.v (replace)
example
    {word : Type}
    (stride : Int)
    (size_class : Int → Int)
    (sc : Int)
    (mword : Int)
    (idx : Int)
    (Z_to_bv : Int → Int → word)
    (P : Int)
    (G : Int)
    (bv_unsigned : word → Int)
    (gw : word)
    (Z_land : Int → Int → Int)
    (last_idx : Int)
    (Zpow : Int → Int → Int)
    (avail : Int)
    (freed : Int)
    (Z_shiftr : Int → Int → Int)
    (Z_shiftl : Int → Int → Int)
    (maplen : Int)
    (h1 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ idx ∧ idx < 32))
    (h3 : (bv_unsigned gw) = G)
    (h4 : (Z_land mword 31) = last_idx)
    (h5 : (0 ≤ (Zpow 2 idx) ∧ (Zpow 2 idx) < (2 ^ (32 : Nat))))
    (h6 : (Z_land avail (Zpow 2 idx)) = 0)
    (h7 : (Z_land freed (Zpow 2 idx)) = 0)
    (h8 : (Z_shiftr (bv_unsigned (Z_to_bv 64 (Z_shiftl mword 52))) 58) = sc)
    (h9 : (Z_shiftr mword 12) = maplen)
    (h10 : 0 ≤ (stride * (idx + 1)))
    (h11 : (Z_land 63 (bv_unsigned (Z_to_bv 64 (0 - P)))) = ((0 - P) % 64))
    (h12 : ((P % 64) = 0 ∧ ((0 - P) % 64) = 0))
    (h13 : ((P % 64) ≠ 0 ∧ ((0 - P) % 64) = (64 - (P % 64)))) :
    stride = ((size_class sc) * 16) := by
  lia

-- openssl/pem: lib/MallocP/RF_aligned_head.v (replace)
example
    {word : Type}
    (last_idx : Int)
    (freeable : Int)
    (sc : Int)
    (maplen : Int)
    (mword : Int)
    (idx : Int)
    (Z_to_bv : Int → Int → word)
    (P : Int)
    (G : Int)
    (bv_unsigned : word → Int)
    (gw : word)
    (Z_land : Int → Int → Int)
    (Zpow : Int → Int → Int)
    (avail : Int)
    (freed : Int)
    (Z_shiftr : Int → Int → Int)
    (Z_shiftl : Int → Int → Int)
    (stride : Int)
    (h1 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ idx ∧ idx < 32))
    (h3 : (bv_unsigned gw) = G)
    (h4 : (Z_land mword 31) = last_idx)
    (h5 : (0 ≤ (Zpow 2 idx) ∧ (Zpow 2 idx) < (2 ^ (32 : Nat))))
    (h6 : (Z_land avail (Zpow 2 idx)) = 0)
    (h7 : (Z_land freed (Zpow 2 idx)) = 0)
    (h8 : (Z_shiftr (bv_unsigned (Z_to_bv 64 (Z_shiftl mword 52))) 58) = sc)
    (h9 : (Z_shiftr mword 12) = maplen)
    (h10 : 0 ≤ (stride * (idx + 1)))
    (h11 : (Z_land 63 (bv_unsigned (Z_to_bv 64 (0 - P)))) = ((0 - P) % 64))
    (h12 : ((P % 64) = 0 ∧ ((0 - P) % 64) = 0))
    (h13 : ((P % 64) ≠ 0 ∧ ((0 - P) % 64) = (64 - (P % 64))))
    (h14 : stride = ((maplen * 4096) - 16)) :
    (((last_idx + (32 * freeable)) + (64 * sc)) + (maplen * 4096)) = (((last_idx + (32 * freeable)) + (64 * sc)) + (4096 * maplen)) := by
  lia

-- openssl/pem: lib/MallocP/RMalloc_reframe.v (replace)
example
    {aptr region T3 : Type}
    (b : aptr)
    (r : region)
    (k : Int)
    (po : Int)
    (n : Int)
    (r_base : region → Int)
    (eo : Int)
    (snd : aptr → Int)
    (stride : Int)
    (round_up_pg : T3 → Int)
    (r_len : region → T3)
    (cz : Int)
    (h1 : 0 ≤ (snd b))
    (h2 : (0 ≤ k ∧ k < 32))
    (h3 : (((snd b) + 16) + (stride * (k + 1))) ≤ (round_up_pg (r_len r)))
    (h4 : 16 ≤ stride)
    (h5 : cz ≤ po)
    (h6 : 0 ≤ n)
    (h7 : (po + n) ≤ eo)
    (h8 : ((eo - po) - n) < (2 ^ (32 : Nat)))
    (h9 : 0 ≤ (stride * k)) :
    ((r_base r) + (eo - 5)) = (((r_base r) + eo) - 5) := by
  lia

-- openssl/pem: lib/MallocP/RMalloc_reframe.v (assert)
example
    {aptr region T3 : Type}
    (b : aptr)
    (r : region)
    (k : Int)
    (rsv : Int)
    (snd : aptr → Int)
    (stride : Int)
    (round_up_pg : T3 → Int)
    (r_len : region → T3)
    (h1 : 0 ≤ (snd b))
    (h2 : (0 ≤ k ∧ k < 32))
    (h3 : (((snd b) + 16) + (stride * (k + 1))) ≤ (round_up_pg (r_len r)))
    (h4 : 16 ≤ stride)
    (h5 : 0 ≤ (stride * k))
    (h6 : (0 ≤ rsv ∧ rsv < (2 ^ (32 : Nat)))) :
    (0 ≤ (k + (32 * (min rsv 5))) ∧ (k + (32 * (min rsv 5))) < 256) := by
  lia

-- openssl/pem: lib/P/Fz_I1_insert.v (assert)
example
    {T1 T2 : Type}
    (j : Int)
    (length : T1 → Nat)
    (bks : T1)
    (i : Int)
    (rn : Int)
    (Ak : Int)
    (Ar : Int)
    (X : Int)
    (An : Int)
    (nr : Int)
    (lh : Int)
    (B : Int)
    (g : T2)
    (g_na : T2 → Int)
    (a : Int)
    (h1 : (Int.toNat i) < (length bks))
    (h2 : ((rn + 8) ≤ Ak ∨ (Ak + 24) ≤ rn))
    (h3 : (Int.toNat j) < (length bks))
    (h4 : ((An + 24) ≤ Ar ∨ (Ar + nr) ≤ An))
    (h5 : ((An + 24) ≤ lh ∨ (lh + 104) ≤ An))
    (h6 : ((An + 24) ≤ X ∨ (X + 24) ≤ An))
    (h7 : ((An + 24) ≤ B ∨ (B + (8 * (g_na g))) ≤ An))
    (h8 : (¬ (rn ≤ a ∧ a < (rn + 8)))) :
    (Int.toNat j) < (length bks) := by
  lia

-- openssl/pem: lib/P/Fz_K_hash.v (replace)
example
    {list_byte : Type}
    (A : Int)
    (str : list_byte)
    (i : Int)
    (length : list_byte → Nat)
    (h1 : (((length str) : Nat) : Int) < (2 ^ (40 : Nat)))
    (h2 : i < (((length str) : Nat) : Int))
    (h3 : (i + 1) = (((length str) : Nat) : Int)) :
    ((A + (i + 1)) + 1) = ((A + i) + 2) := by
  lia

-- openssl/pem: lib/P/Fz_W1_gets.v (replace)
example
    {list_byte : Type}
    (DO : Int)
    (j : Int)
    (bs : list_byte)
    (t : Int)
    (length : list_byte → Nat)
    (h1 : (0 < j ∧ j < ((2 ^ (31 : Nat)) - 1)))
    (h2 : j ≤ (((length bs) : Nat) : Int))
    (h3 : (0 ≤ DO ∧ (DO + j) < (2 ^ (63 : Nat)))) :
    (DO + (t + 1)) = ((DO + t) + 1) := by
  lia

-- openssl/pem: lib/P/Fz_W1_read.v (replace)
example
    (outl : Int)
    (D : Int)
    (off : Int)
    (len : Int)
    (OUT : Int)
    (h1 : (((D + off) + (len - off)) ≤ OUT ∨ (OUT + (len - off)) ≤ (D + off)))
    (h2 : (((D + off) + outl) ≤ OUT ∨ (OUT + outl) ≤ (D + off))) :
    (Int.toNat outl) = ((Int.toNat outl) + ((Int.toNat outl) - (Int.toNat outl))) := by
  lia

-- openssl/pem: lib/P/Fz_W4_block.v (replace)
example
    {word : Type}
    (sp : word)
    (C : Int)
    (T : Int)
    (K : Nat)
    (n0 : Int)
    (lo : Int)
    (Q : Int)
    (j0 : Int)
    (eofv : Int)
    (q : Int)
    (bv_unsigned : word → Int)
    (bv_swrap : Int → Int → Int)
    (h1 : ((0 ≤ n0 ∧ n0 ≤ 80) ∧ ((3 * (n0 / 4)) ≤ ((K : Nat) : Int) ∧ (0 < C ∧ ((C + 92) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ T ∧ ((T + ((K : Nat) : Int)) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ lo ∧ (lo ≤ ((bv_unsigned sp) - 16) ∧ (bv_unsigned sp) < (2 ^ (64 : Nat)))))))))))
    (h2 : ((C + 92) ≤ T ∨ (T + ((K : Nat) : Int)) ≤ C))
    (h3 : ((C + 92) ≤ lo ∨ (bv_unsigned sp) ≤ C))
    (h4 : ((T + ((K : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ T))
    (h5 : (0 ≤ q ∧ ((q + 1) < Q ∧ (0 ≤ j0 ∧ ((j0 + (4 * Q)) ≤ n0 ∧ ((-1) ≤ eofv ∧ eofv ≤ 2))))))
    (h6 : (q + 1) ≤ (n0 / 4))
    (h7 : (bv_swrap 32 ((4 * q) + 4)) = ((4 * q) + 4)) :
    (4 * (q + 1)) = ((4 * q) + 4) := by
  lia

-- openssl/pem: lib/P/Str_memmove.v (replace)
example
    {word list_byte : Type}
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (bs : list_byte)
    (off : Int)
    (bv_unsigned : word → Int)
    (i : Int)
    (length : list_byte → Nat)
    (chunk : list_byte)
    (h1 : (bv_unsigned a1) = ((bv_unsigned a0) + off))
    (h2 : (0 < off ∧ ((off + (bv_unsigned a2)) ≤ (((length bs) : Nat) : Int) ∧ (0 ≤ (bv_unsigned a0) ∧ (((bv_unsigned a0) + (((length bs) : Nat) : Int)) < (2 ^ (64 : Nat)) ∧ 0 ≤ (bv_unsigned a2))))))
    (h3 : (length chunk) = 8) :
    ((bv_unsigned a2) - (i + 8)) = (((bv_unsigned a2) - i) + (-8)) := by
  lia

-- openssl/pem: lib/Start/AsanRegRunSound.v (replace)
example
    {list_Segment atable ctab list_desc T5 T6 T7 T8 T9 : Type}
    (SEGS : list_Segment)
    (A : atable)
    (nx0 : Nat)
    (T : ctab)
    (TAB : list_desc)
    (k : T5)
    (i : Int)
    (kz : Int)
    (n : T6)
    (ds : list_desc)
    (c_tab : ctab → Int)
    (j : Int)
    (img_lo : atable → Int)
    (img_hi : atable → Int)
    (AP_expr_vars_lt : Nat → T7 → Bool)
    (e_spw : T7)
    (length : list_desc → Nat)
    (c_tabend : ctab → Int)
    (GSM_sortedb : T8 → list_desc → Bool)
    (l_ilo : T9 → T8)
    (c_lay : ctab → T9)
    (chk_tab : list_Segment → atable → ctab → T5 → Int → Int → T6 → list_desc → Bool)
    (h1 : (img_lo A) ≤ (img_hi A))
    (h2 : (AP_expr_vars_lt nx0 e_spw) = true)
    (h3 : ((c_tab T) + (64 * (((length TAB) : Nat) : Int))) = (c_tabend T))
    (h4 : (GSM_sortedb (l_ilo (c_lay T)) TAB) = true)
    (h5 : (chk_tab SEGS A T k i kz n ds) = true) :
    (((c_tab T) + (64 * i)) + (64 * j)) = ((c_tab T) + (64 * (i + j))) := by
  lia

-- openssl/punycode: lib/A/Fz_ca2u.v (replace)
example
    {T1 T2 : Type}
    (b : Int)
    (n : Int)
    (i : Int)
    (lo : Int)
    (bv_unsigned : T1 → Int)
    (W : Int → T1)
    (L : Int)
    (spa : Int)
    (usp : Int)
    (shad : Int → Int)
    (FB6 : Int)
    (FB : Int)
    (N_1 : Int)
    (length : T2 → Nat)
    (slack : T2)
    (h1 : 140735332483072 ≤ lo)
    (h2 : (bv_unsigned (W L)) = L)
    (h3 : (bv_unsigned (W spa)) = spa)
    (h4 : (bv_unsigned (W usp)) = usp)
    (h5 : (shad (FB6 + 4096)) = ((shad FB6) + 512))
    (h6 : (FB6 + 4096) ≤ lo)
    (h7 : (((shad FB6) + 512) ≤ lo ∧ 12361728 ≤ (shad FB6)))
    (h8 : lo ≤ (2 ^ (47 : Nat)))
    (h9 : (shad (FB6 + 2208)) = ((shad FB6) + 276))
    (h10 : (((FB6 + 4096) ≤ (shad FB6) ∨ ((shad FB6) + 512) ≤ FB6) ∧ (((FB + 256) ≤ (shad FB6) ∨ ((shad FB6) + 512) ≤ FB) ∧ (2147450880 ≤ (shad FB6) ∧ ((shad FB6) + 512) ≤ 17594333495296))))
    (h11 : ((n + 1) ≤ N_1 ∧ N_1 ≤ (n + 8)))
    (h12 : ((b + N_1) % 8) = 0)
    (h13 : ((b + N_1) ≤ 65536 ∨ 12361728 ≤ b))
    (h14 : (((min (Int.toNat (N_1 - (n + 1))) ((length slack) - 0)) : Nat) : Int) = (N_1 - (n + 1))) :
    ((b + (n + 1)) + (i - (n + 1))) = (b + i) := by
  lia

-- openssl/punycode: lib/A/Fz_cwpi.v (replace)
example
    {T1 : Type}
    (L : Int)
    (lo : Int)
    (bv_unsigned : T1 → Int)
    (W : Int → T1)
    (shad : Int → Int)
    (FB6 : Int)
    (spa : Int)
    (h1 : 140735332483072 ≤ lo)
    (h2 : (bv_unsigned (W L)) = L)
    (h3 : (shad (FB6 + 4096)) = ((shad FB6) + 512))
    (h4 : (bv_unsigned (W (L + (-128)))) = (L - 128))
    (h5 : (bv_unsigned (W (L + (-208)))) = (L + (-208)))
    (h6 : (bv_unsigned (W (L + (-160)))) = (L + (-160)))
    (h7 : (bv_unsigned (W spa)) = spa) :
    ((L + (-160)) - 16) = ((L + (-208)) + ((32 : Nat) : Int)) := by
  lia

-- openssl/punycode: lib/B/D_open.v (replace)
example
    {list_list_byte : Type}
    (argvb : list_list_byte)
    (length : list_list_byte → Nat)
    (h1 : (((length argvb) : Nat) : Int) = 2) :
    2 = (min 2 (length argvb)) := by
  lia

-- openssl/punycode: lib/B/F_printf_core_xloop.v (replace)
example
    {list_Z T2 : Type}
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
    (hex_digits : T2 → Int → list_Z)
    (l : T2)
    (x : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 5681152)
    (h5 : ((6186664 ≤ Fp ∧ (Fp + 232) ≤ 6947864) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((12562008 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 12570624)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (x / 16) < 1152921504606846976)
    (h12 : 1 ≤ (zlength (hex_digits l x)))
    (h13 : (zlength (hex_digits l x)) = ((zlength (hex_digits l (x / 16))) + 1)) :
    (Int.toNat (j - ((zlength (hex_digits l (x / 16))) + 1))) = (Int.toNat ((j - 1) - (zlength (hex_digits l (x / 16))))) := by
  lia

-- openssl/punycode: lib/B/Fz_cwpi.v (replace)
example
    {T1 : Type}
    (L : Int)
    (lo : Int)
    (bv_unsigned : T1 → Int)
    (W : Int → T1)
    (FB6 : Int)
    (AShadow_sha : Int → Int)
    (shad : Int → Int)
    (spa : Int)
    (h1 : 140735332483072 ≤ lo)
    (h2 : (bv_unsigned (W L)) = L)
    (h3 : (AShadow_sha ((FB6 + 2208) + 16)) = ((shad FB6) + 278))
    (h4 : (shad (FB6 + 4096)) = ((shad FB6) + 512))
    (h5 : (bv_unsigned (W (L + (-128)))) = (L - 128))
    (h6 : (bv_unsigned (W (L + (-208)))) = (L + (-208)))
    (h7 : (bv_unsigned (W (L + (-160)))) = (L + (-160)))
    (h8 : (bv_unsigned (W spa)) = spa) :
    ((L + (-128)) - 16) = ((L + (-160)) + ((16 : Nat) : Int)) := by
  lia

-- openssl/punycode: lib/B/Fz_w6.v (replace)
example
    (FB6 : Int)
    (h1 : ((FB6 + 4096) ≤ ((FB6 / 8) + 2147450880) ∨ (((FB6 / 8) + 2147450880) + 512) ≤ FB6))
    (h2 : 12570624 ≤ ((FB6 / 8) + 2147450880)) :
    ((FB6 / 8) + 2147451161) = (((FB6 / 8) + 2147450880) + 281) := by
  lia

-- openssl/punycode: lib/B/R_depot_hash.v (replace)
example
    {list_word : Type}
    (TR : Int)
    (sz : Int)
    (ws : list_word)
    (j : Int)
    (length : list_word → Nat)
    (hacc : Int)
    (h1 : (1 ≤ sz ∧ sz ≤ 254))
    (h2 : (((length ws) : Nat) : Int) = sz)
    (h3 : (0 ≤ TR ∧ (TR + 2040) ≤ (2 ^ (63 : Nat))))
    (h4 : (0 ≤ hacc ∧ hacc < (2 ^ (64 : Nat)))) :
    (TR + (8 * (j + 1))) = ((TR + (8 * j)) + 8) := by
  lia

-- openssl/punycode: lib/B/XR_isort.v (replace)
example
    {T1 : Type}
    (A : Int)
    (k : Int)
    (off : Nat)
    (length : T1 → Nat)
    (ws : T1)
    (h1 : (Int.toNat k) < (length ws)) :
    (A + ((8 * k) + ((off : Nat) : Int))) = ((A + (8 * k)) + ((off : Nat) : Int)) := by
  lia

-- openssl/punycode: lib/B/XR_isort.v (replace)
example (j : Nat) :
    (((2 * j) + 1) + 1) = (2 * (j + 1)) := by
  lia

-- openssl/punycode: lib/B/XR_isort.v (replace)
example
    {T1 T2 T3 : Type}
    (tab : Int)
    (p : Int)
    (j : Int)
    (bv_unsigned : T1 → Int)
    (W : Int → T1)
    (length : T2 → Nat)
    (a : T2)
    (n : Int)
    (fst : T3 → Int)
    (HSM_get : T2 → Int → T3)
    (snd : T3 → Int)
    (HSM_key : T3 → Int)
    (k : Int)
    (ws_of : T2 → T2)
    (wsA : T2)
    (h1 : (0 ≤ p ∧ p < j))
    (h2 : (bv_unsigned (W j)) = j)
    (h3 : (length a) = (Int.toNat n))
    (h4 : ((0 ≤ (fst (HSM_get a p)) ∧ (fst (HSM_get a p)) < (2 ^ (64 : Nat))) ∧ (0 ≤ (snd (HSM_get a p)) ∧ (snd (HSM_get a p)) < (2 ^ (64 : Nat)))))
    (h5 : ((0 ≤ (fst (HSM_get a j)) ∧ (fst (HSM_get a j)) < (2 ^ (64 : Nat))) ∧ (0 ≤ (snd (HSM_get a j)) ∧ (snd (HSM_get a j)) < (2 ^ (64 : Nat)))))
    (h6 : (bv_unsigned (W (HSM_key (HSM_get a p)))) = (HSM_key (HSM_get a p)))
    (h7 : (bv_unsigned (W k)) = k)
    (h8 : (length (ws_of a)) = (2 * (Int.toNat n)))
    (h9 : (length wsA) = (2 * (Int.toNat n))) :
    (tab + (16 * p)) = (tab + (8 * (2 * p))) := by
  lia

-- openssl/punycode: lib/B/XR_isort.v (replace)
example
    {T1 T2 T3 : Type}
    (p : Int)
    (j : Int)
    (bv_unsigned : T1 → Int)
    (W : Int → T1)
    (length : T2 → Nat)
    (a : T2)
    (n : Int)
    (fst : T3 → Int)
    (HSM_get : T2 → Int → T3)
    (snd : T3 → Int)
    (HSM_key : T3 → Int)
    (k : Int)
    (ws_of : T2 → T2)
    (wsA : T2)
    (h1 : (0 ≤ p ∧ p < j))
    (h2 : (bv_unsigned (W j)) = j)
    (h3 : (length a) = (Int.toNat n))
    (h4 : ((0 ≤ (fst (HSM_get a p)) ∧ (fst (HSM_get a p)) < (2 ^ (64 : Nat))) ∧ (0 ≤ (snd (HSM_get a p)) ∧ (snd (HSM_get a p)) < (2 ^ (64 : Nat)))))
    (h5 : ((0 ≤ (fst (HSM_get a j)) ∧ (fst (HSM_get a j)) < (2 ^ (64 : Nat))) ∧ (0 ≤ (snd (HSM_get a j)) ∧ (snd (HSM_get a j)) < (2 ^ (64 : Nat)))))
    (h6 : (bv_unsigned (W (HSM_key (HSM_get a p)))) = (HSM_key (HSM_get a p)))
    (h7 : (bv_unsigned (W k)) = k)
    (h8 : (length (ws_of a)) = (2 * (Int.toNat n)))
    (h9 : (length wsA) = (2 * (Int.toNat n))) :
    (Int.toNat ((2 * p) + 1)) = ((Int.toNat (2 * p)) + 1) := by
  lia

-- openssl/punycode: lib/B/XR_isort.v (replace)
example
    {T1 T2 T3 : Type}
    (tab : Int)
    (cur : Int)
    (bv_unsigned : T1 → Int)
    (W : Int → T1)
    (b : Int)
    (length : T2 → Nat)
    (ws_of : T3 → T2)
    (a : T3)
    (n : Int)
    (h1 : (bv_unsigned (W b)) = b)
    (h2 : (length (ws_of a)) = (2 * (Int.toNat n))) :
    ((tab + (16 * cur)) + 8) = (tab + (8 * ((2 * cur) + 1))) := by
  lia

-- openssl/punycode: lib/B/XR_isort.v (replace)
example
    {T1 T2 T3 : Type}
    (tab : Int)
    (b : Int)
    (bv_unsigned : T1 → Int)
    (W : Int → T1)
    (length : T2 → Nat)
    (ws_of : T3 → T2)
    (a : T3)
    (n : Int)
    (h1 : (bv_unsigned (W b)) = b)
    (h2 : (length (ws_of a)) = (2 * (Int.toNat n))) :
    ((tab + (16 * b)) + 8) = (tab + (8 * ((2 * b) + 1))) := by
  lia

-- openssl/punycode: lib/B/XR_isort.v (replace)
example
    {T1 T2 T3 : Type}
    (last : Int)
    (n : Int)
    (bv_unsigned : T1 → Int)
    (W : Int → T1)
    (length : T2 → Nat)
    (ws_of : T3 → T2)
    (a : T3)
    (h1 : (1 ≤ last ∧ last < n))
    (h2 : (bv_unsigned (W last)) = last)
    (h3 : (length (ws_of a)) = (2 * (Int.toNat n))) :
    (Int.toNat ((2 * last) + 1)) = ((2 * (Int.toNat last)) + 1) := by
  lia

-- openssl/punycode: lib/B/XR_probe.v (replace)
example
    {T1 T2 T3 : Type}
    (N_1 : Int)
    (ne : Int)
    (nth : Nat → T1 → Int → Int)
    (ks : T1)
    (bv_unsigned : T2 → Int)
    (Z_to_bv : Int → Int → T2)
    (SP : Int)
    (length : T3 → Nat)
    (nws : T3)
    (key : Int)
    (h_1 : Int)
    (Z_land : Int → Int → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 SP)) = SP)
    (h2 : (length nws) = (4 * (Int.toNat N_1)))
    (h3 : (bv_unsigned (Z_to_bv 64 key)) = key)
    (h4 : (0 ≤ h_1 ∧ h_1 < N_1))
    (h5 : (bv_unsigned (Z_to_bv 64 h_1)) = h_1)
    (h6 : (nth (Int.toNat h_1) ks 0) ≠ key)
    (h7 : (bv_unsigned (Z_to_bv 64 (nth (Int.toNat h_1) ks 0))) = (nth (Int.toNat h_1) ks 0))
    (h8 : ((4 * (ne + 1)) < (3 * N_1) ∧ (N_1 / 8) < (N_1 - (ne + 1))))
    (h9 : (Z_land ne 18446744073709551615) = ne) :
    ((((N_1 - ne) - 1) + 2147483648) + (4294967296 * 4294967296)) = ((N_1 + (18446744073709551615 - ne)) + 2147483648) := by
  lia

-- openssl/punycode: lib/B/XR_probe.v (replace)
example
    {T1 T2 T3 : Type}
    (B : Int)
    (p : Int)
    (N_1 : Int)
    (nth : Nat → T1 → Int → Int)
    (ks : T1)
    (bv_unsigned : T2 → Int)
    (Z_to_bv : Int → Int → T2)
    (SP : Int)
    (length : T3 → Nat)
    (nws : T3)
    (key : Int)
    (h_1 : Int)
    (ne : Int)
    (Z_land : Int → Int → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 SP)) = SP)
    (h2 : (length nws) = (4 * (Int.toNat N_1)))
    (h3 : (bv_unsigned (Z_to_bv 64 key)) = key)
    (h4 : (0 ≤ h_1 ∧ h_1 < N_1))
    (h5 : (bv_unsigned (Z_to_bv 64 h_1)) = h_1)
    (h6 : (nth (Int.toNat h_1) ks 0) ≠ key)
    (h7 : (bv_unsigned (Z_to_bv 64 (nth (Int.toNat h_1) ks 0))) = (nth (Int.toNat h_1) ks 0))
    (h8 : ((4 * (ne + 1)) < (3 * N_1) ∧ (N_1 / 8) < (N_1 - (ne + 1))))
    (h9 : (Z_land ne 18446744073709551615) = ne)
    (h10 : (bv_unsigned (Z_to_bv 64 (B + (32 * p)))) = (B + (32 * p))) :
    ((B + (32 * p)) + 16) = (B + (8 * ((4 * p) + 2))) := by
  lia

-- openssl/punycode: lib/B/XR_rehash.v (replace)
example (B : Int) (d : Int) :
    (B + (32 * d)) = (B + (8 * (4 * d))) := by
  lia

-- openssl/punycode: lib/B/XR_rehash.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (pl : T1)
    (skipn : Nat → T2 → T1)
    (j : Int)
    (olds : T2)
    (nth : Nat → T2 → Int → Int)
    (k : Int)
    (ows : T1)
    (Z_to_bv : Int → Int → T3)
    (bv_unsigned : T3 → Int)
    (RHM_is_live : Int → Bool)
    (Bo : Int)
    (No : Int)
    (h_1 : Int)
    (N_1 : Int)
    (nws : T1)
    (ks : T2)
    (h1 : (length (skipn (Int.toNat j) olds)) = 0)
    (h2 : (nth (Int.toNat j) olds 0) = k)
    (h3 : (0 ≤ k ∧ k < (2 ^ (64 : Nat))))
    (h4 : (bv_unsigned (Z_to_bv 64 k)) = k)
    (h5 : (RHM_is_live k) = false)
    (h6 : (bv_unsigned (Z_to_bv 64 (Bo + (32 * (j + 1))))) = (Bo + (32 * (j + 1))))
    (h7 : (bv_unsigned (Z_to_bv 64 (Bo + (32 * No)))) = (Bo + (32 * No)))
    (h8 : (0 ≤ h_1 ∧ h_1 < N_1))
    (h9 : (bv_unsigned (Z_to_bv 64 h_1)) = h_1)
    (h10 : (RHM_is_live k) = true)
    (h11 : (bv_unsigned (Z_to_bv 64 (nth (Int.toNat h_1) ks 0))) = (nth (Int.toNat h_1) ks 0))
    (h12 : (length nws) = (4 * (Int.toNat N_1)))
    (h13 : (length ows) = (4 * (Int.toNat No))) :
    ((((length pl) : Nat) : Int) + 1) = ((((length pl) + 1) : Nat) : Int) := by
  lia

-- openssl/punycode: lib/Common/AsanNodesLibE.v (replace)
example
    {T1 T2 T3 : Type}
    (d : Int)
    (bv_unsigned : T1 → Int)
    (b : T1)
    (req : T1)
    (getr : T2 → Nat → T1)
    (regs : T2)
    (model : T3)
    (brk_refusal_b : T3 → T1 → T1 → Bool)
    (h1 : (bv_unsigned req) = ((bv_unsigned b) + d))
    (h2 : (bv_unsigned (getr regs 17)) = 214)
    (h3 : (brk_refusal_b model req b) = true)
    (h4 : (bv_unsigned b) < (bv_unsigned req)) :
    d = (((bv_unsigned b) + d) - (bv_unsigned b)) := by
  lia

-- openssl/punycode: lib/LibA/AA2u.v (replace)
example
    {word : Type}
    (L : Int)
    (FB6 : Int)
    (b : Int)
    (len : Int)
    (N_1 : Int)
    (eb : word)
    (bv_unsigned : word → Int)
    (B : Int → word)
    (A_IMG_END : Int)
    (SB : Int)
    (HIMEM_BEG : Int)
    (HIMEM_END : Int)
    (h1 : (0 < b ∧ (b + N_1) < (2 ^ (63 : Nat))))
    (h2 : ((0 ≤ len ∧ len < (2 ^ (31 : Nat))) ∧ len < N_1))
    (h3 : (bv_unsigned (B len)) = 0)
    (h4 : ((((b + len) / 8) * 8) + 8) ≤ (b + N_1))
    (h5 : ((Int.fmod (bv_unsigned eb) (2 ^ (8 : Nat))) % 2) = 0)
    (h6 : ((FB6 % 64) = 0 ∧ ((A_IMG_END ≤ FB6 ∧ ((FB6 + 4096) ≤ SB ∨ HIMEM_BEG ≤ FB6)) ∧ (FB6 + 4096) ≤ HIMEM_END)))
    (h7 : (A_IMG_END ≤ (L - 2400) ∧ ((L + 96) < (2 ^ (63 : Nat)) ∧ (L % 32) = 0))) :
    (FB6 + (8 * 4)) = (FB6 + 32) := by
  lia

-- openssl/punycode: lib/LibA/AFakeStack.v (replace)
example
    {regfile T2 : Type}
    (fs : Int)
    (h_1 : Int)
    (l0 : regfile)
    (pos : Int)
    (A_IMG_END : Int)
    (HIMEM_END : Int)
    (SB : Int)
    (HIMEM_BEG : Int)
    (length : regfile → Nat)
    (SL_m0 : T2)
    (slots_ok : Int → T2 → Bool)
    (FB : Int)
    (sha : Int → Int)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (A_IMG_END ≤ fs ∧ ((fs + 11571200) ≤ HIMEM_END ∧ ((fs + 11571200) ≤ SB ∨ HIMEM_BEG ≤ fs))))
    (h3 : (length l0) = 32)
    (h4 : (slots_ok 32 SL_m0) = true)
    (h5 : FB = ((fs + 36864) + (64 * pos)))
    (h6 : (sha FB) = ((sha (fs + 36864)) + (8 * pos))) :
    ((fs + 36864) + (8 * (8 * pos))) = ((fs + 36864) + (64 * pos)) := by
  lia

-- openssl/punycode: lib/LibA/AInit.v (replace)
example
    {regfile : Type}
    (fs : Int)
    (spv : Int)
    (h_1 : Int)
    (l0 : regfile)
    (A_IMG_END : Int)
    (FS_SIZE : Int)
    (SB : Int)
    (HIMEM_BEG : Int)
    (length : regfile → Nat)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (A_IMG_END ≤ (spv - 336) ∧ (spv < (2 ^ (63 : Nat)) ∧ (spv % 32) = 0)))
    (h3 : (spv ≤ fs ∨ (fs + FS_SIZE) ≤ (spv - 336)))
    (h4 : (spv ≤ SB ∨ HIMEM_BEG ≤ (spv - 336)))
    (h5 : (length l0) = 32)
    (h6 : ((spv + (-128)) % 32) = 0) :
    (spv + ((-4) * 32)) = (spv + (-128)) := by
  lia

-- openssl/punycode: lib/LibA/AInit.v (replace)
example
    {regfile : Type}
    (fs : Int)
    (spv : Int)
    (h_1 : Int)
    (l0 : regfile)
    (off : Int)
    (A_IMG_END : Int)
    (FS_SIZE : Int)
    (SB : Int)
    (HIMEM_BEG : Int)
    (length : regfile → Nat)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (A_IMG_END ≤ (spv - 336) ∧ (spv < (2 ^ (63 : Nat)) ∧ (spv % 32) = 0)))
    (h3 : (spv ≤ fs ∨ (fs + FS_SIZE) ≤ (spv - 336)))
    (h4 : (spv ≤ SB ∨ HIMEM_BEG ≤ (spv - 336)))
    (h5 : (length l0) = 32)
    (h6 : ((spv + (-128)) % 32) = 0) :
    ((spv + (-128)) + off) = ((spv - 128) + off) := by
  lia

-- openssl/punycode: lib/LibA/AInit.v (replace)
example
    {word regfile : Type}
    (fs : Int)
    (pkt : Int)
    (spv : Int)
    (k : Int)
    (res : word)
    (l0 : regfile)
    (l : regfile)
    (a0v : Int)
    (A_IMG_END : Int)
    (FS_SIZE : Int)
    (SB : Int)
    (HIMEM_BEG : Int)
    (length : regfile → Nat)
    (bv_unsigned : word → Int)
    (h1 : (0 ≤ k ∧ k < 16384))
    (h2 : (A_IMG_END ≤ (spv - 128) ∧ spv < (2 ^ (63 : Nat))))
    (h3 : ((spv ≤ fs ∨ (fs + FS_SIZE) ≤ (spv - 128)) ∧ ((spv ≤ SB ∨ HIMEM_BEG ≤ (spv - 128)) ∧ ((spv ≤ pkt ∨ (pkt + 56) ≤ (spv - 128)) ∧ ((pkt + 56) ≤ fs ∨ (fs + 1085440) ≤ pkt)))))
    (h4 : (length l0) = 32)
    (h5 : (length l) = 32)
    (h6 : ((bv_unsigned res) = 0 → a0v = 0))
    (h7 : ((bv_unsigned res) ≠ 0 → a0v = 1)) :
    spv = ((spv + (-128)) + 128) := by
  lia

-- openssl/punycode: lib/LibA/AWpMemcpy.v (replace)
example
    {regfile T2 : Type}
    (fs : Int)
    (mx : Int)
    (spv : Int)
    (len : Int)
    (h_1 : Int)
    (k : Int)
    (FB : Int)
    (l0 : regfile)
    (x : Int)
    (A_IMG_END : Int)
    (length : regfile → Nat)
    (W : Int → T2)
    (HIMEM_END : Int)
    (bv_unsigned : T2 → Int)
    (sha : Int → Int)
    (h1 : k = (h_1 % 16384))
    (h2 : FB = ((fs + 36864) + (64 * k)))
    (h3 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h4 : mx < 32)
    (h5 : (A_IMG_END ≤ (spv - 2400) ∧ (spv < (2 ^ (63 : Nat)) ∧ (spv % 32) = 0)))
    (h6 : (0 ≤ len ∧ len < (2 ^ (62 : Nat))))
    (h7 : (length l0) = 32)
    (h8 : (0 ≤ x ∧ x < HIMEM_END))
    (h9 : (x < (fs + 36864) ∨ (fs + 1085440) ≤ x))
    (h10 : (bv_unsigned (W (sha x))) = (sha x))
    (h11 : (fs + 36864) = (8 * ((fs + 36864) / 8))) :
    (fs + (4608 * 8)) = (fs + 36864) := by
  lia

-- openssl/punycode: lib/LibB/BA2u.v (replace)
example
    {word : Type}
    (L : Int)
    (FB6 : Int)
    (b : Int)
    (len : Int)
    (N_1 : Int)
    (eb : word)
    (bv_unsigned : word → Int)
    (B : Int → word)
    (sha : Int → Int)
    (B_IMG_END : Int)
    (SB : Int)
    (HIMEM_BEG : Int)
    (HIMEM_END : Int)
    (h1 : (0 < b ∧ (b + N_1) < (2 ^ (63 : Nat))))
    (h2 : ((0 ≤ len ∧ len < (2 ^ (31 : Nat))) ∧ len < N_1))
    (h3 : (bv_unsigned (B len)) = 0)
    (h4 : ((((b + len) / 8) * 8) + 8) ≤ (b + N_1))
    (h5 : ((Int.fmod (bv_unsigned eb) (2 ^ (8 : Nat))) % 2) = 0)
    (h6 : ((FB6 % 64) = 0 ∧ ((B_IMG_END ≤ FB6 ∧ ((FB6 + 4096) ≤ SB ∨ HIMEM_BEG ≤ FB6)) ∧ (FB6 + 4096) ≤ HIMEM_END)))
    (h7 : (B_IMG_END ≤ (L - 2400) ∧ ((L + 64) < (2 ^ (63 : Nat)) ∧ (L % 32) = 0)))
    (h8 : ((sha FB6) % 8) = 0)
    (h9 : (((sha FB6) + 4) % 8) = 4) :
    (FB6 + 2079) = (((FB6 + (8 * 4)) + 2048) - 1) := by
  lia

-- openssl/punycode: lib/LibB/BA2u.v (replace)
example
    {word : Type}
    (L : Int)
    (FB6 : Int)
    (b : Int)
    (len : Int)
    (N_1 : Int)
    (eb : word)
    (bv_unsigned : word → Int)
    (B : Int → word)
    (B_IMG_END : Int)
    (SB : Int)
    (HIMEM_BEG : Int)
    (HIMEM_END : Int)
    (h1 : (0 < b ∧ (b + N_1) < (2 ^ (63 : Nat))))
    (h2 : ((0 ≤ len ∧ len < (2 ^ (31 : Nat))) ∧ len < N_1))
    (h3 : (bv_unsigned (B len)) = 0)
    (h4 : ((((b + len) / 8) * 8) + 8) ≤ (b + N_1))
    (h5 : ((Int.fmod (bv_unsigned eb) (2 ^ (8 : Nat))) % 2) = 0)
    (h6 : ((FB6 % 64) = 0 ∧ ((B_IMG_END ≤ FB6 ∧ ((FB6 + 4096) ≤ SB ∨ HIMEM_BEG ≤ FB6)) ∧ (FB6 + 4096) ≤ HIMEM_END)))
    (h7 : (B_IMG_END ≤ (L - 2400) ∧ ((L + 64) < (2 ^ (63 : Nat)) ∧ (L % 32) = 0))) :
    (FB6 + 2224) = ((FB6 + 2208) + 16) := by
  lia

-- openssl/punycode: lib/LibB/BIcStrncmp.v (replace)
example
    {regfile T2 T3 : Type}
    (p : Int)
    (N_1 : Int)
    (k : Int)
    (z : Int)
    (q : Int)
    (n : Int)
    (l0 : regfile)
    (m : T2)
    (s1p : Int)
    (sz : T2 → Int)
    (bv_unsigned : T3 → Int)
    (B : Int → T3)
    (length : regfile → Nat)
    (h1 : (0 < p ∧ (p + N_1) < (2 ^ (63 : Nat))))
    (h2 : (0 ≤ k ∧ k ≤ z))
    (h3 : z < N_1)
    (h4 : (bv_unsigned (B z)) = 0)
    (h5 : (0 < n ∧ n ≤ 64))
    (h6 : (0 < q ∧ (q + n) < (2 ^ (63 : Nat))))
    (h7 : (length l0) = 32) :
    ((s1p + (sz m)) - 1) = ((s1p + (sz m)) + (-1)) := by
  lia

-- openssl/punycode: lib/LibB/BInit.v (replace)
example
    {regfile : Type}
    (fs : Int)
    (pkt : Int)
    (spv : Int)
    (h_1 : Int)
    (l0 : regfile)
    (B_IMG_END : Int)
    (FS_SIZE : Int)
    (SB : Int)
    (HIMEM_BEG : Int)
    (length : regfile → Nat)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (B_IMG_END ≤ (spv - 336) ∧ (spv < (2 ^ (63 : Nat)) ∧ (spv % 32) = 0)))
    (h3 : (spv ≤ fs ∨ (fs + FS_SIZE) ≤ (spv - 336)))
    (h4 : (spv ≤ SB ∨ HIMEM_BEG ≤ (spv - 336)))
    (h5 : ((spv ≤ pkt ∨ (pkt + 56) ≤ (spv - 336)) ∧ ((pkt + 56) ≤ fs ∨ (fs + 1085440) ≤ pkt)))
    (h6 : (length l0) = 32)
    (h7 : ((spv + (-128)) % 32) = 0) :
    (spv + ((-4) * 32)) = (spv + (-128)) := by
  lia

-- openssl/punycode: lib/LibB/BMStrlen.v (replace)
example
    {T1 : Type}
    (p : Int)
    (N_1 : Int)
    (k : Int)
    (z : Int)
    (i : Int)
    (bv_unsigned : T1 → Int)
    (B : Int → T1)
    (h1 : 0 ≤ p)
    (h2 : (p + N_1) < (2 ^ (64 : Nat)))
    (h3 : (0 ≤ k ∧ k ≤ z))
    (h4 : z < N_1)
    (h5 : (bv_unsigned (B z)) = 0)
    (h6 : ((((p + z) / 8) * 8) + 8) ≤ (p + N_1))
    (h7 : (i + 8) ≤ N_1)
    (h8 : ((p + i) / 8) ≤ ((p + z) / 8)) :
    (p + i) = (((p + i) - 8) + 8) := by
  lia

-- openssl/punycode: lib/LibB/BWpPut.v (replace)
example
    {regfile T2 : Type}
    (fs : Int)
    (pk : Int)
    (mx : Int)
    (spv : Int)
    (h_1 : Int)
    (k : Int)
    (FB : Int)
    (l0 : regfile)
    (x : Int)
    (B_IMG_END : Int)
    (length : regfile → Nat)
    (W : Int → T2)
    (HIMEM_END : Int)
    (bv_unsigned : T2 → Int)
    (sha : Int → Int)
    (h1 : k = (h_1 % 16384))
    (h2 : FB = ((fs + 36864) + (64 * k)))
    (h3 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h4 : (pk % 8) = 0)
    (h5 : mx < 32)
    (h6 : (B_IMG_END ≤ (spv - 2400) ∧ (spv < (2 ^ (63 : Nat)) ∧ (spv % 32) = 0)))
    (h7 : (length l0) = 32)
    (h8 : (0 ≤ x ∧ x < HIMEM_END))
    (h9 : (x < (fs + 36864) ∨ (fs + 1085440) ≤ x))
    (h10 : (bv_unsigned (W (sha x))) = (sha x))
    (h11 : (fs + 36864) = (8 * ((fs + 36864) / 8))) :
    (fs + (4608 * 8)) = (fs + 36864) := by
  lia

-- openssl/punycode: lib/LibB/BWpPut.v (replace)
example
    {regfile : Type}
    (fs : Int)
    (pk : Int)
    (mx : Int)
    (spv : Int)
    (h_1 : Int)
    (k : Int)
    (FB : Int)
    (l0 : regfile)
    (B_IMG_END : Int)
    (length : regfile → Nat)
    (h1 : k = (h_1 % 16384))
    (h2 : FB = ((fs + 36864) + (64 * k)))
    (h3 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h4 : (pk % 8) = 0)
    (h5 : mx < 32)
    (h6 : (B_IMG_END ≤ (spv - 2400) ∧ (spv < (2 ^ (63 : Nat)) ∧ (spv % 32) = 0)))
    (h7 : (length l0) = 32)
    (h8 : ((spv + (-96)) % 32) = 0) :
    (spv + ((-3) * 32)) = (spv + (-96)) := by
  lia

-- openssl/punycode: lib/LibP/PA2u.v (replace)
example
    {word : Type}
    (b : Int)
    (len : Int)
    (N_1 : Int)
    (out : Int)
    (eb : word)
    (k : Int)
    (r : Int)
    (z : Int)
    (tmpv : Int)
    (bv_unsigned : word → Int)
    (B : Int → word)
    (P_IMG_END : Int)
    (h1 : (0 < b ∧ (b + N_1) < (2 ^ (63 : Nat))))
    (h2 : ((0 ≤ len ∧ len < (2 ^ (31 : Nat))) ∧ len < N_1))
    (h3 : (bv_unsigned (B len)) = 0)
    (h4 : ((((b + len) / 8) * 8) + 8) ≤ (b + N_1))
    (h5 : ((Int.fmod (bv_unsigned eb) (2 ^ (8 : Nat))) % 2) = 0)
    (h6 : (P_IMG_END ≤ out ∧ (out + 16) < (2 ^ (63 : Nat))))
    (h7 : ((b + N_1) ≤ out ∨ (out + 16) ≤ b))
    (h8 : (0 ≤ k ∧ k ≤ len))
    (h9 : ((k ≤ r ∧ r ≤ z) ∧ z ≤ len))
    (h10 : (bv_unsigned (B z)) = 0)
    (h11 : ((bv_unsigned (B r)) = 0 ∨ (bv_unsigned (B r)) = 46))
    (h12 : (tmpv = 0 ∨ (tmpv = (b + r) ∧ (k ≤ r ∧ r < len))))
    (h13 : (k + 4) ≤ r) :
    r = (k + (r - k)) := by
  lia

-- openssl/punycode: lib/LibU/UStrchr.v (replace)
example
    {T1 : Type}
    (p : Int)
    (N_1 : Int)
    (k : Int)
    (r : Int)
    (c : Int)
    (spv : Int)
    (i : Int)
    (bv_unsigned : T1 → Int)
    (B : Int → T1)
    (h1 : 0 ≤ p)
    (h2 : (p + N_1) < (2 ^ (64 : Nat)))
    (h3 : (0 ≤ k ∧ k ≤ r))
    (h4 : r < N_1)
    (h5 : (0 < c ∧ c < 256))
    (h6 : ((bv_unsigned (B r)) = 0 ∨ (bv_unsigned (B r)) = c))
    (h7 : ((((p + r) / 8) * 8) + 8) ≤ (p + N_1))
    (h8 : 239208 ≤ (spv - 16))
    (h9 : spv < (2 ^ (64 : Nat)))
    (h10 : (spv ≤ p ∨ (p + N_1) ≤ (spv - 16)))
    (h11 : (i + 8) ≤ r)
    (h12 : ((p + (i + 8)) % 8) = 0) :
    ((p + i) + (1 * 8)) = (p + (i + 8)) := by
  lia

-- openssl/punycode: lib/LibU/UWpMemcpy.v (replace)
example
    {T1 : Type}
    (pk : Int)
    (out : Int)
    (mx : Int)
    (spv : Int)
    (src : Int)
    (len : Int)
    (l : T1)
    (length : T1 → Nat)
    (h1 : mx < 32)
    (h2 : (144 ≤ spv ∧ (spv ≤ pk ∧ (spv % 8) = 0)))
    (h3 : (0 ≤ len ∧ len < (2 ^ (62 : Nat))))
    (h4 : (0 ≤ src ∧ (src + len) < (2 ^ (63 : Nat))))
    (h5 : (((out + mx) ≤ (spv - 144) ∨ spv ≤ out) ∧ ((out + mx) ≤ pk ∨ (pk + 56) ≤ out)))
    (h6 : (length l) = 32) :
    (((spv + (-48)) + 48) + (-48)) = (spv - 48) := by
  lia

-- openssl/punycode: lib/Start/AsanRegBridge.v (replace)
example
    {ctab T2 T3 T4 : Type}
    (T : ctab)
    (c_map : ctab → Int)
    (ctab_okb : ctab → Bool)
    (shad : T2 → T3 → Int)
    (c_lay : ctab → T2)
    (l_ilo : T2 → T3)
    (l_ihi : T2 → T3)
    (ds : T4)
    (nind : T4 → Int)
    (h1 : (ctab_okb T) = true)
    (h2 : (0 ≤ (shad (c_lay T) (l_ilo (c_lay T))) ∧ ((shad (c_lay T) (l_ilo (c_lay T))) ≤ (shad (c_lay T) (l_ihi (c_lay T))) ∧ (shad (c_lay T) (l_ihi (c_lay T))) < (2 ^ (41 : Nat)))))
    (h3 : 0 ≤ (nind ds)) :
    ((c_map T) + 8) = ((c_map T) + ((8 : Nat) : Int)) := by
  lia

-- openssl/punycode: lib/U/Drv_main_B.v (replace)
example
    {T1 T2 T3 : Type}
    (RSTAGE : Int)
    (CNT : Int)
    (zlength : T1 → Int)
    (rd_content : T2 → T1)
    (st1 : T2)
    (length : T3 → Nat)
    (DATA : T3)
    (LEN : Int)
    (rd_cap : T2 → Int)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int))
    (h3 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h4 : 0 ≤ LEN)
    (h5 : ((1 ≤ CNT ∧ CNT ≤ 65536) ∧ CNT ≤ ((rd_cap st1) - LEN))) :
    RSTAGE = ((RSTAGE + CNT) - (((Int.toNat CNT) : Nat) : Int)) := by
  lia

-- openssl/punycode: lib/U/Drv_main_B.v (replace)
example
    {T1 T2 T3 : Type}
    (A : Int)
    (LEN : Int)
    (length : T1 → Nat)
    (DATA : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (arg1 : T1)
    (bs : T1)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int))
    (h3 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h4 : 0 ≤ LEN)
    (h5 : ((1 ≤ CNT ∧ CNT ≤ 65536) ∧ CNT ≤ ((rd_cap st1) - LEN)))
    (h6 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h7 : 1 ≤ (length bs)) :
    (A + LEN) = (A + (((length DATA) : Nat) : Int)) := by
  lia

-- openssl/punycode: lib/U/Drv_main_B.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (bs : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (DATA : T1)
    (LEN : Int)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (arg1 : T1)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int))
    (h3 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h4 : 0 ≤ LEN)
    (h5 : ((1 ≤ CNT ∧ CNT ≤ 65536) ∧ CNT ≤ ((rd_cap st1) - LEN)))
    (h6 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h7 : 1 ≤ (length bs)) :
    (Int.toNat (((length bs) : Nat) : Int)) = (length bs) := by
  lia

-- openssl/punycode: lib/U/Fz_fuzz.v (replace)
example (usp : Int) :
    ((usp + (-128)) + (-2176)) = (((usp + (-128)) + (-2216)) + ((40 : Nat) : Int)) := by
  lia

-- pupnp/FuzzHttp: lib/A0/AW/H_ListDestroy.v (replace)
example
    {T1 T2 : Type}
    (length : T1 → Nat)
    (ns : T1)
    (alloc_ceiling : Int)
    (q : Int)
    (blk_size : T2 → Int)
    (b : T2)
    (h1 : alloc_ceiling ≤ q)
    (h2 : alloc_ceiling ≤ (q + (-96)))
    (h3 : (blk_size b) = 24) :
    (((length ns) : Nat) : Int) = (((((length ns) : Nat) : Int) + 1) - 1) := by
  lia

-- pupnp/FuzzHttp: lib/A0/AW/H_germ_seg4.v (replace)
example
    {T1 T2 T3 : Type}
    (hvA : T1 → Int)
    (h_1 : T1)
    (i : Nat)
    (length : T2 → Nat)
    (str : T2)
    (vbs : T2)
    (f : Nat)
    (bv_unsigned : T3 → Int)
    (bc : T3)
    (h1 : (length str) < (length vbs))
    (h2 : (bv_unsigned bc) ≠ 0)
    (h3 : (i + 1) ≠ f) :
    ((hvA h_1) + (((i + 1) : Nat) : Int)) = (((hvA h_1) + ((i : Nat) : Int)) + 1) := by
  lia

-- pupnp/FuzzHttp: lib/A0/AW/H_membuffer_delete_seg.v (replace)
example (idx : Int) (num : Int) (A : Int) :
    (idx + num) = (((A + idx) + num) - A) := by
  lia

-- pupnp/FuzzHttp: lib/A0/AW/H_vfm_G.v (assert)
example (h1 : (0 : Int) ≤ 137408) :
    ((137408 + 8) : Int) < (2 ^ (62 : Nat)) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ICP/I_strncmp.v (assert)
example
    {list_byte : Type}
    (q : Int)
    (A : Int)
    (B : Int)
    (n : Int)
    (lo : Int)
    (ls : list_byte)
    (rs : list_byte)
    (length : list_byte → Nat)
    (h1 : lo ≤ ((q - 2176) - 80))
    (h2 : 17594333495296 ≤ lo)
    (h3 : q < (2 ^ (64 : Nat)))
    (h4 : ((A + (((length ls) : Nat) : Int)) ≤ lo ∨ q ≤ A))
    (h5 : ((B + (((length rs) : Nat) : Int)) ≤ lo ∨ q ≤ B))
    (h6 : (0 ≤ n ∧ n < (2 ^ (63 : Nat))))
    (h7 : (A + (min n (((length ls) : Nat) : Int))) < (2 ^ (47 : Nat)))
    (h8 : (min n (((length ls) : Nat) : Int)) ≤ (2 ^ (43 : Nat)))
    (h9 : (B + (min n (((length rs) : Nat) : Int))) < (2 ^ (47 : Nat)))
    (h10 : (min n (((length rs) : Nat) : Int)) ≤ (2 ^ (43 : Nat))) :
    lo ≤ (q - 2176) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ICP/I_strncpy.v (replace)
example
    {list_byte : Type}
    (q : Int)
    (D : Int)
    (n : Int)
    (lo : Int)
    (dbs : list_byte)
    (length : list_byte → Nat)
    (sh : Int → Int)
    (Z_shiftr : Int → Int → Int)
    (h1 : lo ≤ ((q - 2160) - 2256))
    (h2 : 17594333495296 ≤ lo)
    (h3 : q < (2 ^ (64 : Nat)))
    (h4 : (length dbs) = (Int.toNat n))
    (h5 : (0 ≤ n ∧ n < (2 ^ (31 : Nat))))
    (h6 : (D + n) ≤ lo)
    (h7 : 1335296 ≤ D)
    (h8 : (D + n) < (2 ^ (47 : Nat)))
    (h9 : (sh ((D + n) - 1)) = (2147450880 + (Z_shiftr ((D + n) + (-1)) 3))) :
    ((D + n) - 1) = ((D + n) + (-1)) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ICP/I_strnlen.v (replace)
example
    {list_byte : Type}
    (q : Int)
    (A : Int)
    (n : Int)
    (lo : Int)
    (buf : list_byte)
    (r : Int)
    (length : list_byte → Nat)
    (h1 : lo ≤ (((q - 2144) - 32) - 2208))
    (h2 : 17594333495296 ≤ lo)
    (h3 : q < (2 ^ (64 : Nat)))
    (h4 : 0 < A)
    (h5 : ((A + (((length buf) : Nat) : Int)) ≤ lo ∨ q ≤ A))
    (h6 : (A + (min (r + 1) n)) < (2 ^ (47 : Nat)))
    (h7 : (min (r + 1) n) ≤ (2 ^ (43 : Nat)))
    (h8 : (0 ≤ n ∧ n < (2 ^ (64 : Nat)))) :
    ((A + (min (r + 1) n)) + (-1)) = ((A + (min (r + 1) n)) - 1) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ICP/M_strchrnul.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a0 : word)
    (str : list_byte)
    (slack : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (i : Int)
    (length : list_byte → Nat)
    (h1 : ((-(((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h2 : lo ≤ ((bv_unsigned sp) - 16))
    (h3 : (0 ≤ (bv_unsigned a0) ∧ (((((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ lo ∧ (bv_unsigned sp) < (2 ^ (64 : Nat))))))
    (h4 : (((((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ ((bv_unsigned sp) - 16) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h5 : i = (((length str) : Nat) : Int)) :
    ((bv_unsigned a0) + i) = ((((bv_unsigned a0) + i) - 1) + 1) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ICP/M_strchrnul.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a0 : word)
    (str : list_byte)
    (slack : list_byte)
    (lo : Int)
    (i : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (h1 : ((-(((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h2 : lo ≤ ((bv_unsigned sp) - 16))
    (h3 : (0 ≤ (bv_unsigned a0) ∧ (((((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ lo ∧ (bv_unsigned sp) < (2 ^ (64 : Nat))))))
    (h4 : (((((bv_unsigned a0) + (((length str) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ ((bv_unsigned sp) - 16) ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h5 : i = (((length str) : Nat) : Int)) :
    (Int.toNat i) = (Int.toNat (((bv_unsigned a0) + i) - (bv_unsigned a0))) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ICP/M_twoway_B.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (H : Int)
    (h0 : Int)
    (hay : list_byte)
    (slack : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (length : list_byte → Nat)
    (got_ssp : Int)
    (ssp_guard : Int)
    (NAD : Int)
    (h1 : ((-((H + (((length hay) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h2 : lo ≤ (((bv_unsigned sp) - 2240) - 2320))
    (h3 : 17594333495296 ≤ lo)
    (h4 : ((H + (((length hay) : Nat) : Int)) + 1) < (2 ^ (47 : Nat)))
    (h5 : ((((length hay) : Nat) : Int) + 1) ≤ (2 ^ (43 : Nat)))
    (h6 : (0 ≤ H ∧ ((((H + (((length hay) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ lo ∧ (bv_unsigned sp) < (2 ^ (64 : Nat))))))
    (h7 : ((((H + (((length hay) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ lo ∨ (bv_unsigned sp) ≤ H))
    (h8 : (got_ssp + 8) ≤ lo)
    (h9 : (ssp_guard + 8) ≤ lo)
    (h10 : (NAD + 8) ≤ lo)
    (h11 : 0 < H)
    (h12 : (H ≤ h0 ∧ h0 ≤ (H + (((length hay) : Nat) : Int)))) :
    ((bv_unsigned sp) + (-2240)) = ((bv_unsigned sp) - 2240) := by
  lia

-- pupnp/FuzzHttp: lib/A0/T7A0/F_printf_core_dir.v (replace)
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
    (alloc_ceiling : Int)
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 136160)
    (h5 : ((699760 ≤ Fp ∧ (Fp + 232) ≤ 6318512) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6318520 ≤ B ∧ (B + BS) ≤ alloc_ceiling) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : alloc_ceiling ≤ lo)
    (h12 : (i + 1) < (zlength fmt))
    (h13 : (32 ≤ (znth fmt (i + 1)) ∧ (znth fmt (i + 1)) < 64))
    (h14 : (i + 2) < (zlength fmt)) :
    (i + 2) = ((i + 1) + 1) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ZAA/APrimPop.v (replace)
example (cnt : Nat) (s : Nat) (rest : Nat) :
    ((cnt * s) + rest) = ((s + ((cnt * s) + rest)) - s) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ZAA/APrimPopR.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (region : T1 → T2 → Int)
    (AL : T1)
    (c : T2)
    (p_au : T3 → Int)
    (k : T3)
    (cn : Nat)
    (sn : Nat)
    (pop_new : T3 → T2 → T4 → Int)
    (r : T4)
    (class_size : T2 → Int)
    (p_nf : T3 → Int)
    (length : T5 → Nat)
    (ws2 : T5)
    (pop_mu : T3 → T2 → T4 → Int)
    (z8 : Int)
    (s8 : Nat)
    (rest : Nat)
    (rest8 : Nat)
    (m8 : Int)
    (a8 : Int)
    (nb : Nat)
    (nsh : Nat)
    (sh : Int → Int)
    (h1 : (Int.toNat ((p_nf k) + (pop_new k c r))) ≤ (length ws2))
    (h2 : ((class_size c) / 8) = z8)
    (h3 : ((pop_new k c r) * (class_size c)) = (8 * ((pop_new k c r) * z8)))
    (h4 : 0 ≤ ((pop_new k c r) * z8))
    (h5 : ((pop_new k c r) * (class_size c)) ≤ ((pop_mu k c r) - (p_au k)))
    (h6 : ((cn : Nat) : Int) = (pop_new k c r))
    (h7 : ((sn : Nat) : Int) = (class_size c))
    (h8 : ((s8 : Nat) : Int) = z8)
    (h9 : ((rest : Nat) : Int) = (((pop_mu k c r) - (p_au k)) - ((pop_new k c r) * (class_size c))))
    (h10 : ((rest8 : Nat) : Int) = ((m8 - a8) - ((pop_new k c r) * z8)))
    (h11 : nb = ((cn * sn) + rest))
    (h12 : nsh = ((cn * s8) + rest8))
    (h13 : (sh ((region AL c) + (pop_mu k c r))) = ((sh (region AL c)) + m8))
    (h14 : (sh ((region AL c) + (p_au k))) = ((sh (region AL c)) + a8)) :
    (((region AL c) + (p_au k)) + (((cn : Nat) : Int) * ((sn : Nat) : Int))) = ((region AL c) + ((p_au k) + ((pop_new k c r) * (class_size c)))) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ZAA/APrimPopR.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (sh : Int → Int)
    (region : T1 → T2 → Int)
    (AL : T1)
    (c : T2)
    (p_au : T3 → Int)
    (k : T3)
    (i : Nat)
    (s8 : Nat)
    (a8 : Int)
    (z8 : Int)
    (p_nf : T3 → Int)
    (pop_new : T3 → T2 → T4 → Int)
    (r : T4)
    (length : T5 → Nat)
    (ws2 : T5)
    (class_size : T2 → Int)
    (pop_mu : T3 → T2 → T4 → Int)
    (cn : Nat)
    (sn : Nat)
    (rest : Nat)
    (rest8 : Nat)
    (m8 : Int)
    (nb : Nat)
    (nsh : Nat)
    (h1 : (Int.toNat ((p_nf k) + (pop_new k c r))) ≤ (length ws2))
    (h2 : ((class_size c) / 8) = z8)
    (h3 : ((pop_new k c r) * (class_size c)) = (8 * ((pop_new k c r) * z8)))
    (h4 : 0 ≤ ((pop_new k c r) * z8))
    (h5 : ((pop_new k c r) * (class_size c)) ≤ ((pop_mu k c r) - (p_au k)))
    (h6 : ((cn : Nat) : Int) = (pop_new k c r))
    (h7 : ((sn : Nat) : Int) = (class_size c))
    (h8 : ((s8 : Nat) : Int) = z8)
    (h9 : ((rest : Nat) : Int) = (((pop_mu k c r) - (p_au k)) - ((pop_new k c r) * (class_size c))))
    (h10 : ((rest8 : Nat) : Int) = ((m8 - a8) - ((pop_new k c r) * z8)))
    (h11 : nb = ((cn * sn) + rest))
    (h12 : nsh = ((cn * s8) + rest8))
    (h13 : (sh ((region AL c) + (pop_mu k c r))) = ((sh (region AL c)) + m8))
    (h14 : (sh ((region AL c) + (p_au k))) = ((sh (region AL c)) + a8)) :
    ((sh ((region AL c) + (p_au k))) + (((i : Nat) : Int) * ((s8 : Nat) : Int))) = ((sh (region AL c)) + (a8 + (((i : Nat) : Int) * z8))) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ZAA/F_alloc_A.v (replace)
example
    (rk : Int)
    (rz : Int)
    (n : Int)
    (Z_b2z : Bool → Int)
    (al_n : Int → Int)
    (a0_need : Int → Int)
    (h1 : (8 ≤ (max n 8) ∧ (max n 8) ≤ (2 ^ (28 : Nat))))
    (h2 : (n + (Z_b2z (decide (n < 1)))) = (al_n n))
    (h3 : (a0_need n) = ((8 * rk) + rz)) :
    (((8 * rk) + rz) + rz) = (rz + ((8 * rk) + rz)) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ZAA/F_alloc_B.v (replace)
example (Z_log2 : Int → Int) (needed : Int) (h1 : 9 ≤ (Z_log2 needed)) (h2 : (Z_log2 needed) < 17) :
    ((Z_log2 needed) + 1) = ((Z_log2 needed) + 1) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ZAA/F_prim_efa.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (fa_base : T1 → Int → Int)
    (AL : T1)
    (c : Int)
    (length : T2 → Nat)
    (ws : T2)
    (beg : Int)
    (region : T1 → Int → Int)
    (al_space : T1 → Int)
    (K_REGION : Int)
    (FA_OFF : Int)
    (ria : Int)
    (K_SPACE : Int)
    (total : Int)
    (p_mfa : T3 → Int)
    (k : T3)
    (nm : Int)
    (rup : Int → T4 → Int)
    (K_MAP : T4)
    (size : Int)
    (sh : Int → Int)
    (h1 : (region AL c) = ((al_space AL) + (c * K_REGION)))
    (h2 : (fa_base AL c) = ((region AL c) + FA_OFF))
    (h3 : ria = (((al_space AL) + K_SPACE) + (128 * c)))
    (h4 : (decide ((4 * total) ≤ (p_mfa k))) = true)
    (h5 : (decide ((4 * total) ≤ (p_mfa k))) = false)
    (h6 : nm = (rup (4 * total) K_MAP))
    (h7 : beg = ((fa_base AL c) + (p_mfa k)))
    (h8 : size = (nm - (p_mfa k)))
    (h9 : (beg % 4096) = 0)
    (h10 : (size % 4096) = 0)
    (h11 : (sh (beg + size)) = ((sh beg) + (size / 8))) :
    ((fa_base AL c) + (4 * (((length ws) : Nat) : Int))) = beg := by
  lia

-- pupnp/FuzzHttp: lib/A0/ZAA/F_quar_A.v (replace)
example
    {T1 : Type}
    (al_space : T1 → Int)
    (AL : T1)
    (c : Int)
    (K_REGION : Int)
    (B : Int)
    (class_size : Int → Int)
    (K_SPACE : Int)
    (M : Int)
    (rup8 : Int → Int)
    (n : Int)
    (rz : Int)
    (region : T1 → Int → Int)
    (v : Int)
    (off : Int)
    (Z_shiftr : Int → Int → Int)
    (Z_land : Int → Int → Int)
    (sz : Int)
    (idx : Int)
    (h1 : (((al_space AL) + K_REGION) ≤ B ∧ ((B + (class_size c)) ≤ ((al_space AL) + K_SPACE) ∧ (B % 16) = 0)))
    (h2 : ((B + 0) ≤ M ∧ (((M + 16) + (rup8 n)) ≤ (B + (class_size c)) ∧ (M % 16) = 0)))
    (h3 : M = ((B + rz) - 16))
    (h4 : B = ((region AL c) + (16 * v)))
    (h5 : ((n ≤ (rup8 n) ∧ (rup8 n) < (n + 8)) ∧ ((rup8 n) % 8) = 0))
    (h6 : ((16 * v) ≤ off ∧ (((off + 16) + (rup8 n)) ≤ ((16 * v) + (class_size c)) ∧ off = ((16 * v) + (rz - 16)))))
    (h7 : (M - (al_space AL)) = ((c * 4294967296) + off))
    (h8 : (0 ≤ off ∧ off < 4294967296))
    (h9 : (Z_shiftr (M - (al_space AL)) 32) = c)
    (h10 : (Z_land c 31) = c)
    (h11 : ((16 * v) = (sz * idx) ∧ (0 ≤ idx ∧ (Int.fdiv off sz) = idx)))
    (h12 : idx < (2 ^ (27 : Nat))) :
    (((al_space AL) + 137438953472) + (128 * c)) = (((al_space AL) + 137438953472) + (c * 128)) := by
  lia

-- pupnp/FuzzHttp: lib/A0/ZAA/F_quar_Ep.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (cnt : Int)
    (v : Int)
    (al_space : T1 → Int)
    (AL : T1)
    (K_REGION : Int)
    (NBA : Int)
    (K_SPACE : Int)
    (sh : Int → Int)
    (k1 : T2)
    (l : T3)
    (p_au : T2 → Int)
    (Z_shiftr : Int → Int → Int)
    (Z_shiftl : Int → Int → Int)
    (Z_to_bv : Int → Int → T4)
    (amo_aligned : T5 → T4 → Bool)
    (AD : T5)
    (at_thr : T6 → Int)
    (al_thread : T1 → T6)
    (qb_addr : T1 → T7 → Int)
    (bn : T7)
    (length : T3 → Nat)
    (l' : T3)
    (b : T7)
    (Q_BBYTES : Int)
    (qlast : T1 → T3 → Int)
    (qb_v : T7 → Int)
    (h1 : (1 ≤ cnt ∧ cnt ≤ 2))
    (h2 : (0 ≤ v ∧ v < (2 ^ (28 : Nat))))
    (h3 : (((al_space AL) + K_REGION) ≤ NBA ∧ (NBA + 8192) ≤ ((al_space AL) + K_SPACE)))
    (h4 : (NBA % 8) = 0)
    (h5 : (2147450880 ≤ (sh NBA) ∧ ((sh NBA) + 1024) ≤ 17594333495296))
    (h6 : ((p_au k1) % 8) = 0)
    (h7 : (Z_shiftr ((Z_shiftl (cnt + (-1)) 32) % 18446744073709551616) 30) = (4 * (cnt - 1)))
    (h8 : (amo_aligned AD (Z_to_bv 64 ((at_thr (al_thread AL)) + 2784))) = true)
    (h9 : (sh (((al_space AL) + K_SPACE) + 4096)) ≤ 17594333495296)
    (h10 : 2147450880 ≤ (sh (al_space AL)))
    (h11 : (qb_addr AL bn) = NBA)
    (h12 : (((length l) : Nat) : Int) = ((((length l') : Nat) : Int) + 1))
    (h13 : (2147450880 ≤ (sh (qb_addr AL b)) ∧ ((sh (qb_addr AL b)) + 1024) ≤ 17594333495296))
    (h14 : (((al_space AL) + K_REGION) ≤ (qb_addr AL b) ∧ ((qb_addr AL b) + Q_BBYTES) ≤ ((al_space AL) + K_SPACE)))
    (h15 : (qlast AL l) = (qb_addr AL b))
    (h16 : (qb_v b) ≠ v)
    (h17 : (((qb_addr AL b) + 8192) ≤ NBA ∨ (NBA + 8192) ≤ (qb_addr AL b))) :
    ((4 * (cnt - 1)) * (2 ^ (30 : Nat))) = ((cnt + (-1)) * (2 ^ (32 : Nat))) := by
  lia

-- pupnp/FuzzHttp: lib/ASN/AsanPlanSound.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (s : T1)
    (b : T1)
    (h1 : (((bv_unsigned b) + (bv_unsigned s)) % 4096) = 0) :
    (bv_unsigned s) = (((bv_unsigned b) + (bv_unsigned s)) - (bv_unsigned b)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/AW/HCount.v (lemma)
example (c : Int) (w0 : Int → Int) :
    ((0 : Int) ≤ (5 * 0) ∧ (5 * 0) ≤ ((w0 (c + 1)) - (w0 (c + 1)))) := by
  lia

-- pupnp/FuzzHttp: lib/B0/AW/H_phdr_seg.v (replace)
example
    {list_word : Type}
    (A : Int)
    (len : Int)
    (ws : list_word)
    (cur : Int)
    (tcur : Int)
    (tlz : Int)
    (s7v : Int)
    (length : list_word → Nat)
    (h1 : (length ws) = 66)
    (h2 : 0 ≤ tcur)
    (h3 : 1 ≤ tlz)
    (h4 : (tcur + tlz) = cur)
    (h5 : cur ≤ len)
    (h6 : (0 ≤ s7v ∧ s7v < (2 ^ (64 : Nat)))) :
    (A + cur) = ((A + tcur) + tlz) := by
  lia

-- pupnp/FuzzHttp: lib/B0/AW/H_presp.v (replace)
example
    {T1 T2 : Type}
    (P : Int)
    (q : Int)
    (A : Int)
    (cap : Int)
    (bn : Int)
    (len : Int)
    (bs : T1)
    (lo : Int)
    (sh : Int → Int)
    (alloc_ceiling : Int)
    (n : Int)
    (length : T1 → Nat)
    (firstn : Nat → T2 → T1)
    (skipn : Nat → T1 → T2)
    (t' : Int)
    (h1 : q < (2 ^ (64 : Nat)))
    (h2 : q ≤ ((2 ^ (47 : Nat)) - 64))
    (h3 : 6328320 ≤ P)
    (h4 : ((A + cap) + 1) < (2 ^ (63 : Nat)))
    (h5 : lo ≤ q)
    (h6 : ((sh q) + 8) ≤ 17594333495296)
    (h7 : ((sh alloc_ceiling) - ((sh alloc_ceiling) % 8)) ≤ ((sh lo) - ((sh lo) % 8)))
    (h8 : ((sh lo) - ((sh lo) % 8)) ≤ (sh lo))
    (h9 : (0 ≤ n ∧ n ≤ len))
    (h10 : (length bs) = (Int.toNat bn))
    (h11 : (((length (firstn (Int.toNat n) (skipn (Int.toNat t') bs))) : Nat) : Int) = n) :
    (P + 264) = ((P + 232) + 32) := by
  lia

-- pupnp/FuzzHttp: lib/B0/AW/H_puri_seg2.v (replace)
example {T1 T2 : Type} (size : Int) (puriF : T1 → T2 → Int) (FI : T1) (st : T2) :
    size = ((((puriF FI st) + 32) + size) - ((puriF FI st) + 32)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/AW/H_vfm_A.v (replace)
example (j : Int) (cur : Int) (pos : Int) (h1 : (cur + (j + 1)) ≤ pos) :
    (j - 1) = (j + (-1)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ICP/I_printf_common.v (replace)
example
    {word list_byte T3 : Type}
    (sp : word)
    (a2 : word)
    (lo : Int)
    (FMT : Int)
    (fstr : list_byte)
    (Sa : Int)
    (sstr : list_byte)
    (dcs : T3)
    (k : Nat)
    (c : Int)
    (length : list_byte → Nat)
    (bv_unsigned : word → Int)
    (cells_size : T3 → Nat)
    (sh : Int → Int)
    (Z_shiftr : Int → Int → Int)
    (h1 : lo ≤ ((bv_unsigned sp) - 2320))
    (h2 : 17594333495296 ≤ lo)
    (h3 : (1 ≤ (((length fstr) : Nat) : Int) ∧ (((length fstr) : Nat) : Int) ≤ 62))
    (h4 : (65536 ≤ FMT ∧ ((FMT + (((length fstr) : Nat) : Int)) + 1) ≤ 6328320))
    (h5 : ((bv_unsigned sp) ≤ (bv_unsigned a2) ∧ ((bv_unsigned a2) + 8) ≤ (2 ^ (64 : Nat))))
    (h6 : ((Sa + ((((length sstr) : Nat) : Int) + 1)) ≤ ((bv_unsigned sp) - 2320) ∨ (bv_unsigned sp) ≤ Sa))
    (h7 : (Sa + ((((length sstr) : Nat) : Int) + 1)) < (2 ^ (47 : Nat)))
    (h8 : 0 < Sa)
    (h9 : ((((length sstr) : Nat) : Int) + 1) ≤ (2 ^ (43 : Nat)))
    (h10 : (cells_size dcs) = 40)
    (h11 : ((((length sstr) : Nat) : Int) + 1) ≤ 64)
    (h12 : (Int.toNat ((sh ((Sa + ((((length sstr) : Nat) : Int) + 1)) - 1)) - c)) = k)
    (h13 : ((sh Sa) ≤ c ∧ c < (sh ((Sa + ((((length sstr) : Nat) : Int) + 1)) - 1))))
    (h14 : (sh ((Sa + ((((length sstr) : Nat) : Int) + 1)) - 1)) = (2147450880 + (Z_shiftr ((Sa + ((((length sstr) : Nat) : Int) + 1)) + (-1)) 3))) :
    ((Sa + ((((length sstr) : Nat) : Int) + 1)) - 1) = ((Sa + ((((length sstr) : Nat) : Int) + 1)) + (-1)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ICP/I_sscanf.v (replace)
example (q : Int) :
    (q - 3408) = ((q + (-112)) - 3296) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ICP/IcptKit.v (assert)
example
    (off : Int)
    (k : Int)
    (h1 : (0 ≤ off ∧ off < 8))
    (h2 : (k = 0 ∨ ((0 < k ∧ k < 8) ∧ off < k)))
    (h3 : (k = 0 ∨ (k = 1 ∨ (k = 2 ∨ (k = 3 ∨ (k = 4 ∨ (k = 5 ∨ (k = 6 ∨ k = 7)))))))) :
    (off = 0 ∨ (off = 1 ∨ (off = 2 ∨ (off = 3 ∨ (off = 4 ∨ (off = 5 ∨ (off = 6 ∨ off = 7))))))) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ICP/N_shgetc_B.v (replace)
example
    (T : Int)
    (p : Int)
    (off : Int)
    (RG : Int)
    (win : Int → Int → Int)
    (h1 : (1 ≤ RG ∧ ((T + off) + RG) ≤ ((T + p) + 1)))
    (h2 : (win p off) = p)
    (h3 : off = p) :
    0 = ((T + p) - (T + off)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/T7A0/F_printf_core_dloop.v (replace)
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
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (alloc_ceiling : Int)
    (x : Int)
    (dec_digits : Int → list_Z)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 136160)
    (h5 : ((702928 ≤ Fp ∧ (Fp + 232) ≤ 6321648) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6321656 ≤ B ∧ (B + BS) ≤ alloc_ceiling) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : alloc_ceiling ≤ lo)
    (h12 : (x / 10) < 1844674407370955162)
    (h13 : 2 ≤ (zlength (dec_digits x))) :
    ((q + (-392)) + (j - 1)) = (((q + (-392)) + j) + (-1)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/T7A0/F_printf_core_xloop.v (replace)
example
    {list_Z T2 : Type}
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
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (alloc_ceiling : Int)
    (x : Int)
    (hex_digits : T2 → Int → list_Z)
    (l : T2)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 136160)
    (h5 : ((702928 ≤ Fp ∧ (Fp + 232) ≤ 6321648) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((6321656 ≤ B ∧ (B + BS) ≤ alloc_ceiling) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : alloc_ceiling ≤ lo)
    (h12 : (x / 16) < 1152921504606846976)
    (h13 : 1 ≤ (zlength (hex_digits l x))) :
    ((q + (-392)) + (j - 1)) = (((q + (-392)) + j) + (-1)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/T7A0/RF_mainA_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (DATA : T1)
    (RSVA : Int)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (LEN : Int)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (arg1 : T1)
    (bs : T1)
    (h1 : RSVA = 6122384)
    (h2 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h3 : LEN = (((length DATA) : Nat) : Int))
    (h4 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h5 : 0 ≤ LEN)
    (h6 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536))
    (h7 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h8 : (length bs) ≠ 0) :
    (length DATA) = ((length DATA) + 0) := by
  lia

-- pupnp/FuzzHttp: lib/B0/T7A0/RF_mainA_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (A : Int)
    (LEN : Int)
    (length : T1 → Nat)
    (DATA : T1)
    (RSVA : Int)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (arg1 : T1)
    (bs : T1)
    (h1 : RSVA = 6122384)
    (h2 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h3 : LEN = (((length DATA) : Nat) : Int))
    (h4 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h5 : 0 ≤ LEN)
    (h6 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536))
    (h7 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h8 : (length bs) ≠ 0) :
    (A + LEN) = (A + (((length DATA) : Nat) : Int)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/T7A0/RF_mainA_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (rd_cap : T1 → Int)
    (st1 : T1)
    (LEN : Int)
    (length : T2 → Nat)
    (bs : T2)
    (DATA : T2)
    (RSVA : Int)
    (zlength : T3 → Int)
    (rd_content : T1 → T3)
    (CNT : Int)
    (arg1 : T2)
    (h1 : RSVA = 6122384)
    (h2 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h3 : LEN = (((length DATA) : Nat) : Int))
    (h4 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h5 : 0 ≤ LEN)
    (h6 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536))
    (h7 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h8 : (length bs) ≠ 0) :
    ((Int.toNat ((rd_cap st1) - LEN)) - (length bs)) = (Int.toNat ((rd_cap st1) - ((((length DATA) + (length bs)) : Nat) : Int))) := by
  lia

-- pupnp/FuzzHttp: lib/B0/T7G/GlueAllocKit.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (x : Int)
    (a : Int)
    (length : T1 → Nat)
    (cbytes : T2 → T1)
    (cellw : T3 → T4 → T2)
    (w : T3)
    (v : T4)
    (h1 : (Int.toNat (x - a)) < (length (cbytes (cellw w v)))) :
    x = (a + (x - a)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ZAA/ADepot.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (j : Nat)
    (head_of : T1 → T2 → Int)
    (firstn : T3 → T4 → T1)
    (k : T3)
    (hs : T4)
    (b : T2)
    (h1 : (head_of (firstn k hs) b) ≠ (((j : Nat) : Int) + 1)) :
    j = (Int.toNat ((((j : Nat) : Int) + 1) - 1)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ZAA/F_prim_cdealloc.v (replace)
example
    (spacebeg : Int)
    (v : Int)
    (c : Int)
    (pcl : Int)
    (CB : Int)
    (Z_shiftr : Int → Int → Int)
    (Z_shiftl : Int → Int → Int)
    (h1 : pcl = (CB + (80 * c)))
    (h2 : (Z_shiftr ((((((spacebeg + (c * 4294967296)) + (16 * v)) - ((Z_shiftl c 32) % 18446744073709551616)) % 18446744073709551616) - spacebeg) % 18446744073709551616) 4) = v) :
    (spacebeg + (16 * v)) = (((spacebeg + (c * 4294967296)) + (16 * v)) - (c * 4294967296)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ZAA/F_prim_popf.v (replace)
example
    {T1 T2 : Type}
    (i : Int)
    (class_size : T1 → Int)
    (c : T1)
    (fa_base : T2 → T1 → Int)
    (AL : T2)
    (region : T2 → T1 → Int)
    (FA_OFF : Int)
    (cnt : Int)
    (h1 : (fa_base AL c) = ((region AL c) + FA_OFF))
    (h2 : (0 ≤ (i * (class_size c)) ∧ ((i * (class_size c)) + (class_size c)) ≤ (cnt * (class_size c)))) :
    ((i + 1) * (class_size c)) = ((i * (class_size c)) + (class_size c)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ZAA/F_quar_E.v (replace)
example
    {T1 T2 T3 : Type}
    (qb_addr : T1 → T2 → Int)
    (AL : T1)
    (b : T2)
    (qb_count : T2 → Int)
    (length : T3 → Nat)
    (l : T3)
    (l' : T3)
    (sh : Int → Int)
    (al_space : T1 → Int)
    (K_REGION : Int)
    (Q_BBYTES : Int)
    (K_SPACE : Int)
    (qlast : T1 → T3 → Int)
    (h1 : (((length l) : Nat) : Int) = ((((length l') : Nat) : Int) + 1))
    (h2 : (2147450880 ≤ (sh (qb_addr AL b)) ∧ ((sh (qb_addr AL b)) + 1024) ≤ 17594333495296))
    (h3 : (((al_space AL) + K_REGION) ≤ (qb_addr AL b) ∧ ((qb_addr AL b) + Q_BBYTES) ≤ ((al_space AL) + K_SPACE)))
    (h4 : (qlast AL l) = (qb_addr AL b))
    (h5 : 0 ≤ (qb_count b)) :
    ((((qb_addr AL b) + 24) + (8 * (qb_count b))) + (-24)) = ((qb_addr AL b) + ((qb_count b) * 8)) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ZAA/F_quar_P.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (q : Int)
    (lo : Int)
    (ENQ_STACK : Int)
    (DRAIN_STACK : Int)
    (qc_hdr : T1 → T2 → Int)
    (AL : T1)
    (ch : T2)
    (B : Int)
    (rz : Int)
    (rup8 : Int → Int)
    (n : Int)
    (M : Int)
    (sh : Int → Int)
    (bs : Int)
    (sc_beg : T3 → Int)
    (sc : T3)
    (glob : T4)
    (loc : T4)
    (qbytes : T4 → Int)
    (loc' : T4)
    (pq_drains : T5 → T4 → T2 → Bool)
    (P : T5)
    (h1 : lo ≤ ((q - 80) - ENQ_STACK))
    (h2 : lo ≤ ((q - 80) - DRAIN_STACK))
    (h3 : lo ≤ ((q - 80) - 64))
    (h4 : (qc_hdr AL ch) = ((B + rz) - 16))
    (h5 : (0 ≤ (rup8 n) ∧ (((rup8 n) % 8) = 0 ∧ n ≤ (rup8 n))))
    (h6 : ((M + 16) % 8) = 0)
    (h7 : (2147450880 ≤ (sh (M + 16)) ∧ ((sh (M + 16)) + ((rup8 n) / 8)) ≤ 17594333495296))
    (h8 : (M + 16) = (B + rz))
    (h9 : (sh (M + 16)) = ((sh B) + (rz / 8)))
    (h10 : (sh ((M + 16) + (rup8 n))) = ((sh (M + 16)) + ((rup8 n) / 8)))
    (h11 : (2147450880 ≤ (sh B) ∧ ((sh B) + (bs / 8)) ≤ 17594333495296))
    (h12 : ((sh (M + 16)) + ((rup8 n) / 8)) ≤ ((sh B) + (bs / 8)))
    (h13 : 0 ≤ ((rup8 n) / 8))
    (h14 : 0 ≤ (((bs - rz) - (rup8 n)) / 8))
    (h15 : (((sh (M + 16)) + ((rup8 n) / 8)) + (((bs - rz) - (rup8 n)) / 8)) ≤ ((sh B) + (bs / 8)))
    (h16 : B = ((sc_beg sc) + 4096))
    (h17 : (sh B) = ((sh (sc_beg sc)) + 512))
    (h18 : 0 ≤ (rz / 8))
    (h19 : ((q - 80) % 16) = 0)
    (h20 : lo ≤ (q - 80))
    (h21 : (0 ≤ (qbytes loc') ∧ (qbytes loc') < (2 ^ (56 : Nat))))
    (h22 : 0 ≤ (qbytes glob))
    (h23 : 0 ≤ (qbytes loc))
    (h24 : (pq_drains P loc ch) = false)
    (h25 : (0 ≤ (qbytes loc') ∧ (((qbytes glob) + (qbytes loc')) < (2 ^ (56 : Nat)) ∧ 0 ≤ (qbytes glob))))
    (h26 : (pq_drains P loc ch) = true) :
    q = ((q - 80) + 80) := by
  lia

-- pupnp/FuzzHttp: lib/B0/ZAA/F_sec_A.v (replace)
example
    {T1 : Type}
    (r : Int)
    (size : Int)
    (rup4k : Int → Int)
    (sec_msize : Int → Int)
    (lo : Int)
    (sh : Int → Int)
    (K8 : Int)
    (Z8 : Int)
    (al_parr : T1 → Int)
    (AL : T1)
    (h1 : (size ≤ (rup4k size) ∧ (rup4k size) < (size + 4096)))
    (h2 : (sec_msize size) = ((rup4k size) + 4096))
    (h3 : (r + (sec_msize size)) ≤ lo)
    (h4 : (sh (r + (sec_msize size))) = (((sh r) + 512) + K8))
    (h5 : (sh ((4096 + r) + size)) = (((sh r) + 512) + Z8))
    (h6 : ((r + (sec_msize size)) ≤ (sh r) ∨ (((sh r) + 512) + K8) ≤ r))
    (h7 : ((((sh r) + 512) + K8) ≤ (al_parr AL) ∨ ((al_parr AL) + (2 ^ (23 : Nat))) ≤ (sh r)))
    (h8 : (((rup4k size) - size) / 8) = (K8 - Z8)) :
    r = ((4096 + r) - 4096) := by
  lia

-- pupnp/FuzzHttp: lib/P0/AllocRealloc.v (replace)
example
    {T1 : Type}
    (sz : Int)
    (A : Int)
    (A' : Int)
    (n : Int)
    (length : T1 → Nat)
    (old : T1)
    (junk : T1)
    (h1 : ((A + sz) ≤ A' ∨ (A' + n) ≤ A))
    (h2 : (length old) = (Int.toNat sz))
    (h3 : (length junk) = (Int.toNat n)) :
    sz = ((A + sz) - A) := by
  lia

-- pupnp/FuzzHttp: lib/P0/F_memmove.v (replace)
example
    {word list_byte T3 T4 : Type}
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (U : Int)
    (us : list_byte)
    (bv_unsigned : word → Int)
    (k : Nat)
    (length : list_byte → Nat)
    (usF : list_byte → T3 → T4 → Nat → list_byte)
    (sof : T3)
    (dof : T4)
    (h1 : 8 ≤ U)
    (h2 : (U ≤ (bv_unsigned a1) ∧ ((bv_unsigned a1) + (bv_unsigned a2)) ≤ (U + (((length us) : Nat) : Int))))
    (h3 : (U ≤ (bv_unsigned a0) ∧ ((bv_unsigned a0) + (bv_unsigned a2)) ≤ (U + (((length us) : Nat) : Int))))
    (h4 : (bv_unsigned a2) < (2 ^ (62 : Nat)))
    (h5 : (length (usF us sof dof k)) = (length us)) :
    ((bv_unsigned a1) + (((k + 1) : Nat) : Int)) = (((bv_unsigned a1) + ((k : Nat) : Int)) + 1) := by
  lia

-- pupnp/FuzzHttp: lib/P0/F_memmove.v (replace)
example
    {word list_byte T3 T4 : Type}
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (U : Int)
    (us : list_byte)
    (bv_unsigned : word → Int)
    (k : Nat)
    (length : list_byte → Nat)
    (usF : list_byte → T3 → T4 → Nat → list_byte)
    (sof : T3)
    (dof : T4)
    (ch : list_byte)
    (h1 : 8 ≤ U)
    (h2 : (U ≤ (bv_unsigned a1) ∧ ((bv_unsigned a1) + (bv_unsigned a2)) ≤ (U + (((length us) : Nat) : Int))))
    (h3 : (U ≤ (bv_unsigned a0) ∧ ((bv_unsigned a0) + (bv_unsigned a2)) ≤ (U + (((length us) : Nat) : Int))))
    (h4 : (bv_unsigned a2) < (2 ^ (62 : Nat)))
    (h5 : (length (usF us sof dof k)) = (length us))
    (h6 : (length ch) = 8) :
    ((bv_unsigned a2) - (((k + 8) : Nat) : Int)) = (((bv_unsigned a2) - ((k : Nat) : Int)) + (-8)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/F_printf_core_dloop.v (replace)
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
    (h3 : q ≤ (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 131072)
    (h5 : ((169568 ≤ Fp ∧ (Fp + 232) ≤ 372632) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((372640 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (x / 10) < 1844674407370955162)
    (h12 : 2 ≤ (zlength (dec_digits x))) :
    (Int.toNat (j - ((zlength W') + 1))) = (Int.toNat ((j - 1) - (zlength W'))) := by
  lia

-- pupnp/FuzzHttp: lib/P0/F_printf_core_xloop.v (replace)
example
    {list_Z T2 : Type}
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
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (x : Int)
    (hex_digits : T2 → Int → list_Z)
    (l : T2)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q ≤ (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 131072)
    (h5 : ((169568 ≤ Fp ∧ (Fp + 232) ≤ 372632) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((372640 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (x / 16) < 1152921504606846976)
    (h12 : 1 ≤ (zlength (hex_digits l x))) :
    ((q + (-392)) + (j - 1)) = (((q + (-392)) + j) + (-1)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/F_shgetc_B.v (replace)
example
    {T1 : Type}
    (p : Int)
    (off : Int)
    (T : Int)
    (length : T1 → Nat)
    (zbytes : T1 → T1)
    (txt : T1)
    (pre : T1)
    (post : T1)
    (firstn : Nat → T1 → T1)
    (k : Nat)
    (skipn : Nat → T1 → T1)
    (win : Int → Int → Int)
    (h1 : (length (zbytes txt)) = (length txt))
    (h2 : (length txt) = ((length pre) + ((length post) + 1)))
    (h3 : (length (firstn k (zbytes pre))) = k)
    (h4 : (length (zbytes (skipn k pre))) = ((length pre) - k))
    (h5 : (win p off) = p)
    (h6 : off = p) :
    (p - off) = ((T + p) - (T + off)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/F_stdio_write.v (replace)
example
    {T1 : Type}
    (length : T1 → Nat)
    (skipn : Nat → T1 → T1)
    (k : Int)
    (n0 : Int)
    (b1 : T1)
    (n1 : Int)
    (to_bytes : T1 → T1)
    (b0 : T1)
    (h1 : (length (to_bytes b0)) = (length b0))
    (h2 : (length (to_bytes b1)) = (length b1))
    (h3 : (n0 - k) = (((length (skipn (Int.toNat k) b0)) : Nat) : Int))
    (h4 : (n1 - (k - n0)) = (((length (skipn (Int.toNat (k - n0)) b1)) : Nat) : Int)) :
    (((length (skipn (Int.toNat (k - n0)) b1)) : Nat) : Int) = ((n0 + n1) - k) := by
  lia

-- pupnp/FuzzHttp: lib/P0/F_stpncpy.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (a0 : word)
    (a1 : word)
    (a2 : word)
    (str : list_byte)
    (slack : list_byte)
    (lo : Int)
    (bv_unsigned : word → Int)
    (i : Nat)
    (length : list_byte → Nat)
    (h1 : ((-(((bv_unsigned a1) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length slack) : Nat) : Int))
    (h2 : (((bv_unsigned a0) + (bv_unsigned a2)) ≤ (bv_unsigned a1) ∨ ((((bv_unsigned a1) + (((length str) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ (bv_unsigned a0)))
    (h3 : (((bv_unsigned a0) + (bv_unsigned a2)) ≤ lo ∨ (bv_unsigned sp) ≤ (bv_unsigned a0)))
    (h4 : (((((bv_unsigned a1) + (((length str) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ ((bv_unsigned sp) - 16) ∨ (bv_unsigned sp) ≤ (bv_unsigned a1)))
    (h5 : lo ≤ ((bv_unsigned sp) - 16))
    (h6 : (0 ≤ (bv_unsigned a0) ∧ (((bv_unsigned a0) + (bv_unsigned a2)) < (2 ^ (64 : Nat)) ∧ (0 ≤ (bv_unsigned a1) ∧ (((((bv_unsigned a1) + (((length str) : Nat) : Int)) + 1) + (((length slack) : Nat) : Int)) ≤ (2 ^ (64 : Nat)) ∧ (0 ≤ lo ∧ ((bv_unsigned sp) < (2 ^ (64 : Nat)) ∧ 0 ≤ (bv_unsigned a2)))))))) :
    (((bv_unsigned a1) + (((i + 1) : Nat) : Int)) + 1) = (((bv_unsigned a1) + ((i : Nat) : Int)) + 2) := by
  lia

-- pupnp/FuzzHttp: lib/P0/H_membuffer_assign.v (assert)
example
    (cap : Int)
    (MB : Int)
    (B : Int)
    (A : Int)
    (h1 : (MB + 32) ≤ B)
    (h2 : (0 ≤ A ∧ A < (2 ^ (64 : Nat)))) :
    cap ≤ ((cap + 0) + 5) := by
  lia

-- pupnp/FuzzHttp: lib/P0/H_memptr_cmp.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    (((bv_unsigned sp) + (-32)) - 48) = ((bv_unsigned sp) - 80) := by
  lia

-- pupnp/FuzzHttp: lib/P0/H_parse_uri_B.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (length : T2 → Nat)
    (rest : T2)
    (ulen : Int)
    (bh2 : Int)
    (str : T2)
    (slack : T2)
    (U : Int)
    (wb : T2)
    (zn : Nat)
    (h1 : (((length rest) : Nat) : Int) = (((ulen - bh2) - (((length str) : Nat) : Int)) + (((length slack) : Nat) : Int)))
    (h2 : ((-(((U + bh2) + (((length str) : Nat) : Int)) + 1)) % 8) ≤ (((length rest) : Nat) : Int))
    (h3 : (length wb) = 256)
    (h4 : (zn ≤ (length str) ∧ zn ≤ 255)) :
    (((bv_unsigned sp) + (-384)) + 24) = ((bv_unsigned sp) + (-360)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/H_pent_B.v (lemma)
example
    {alloc_if_rsegs T2 T3 : Type}
    (AI : alloc_if_rsegs)
    (P : Int)
    (q : Int)
    (lo : Int)
    (B : Int)
    (al_realloc_pc : T2 → Int)
    (ai_L : T3 → alloc_if_rsegs → T2)
    (rsegs : T3)
    (al_tp : T2 → Int)
    (al_errno : T2 → Int)
    (al_stack : T2 → Int)
    (alloc_ceiling : Int)
    (h1 : (al_realloc_pc (ai_L rsegs AI)) = 101992)
    (h2 : (al_tp (ai_L rsegs AI)) = 240944)
    (h3 : (al_errno (ai_L rsegs AI)) = 240780)
    (h4 : (lo + 2384) ≤ q)
    (h5 : lo ≤ ((q - 32) - (al_stack (ai_L rsegs AI))))
    (h6 : 0 ≤ (al_stack (ai_L rsegs AI)))
    (h7 : 376832 ≤ lo)
    (h8 : alloc_ceiling ≤ lo)
    (h9 : (q + 144) ≤ P)
    (h10 : (P + 504) ≤ B)
    (h11 : B < (2 ^ (62 : Nat))) :
    (P + 504) < (2 ^ (63 : Nat)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/H_phdr_C.v (replace)
example
    {T1 : Type}
    (P : Int)
    (length : T1 → Nat)
    (bs : T1)
    (len : Int)
    (cur : Int)
    (A : Int)
    (cap : Int)
    (LMAX : Int)
    (lo : Int)
    (h1 : ((((length bs) : Nat) : Int) ≥ len ∧ ((0 ≤ cur ∧ cur < (2 ^ (64 : Nat))) ∧ (((A + cap) + 1) < (2 ^ (63 : Nat)) ∧ ((len + 1) ≤ LMAX ∧ (LMAX = ((2 ^ (26 : Nat)) + 16) ∧ (A + (((length bs) : Nat) : Int)) ≤ lo))))))
    (h2 : (((A + (cap + 1)) ≤ 65536 ∨ 167936 ≤ A) ∧ ((A + (cap + 1)) ≤ 167936 ∨ 376832 ≤ A)))
    (h3 : (length bs) = (Int.toNat (cap + 1))) :
    (P + 368) = ((P + 288) + 80) := by
  lia

-- pupnp/FuzzHttp: lib/P0/H_phdr_C.v (replace)
example
    {T1 : Type}
    (cur : Int)
    (tlz : Int)
    (A : Int)
    (length : T1 → Nat)
    (bs : T1)
    (len : Int)
    (cap : Int)
    (LMAX : Int)
    (lo : Int)
    (full : T1)
    (str : T1)
    (sl : T1)
    (h1 : ((((length bs) : Nat) : Int) ≥ len ∧ ((0 ≤ cur ∧ cur < (2 ^ (64 : Nat))) ∧ (((A + cap) + 1) < (2 ^ (63 : Nat)) ∧ ((len + 1) ≤ LMAX ∧ (LMAX = ((2 ^ (26 : Nat)) + 16) ∧ (A + (((length bs) : Nat) : Int)) ≤ lo))))))
    (h2 : (((A + (cap + 1)) ≤ 65536 ∨ 167936 ≤ A) ∧ ((A + (cap + 1)) ≤ 167936 ∨ 376832 ≤ A)))
    (h3 : (length bs) = (Int.toNat (cap + 1)))
    (h4 : (((length str) : Nat) : Int) ≤ tlz)
    (h5 : (((length full) : Nat) : Int) = (((cap + 1) - cur) + (((length sl) : Nat) : Int))) :
    (Int.toNat (cur + tlz)) = (Int.toNat (((A + cur) + tlz) - A)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/H_reql_B.v (replace)
example
    (q : Int)
    (A : Int)
    (cap : Int)
    (round_up8 : Int → Int)
    (alloc_ceiling : Int)
    (h1 : (((A + (cap + 1)) ≤ (round_up8 (A + (cap + 1))) ∧ (round_up8 (A + (cap + 1))) ≤ ((A + (cap + 1)) + 7)) ∧ (((round_up8 (A + (cap + 1))) % 8) = 0 ∧ ((round_up8 (A + (cap + 1))) ≤ alloc_ceiling ∧ ((A + (cap + 1)) ≤ 167936 → (round_up8 (A + (cap + 1))) ≤ 167936))))) :
    (q + 64) = ((q + 56) + ((8 : Nat) : Int)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_free.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 : Type}
    (r_base : T1 → Int)
    (r : T1)
    (snd : T2 → Int)
    (q : T2)
    (j : Int)
    (off' : Int)
    (off : Int)
    (pf : T2)
    (b : T2)
    (conc : T3 → T2 → Int)
    (st : T3)
    (c0 : T2)
    (blk_addr : T4 → Int)
    (blk : T4)
    (get_stride : T5 → Int)
    (get_meta_rec : T3 → T6 → T5)
    (g : T6)
    (i : Int)
    (m_last_idx : T5 → Int)
    (round_up_pg : T7 → Int)
    (r_len : T1 → T7)
    (stq : Int)
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
    (h14 : ((((r_base r) + (round_up_pg (r_len r))) ≤ 65536 ∨ 167936 ≤ (r_base r)) ∧ (((r_base r) + (round_up_pg (r_len r))) ≤ 167936 ∨ 376832 ≤ (r_base r))))
    (h15 : (conc st b) = ((r_base r) + (snd b))) :
    ((r_base r) + ((snd q) + j)) = (((r_base r) + (snd q)) + j) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_main_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (RSV : Int)
    (CNT : Int)
    (zlength : T1 → Int)
    (rd_content : T2 → T1)
    (st1 : T2)
    (length : T3 → Nat)
    (DATA : T3)
    (LEN : Int)
    (rd_cap : T2 → Int)
    (h1 : RSV = 175065)
    (h2 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h3 : LEN = (((length DATA) : Nat) : Int))
    (h4 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h5 : 0 ≤ LEN)
    (h6 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536)) :
    RSV = ((RSV + CNT) - (((Int.toNat CNT) : Nat) : Int)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_main_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (DATA : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (LEN : Int)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (arg1 : T1)
    (bs : T1)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int))
    (h3 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h4 : 0 ≤ LEN)
    (h5 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536))
    (h6 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h7 : (length bs) ≠ 0) :
    (length DATA) = ((length DATA) + 0) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_main_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (length : T1 → Nat)
    (bs : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (DATA : T1)
    (LEN : Int)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (arg1 : T1)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int))
    (h3 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h4 : 0 ≤ LEN)
    (h5 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536))
    (h6 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h7 : (length bs) ≠ 0) :
    (length bs) = (Int.toNat (((length bs) : Nat) : Int)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_main_B2.v (replace)
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
    (arg1 : T1)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int))
    (h3 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h4 : 0 ≤ LEN)
    (h5 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536))
    (h6 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h7 : (length bs) ≠ 0) :
    (LEN + (((length bs) : Nat) : Int)) = ((((length bs) : Nat) : Int) + LEN) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_main_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (A : Int)
    (LEN : Int)
    (length : T1 → Nat)
    (DATA : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (arg1 : T1)
    (bs : T1)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int))
    (h3 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h4 : 0 ≤ LEN)
    (h5 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536))
    (h6 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h7 : (length bs) ≠ 0) :
    (A + LEN) = (A + (((length DATA) : Nat) : Int)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_main_B2.v (replace)
example
    {T1 T2 T3 : Type}
    (A : Int)
    (length : T1 → Nat)
    (DATA : T1)
    (bs : T1)
    (zlength : T2 → Int)
    (rd_content : T3 → T2)
    (st1 : T3)
    (LEN : Int)
    (CNT : Int)
    (rd_cap : T3 → Int)
    (arg1 : T1)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : LEN = (((length DATA) : Nat) : Int))
    (h3 : CNT = (min ((rd_cap st1) - LEN) 65536))
    (h4 : 0 ≤ LEN)
    (h5 : ((0 < CNT ∧ CNT ≤ ((rd_cap st1) - LEN)) ∧ CNT ≤ 65536))
    (h6 : (((length arg1) : Nat) : Int) ≤ 131071)
    (h7 : (length bs) ≠ 0) :
    ((A + (((length DATA) : Nat) : Int)) + (((length bs) : Nat) : Int)) = (A + (((((length DATA) + (length bs)) + 0) : Nat) : Int)) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_realloc_ip.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (r_base : T1 → Int)
    (r : T1)
    (snd : T2 → Int)
    (c : T2)
    (stride : Int)
    (res : Int)
    (conc : T3 → T2 → Int)
    (st : T3)
    (bm : T2)
    (i : Int)
    (bo : Int)
    (off : Int)
    (A : Int)
    (UNIT : Int)
    (m_last_idx : T4 → Int)
    (mr : T4)
    (IB : Int)
    (E : Int)
    (round_up_pg : T5 → Int)
    (r_len : T1 → T5)
    (n : Int)
    (r5 : Int)
    (b3 : Int)
    (Z_land : Int → Int → Int)
    (Z_shiftr : Int → Int → Int)
    (m_sizeclass : T4 → Int)
    (h1 : bo = off)
    (h2 : (snd c) = (((snd bm) + 16) + (stride * i)))
    (h3 : (conc st c) = ((r_base r) + (snd c)))
    (h4 : A = (((r_base r) + (snd c)) + (UNIT * off)))
    (h5 : 0 ≤ (stride * i))
    (h6 : ((stride * i) + stride) ≤ ((stride * (m_last_idx mr)) + stride))
    (h7 : ((16 * off) + 16) ≤ stride)
    (h8 : (((A - (UNIT * off)) + stride) - IB) = E)
    (h9 : ((((snd c) + stride) - IB) + 1) ≤ (round_up_pg (r_len r)))
    (h10 : res = (((stride - IB) - (UNIT * off)) - n))
    (h11 : 0 ≤ res)
    (h12 : ((0 ≤ (min res 5) ∧ (min res 5) ≤ 5) ∧ (min res 5) ≤ res))
    (h13 : ((5 ≤ res → (min res 5) = 5) ∧ (res < 5 → (min res 5) = res)))
    (h14 : r5 = (min res 5))
    (h15 : b3 = (i + (32 * r5)))
    (h16 : (0 ≤ b3 ∧ b3 < 256))
    (h17 : (Z_land b3 31) = i)
    (h18 : (Z_shiftr b3 5) = r5)
    (h19 : (0 ≤ (m_sizeclass mr) ∧ (m_sizeclass mr) < 64))
    (h20 : (48 ≤ (m_sizeclass mr) → (m_sizeclass mr) = 63))
    (h21 : (0 ≤ (m_sizeclass mr) ∧ (m_sizeclass mr) < 48))
    (h22 : r5 < 5)
    (h23 : (conc st bm) = ((r_base r) + (snd bm)))
    (h24 : r5 = 5)
    (h25 : 5 ≤ res) :
    ((r_base r) + ((((snd c) + stride) - 4) - res)) = ((((((conc st bm) + 16) + (stride * i)) + stride) - 4) - res) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_realloc_mm.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (snd : T1 → Int)
    (c : T1)
    (UNIT : Int)
    (off : Int)
    (bo : Int)
    (st : T2)
    (bm : T1)
    (stride : Int)
    (i : Int)
    (conc : T2 → T1 → Int)
    (r_base : T3 → Int)
    (r : T3)
    (A : Int)
    (m_last_idx : T4 → Int)
    (mr : T4)
    (IB : Int)
    (round_up_pg : T5 → Int)
    (r_len : T3 → T5)
    (res : Int)
    (n : Int)
    (r5 : Int)
    (b3 : Int)
    (Z_land : Int → Int → Int)
    (Z_shiftr : Int → Int → Int)
    (m_sizeclass : T4 → Int)
    (h1 : bo = off)
    (h2 : (snd c) = (((snd bm) + 16) + (stride * i)))
    (h3 : (conc st c) = ((r_base r) + (snd c)))
    (h4 : A = (((r_base r) + (snd c)) + (UNIT * off)))
    (h5 : 0 ≤ (stride * i))
    (h6 : ((stride * i) + stride) ≤ ((stride * (m_last_idx mr)) + stride))
    (h7 : ((16 * off) + 16) ≤ stride)
    (h8 : ((((snd c) + stride) - IB) + 1) ≤ (round_up_pg (r_len r)))
    (h9 : res = (((stride - IB) - (UNIT * off)) - n))
    (h10 : 0 ≤ res)
    (h11 : ((0 ≤ (min res 5) ∧ (min res 5) ≤ 5) ∧ (min res 5) ≤ res))
    (h12 : ((5 ≤ res → (min res 5) = 5) ∧ (res < 5 → (min res 5) = res)))
    (h13 : r5 = (min res 5))
    (h14 : b3 = (i + (32 * r5)))
    (h15 : (0 ≤ b3 ∧ b3 < 256))
    (h16 : (Z_land b3 31) = i)
    (h17 : (Z_shiftr b3 5) = r5)
    (h18 : (0 ≤ (m_sizeclass mr) ∧ (m_sizeclass mr) < 64))
    (h19 : (48 ≤ (m_sizeclass mr) → (m_sizeclass mr) = 63)) :
    (((snd c) + (UNIT * off)) - 1) = (((snd c) + (UNIT * off)) - 1) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_realloc_mm.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (r_base : T1 → Int)
    (r : T1)
    (snd : T2 → Int)
    (c : T2)
    (stride : Int)
    (bo : Int)
    (off : Int)
    (st : T3)
    (bm : T2)
    (i : Int)
    (conc : T3 → T2 → Int)
    (A : Int)
    (UNIT : Int)
    (m_last_idx : T4 → Int)
    (mr : T4)
    (IB : Int)
    (round_up_pg : T5 → Int)
    (r_len : T1 → T5)
    (res : Int)
    (n : Int)
    (r5 : Int)
    (b3 : Int)
    (Z_land : Int → Int → Int)
    (Z_shiftr : Int → Int → Int)
    (m_sizeclass : T4 → Int)
    (h1 : bo = off)
    (h2 : (snd c) = (((snd bm) + 16) + (stride * i)))
    (h3 : (conc st c) = ((r_base r) + (snd c)))
    (h4 : A = (((r_base r) + (snd c)) + (UNIT * off)))
    (h5 : 0 ≤ (stride * i))
    (h6 : ((stride * i) + stride) ≤ ((stride * (m_last_idx mr)) + stride))
    (h7 : ((16 * off) + 16) ≤ stride)
    (h8 : ((((snd c) + stride) - IB) + 1) ≤ (round_up_pg (r_len r)))
    (h9 : res = (((stride - IB) - (UNIT * off)) - n))
    (h10 : 0 ≤ res)
    (h11 : ((0 ≤ (min res 5) ∧ (min res 5) ≤ 5) ∧ (min res 5) ≤ res))
    (h12 : ((5 ≤ res → (min res 5) = 5) ∧ (res < 5 → (min res 5) = res)))
    (h13 : r5 = (min res 5))
    (h14 : b3 = (i + (32 * r5)))
    (h15 : (0 ≤ b3 ∧ b3 < 256))
    (h16 : (Z_land b3 31) = i)
    (h17 : (Z_shiftr b3 5) = r5)
    (h18 : (0 ≤ (m_sizeclass mr) ∧ (m_sizeclass mr) < 64))
    (h19 : (48 ≤ (m_sizeclass mr) → (m_sizeclass mr) = 63))
    (h20 : (0 ≤ (m_sizeclass mr) ∧ (m_sizeclass mr) < 48))
    (h21 : r5 < 5)
    (h22 : (conc st bm) = ((r_base r) + (snd bm)))
    (h23 : r5 = 5)
    (h24 : 5 ≤ res) :
    ((r_base r) + ((((snd c) + stride) - 4) - 1)) = (((r_base r) + ((((snd c) + stride) - 4) - 4)) + 3) := by
  lia

-- pupnp/FuzzHttp: lib/P0/RF_realloc_mm.v (replace)
example
    {T1 T2 T3 T4 T5 : Type}
    (m_last_idx : T1 → Int)
    (mr : T1)
    (m_freeable : T1 → Int)
    (m_maplen : T1 → Int)
    (bo : Int)
    (off : Int)
    (st : T2)
    (bm : T3)
    (c : T3)
    (snd : T3 → Int)
    (stride : Int)
    (i : Int)
    (conc : T2 → T3 → Int)
    (r_base : T4 → Int)
    (r : T4)
    (A : Int)
    (UNIT : Int)
    (IB : Int)
    (round_up_pg : T5 → Int)
    (r_len : T4 → T5)
    (res : Int)
    (n : Int)
    (r5 : Int)
    (b3 : Int)
    (Z_land : Int → Int → Int)
    (Z_shiftr : Int → Int → Int)
    (m_sizeclass : T1 → Int)
    (h1 : bo = off)
    (h2 : (snd c) = (((snd bm) + 16) + (stride * i)))
    (h3 : (conc st c) = ((r_base r) + (snd c)))
    (h4 : A = (((r_base r) + (snd c)) + (UNIT * off)))
    (h5 : 0 ≤ (stride * i))
    (h6 : ((stride * i) + stride) ≤ ((stride * (m_last_idx mr)) + stride))
    (h7 : ((16 * off) + 16) ≤ stride)
    (h8 : ((((snd c) + stride) - IB) + 1) ≤ (round_up_pg (r_len r)))
    (h9 : res = (((stride - IB) - (UNIT * off)) - n))
    (h10 : 0 ≤ res)
    (h11 : ((0 ≤ (min res 5) ∧ (min res 5) ≤ 5) ∧ (min res 5) ≤ res))
    (h12 : ((5 ≤ res → (min res 5) = 5) ∧ (res < 5 → (min res 5) = res)))
    (h13 : r5 = (min res 5))
    (h14 : b3 = (i + (32 * r5)))
    (h15 : (0 ≤ b3 ∧ b3 < 256))
    (h16 : (Z_land b3 31) = i)
    (h17 : (Z_shiftr b3 5) = r5)
    (h18 : (0 ≤ (m_sizeclass mr) ∧ (m_sizeclass mr) < 64))
    (h19 : (48 ≤ (m_sizeclass mr) → (m_sizeclass mr) = 63))
    (h20 : (0 ≤ (m_sizeclass mr) ∧ (m_sizeclass mr) < 48))
    (h21 : r5 < 5)
    (h22 : (conc st bm) = ((r_base r) + (snd bm)))
    (h23 : r5 = 5)
    (h24 : 5 ≤ res)
    (h25 : i = 0) :
    ((((m_last_idx mr) + (32 * (m_freeable mr))) + 4032) + (4096 * (m_maplen mr))) = ((((m_last_idx mr) + (32 * (m_freeable mr))) + (64 * 63)) + (4096 * (m_maplen mr))) := by
  lia

-- simdjson/fuzz_atpointer: lib/A/Z52.v (replace)
example
    {T1 T2 T3 : Type}
    (sp' : Int)
    (Z_to_bv : Int → Int → T1)
    (n : Int)
    (d : Int)
    (vcost_pushes : Nat → Int → Int → Int)
    (bs : T2)
    (bv_unsigned : T1 → Int)
    (lo : Int)
    (zlength : T3 → Int)
    (chars : T2 → T3)
    (USTACK_TOP : Int)
    (length : T3 → Nat)
    (poffs : T3 → T3)
    (atp_P : T3 → Nat)
    (ATPA_SPLITINTO_STACK : Int)
    (P0 : Nat)
    (h1 : (0 ≤ n ∧ n < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h3 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h4 : (zlength (chars bs)) = n)
    (h5 : (zlength (chars bs)) < (2 ^ (26 : Nat)))
    (h6 : (bv_unsigned (Z_to_bv 64 sp')) ≤ (sp' + 80))
    (h7 : ((sp' + 80) + 24) ≤ USTACK_TOP)
    (h8 : ((sp' + 80) % 8) = 0)
    (h9 : (length (poffs (chars bs))) ≤ (atp_P (chars bs)))
    (h10 : (vcost_pushes (length (poffs (chars bs))) 0 0) ≤ (vcost_pushes (atp_P (chars bs)) 0 0))
    (h11 : (lo + ATPA_SPLITINTO_STACK) ≤ (bv_unsigned (Z_to_bv 64 sp')))
    (h12 : ((bv_unsigned (Z_to_bv 64 sp')) + 16) ≤ USTACK_TOP)
    (h13 : ((bv_unsigned (Z_to_bv 64 sp')) % 16) = 0)
    (h14 : (zlength (poffs (chars bs))) = ((P0 : Nat) : Int)) :
    (sp' + 96) = ((sp' + ((80 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_atpointer: lib/A/Z59.v (assert)
example
    {T1 T2 T3 : Type}
    (obj_costA : Nat → Int → Int)
    (TAPE_MAX_DEPTH : Nat)
    (zlength : T1 → Int)
    (chars : T2 → T1)
    (bsp : T2)
    (bv_unsigned : T3 → Int)
    (Z_to_bv : Int → Int → T3)
    (sp' : Int)
    (doc_len : T2 → Int)
    (bs : T2)
    (atp_s0 : T1 → T1)
    (P1 : Int)
    (length : T2 → Nat)
    (n : Int)
    (lo : Int)
    (a : T3)
    (arr_costA : Nat → Int → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h2 : (0 ≤ (doc_len bs) ∧ (doc_len bs) ≤ 1048512))
    (h3 : (0 ≤ (zlength (atp_s0 (chars bs))) ∧ (zlength (atp_s0 (chars bs))) < (2 ^ (64 : Nat))))
    (h4 : (0 ≤ P1 ∧ (P1 + (((length bsp) : Nat) : Int)) < (2 ^ (47 : Nat))))
    (h5 : (((length bsp) : Nat) : Int) ≤ n)
    (h6 : (zlength (chars bsp)) = (((length bsp) : Nat) : Int))
    (h7 : (bv_unsigned a) < lo)
    (h8 : (0 ≤ (arr_costA (TAPE_MAX_DEPTH - 1) (zlength (chars bsp))) ∧ (arr_costA (TAPE_MAX_DEPTH - 1) (zlength (chars bsp))) ≤ (obj_costA (TAPE_MAX_DEPTH - 1) (zlength (chars bsp))))) :
    (0 ≤ (obj_costA (TAPE_MAX_DEPTH - 1) (zlength (chars bsp))) ∧ (obj_costA (TAPE_MAX_DEPTH - 1) (zlength (chars bsp))) ≤ (obj_costA (TAPE_MAX_DEPTH - 1) (zlength (chars bsp)))) := by
  lia

-- simdjson/fuzz_atpointer: lib/A/Zon.v (replace)
example
    {word list_word : Type}
    (sp : word)
    (MB : Int)
    (MSZ : Int)
    (IDX : Int)
    (nres : Int)
    (n : Int)
    (LMB : Int)
    (lo : Int)
    (ws : list_word)
    (length : list_word → Nat)
    (kHighShadowEnd : Int)
    (bv_unsigned : word → Int)
    (h1 : ((MB % 4096) = 0 ∧ (65536 < MSZ ∧ (MSZ % 4096) = 0)))
    (h2 : (6721536 ≤ LMB ∧ (LMB + 32) ≤ lo))
    (h3 : (LMB = MB ∨ ((LMB + 32) ≤ MB ∨ (MB + MSZ) ≤ LMB)))
    (h4 : ((0 ≤ IDX ∧ IDX < n) ∧ (n ≤ nres ∧ ((((length ws) : Nat) : Int) = nres ∧ nres ≤ (2 ^ (20 : Nat))))))
    (h5 : (kHighShadowEnd + 8) ≤ lo)
    (h6 : lo ≤ ((bv_unsigned sp) - 32))
    (h7 : (bv_unsigned sp) ≤ (2 ^ (47 : Nat)))
    (h8 : 6721536 ≤ MB) :
    MB = ((MB + 4096) + (-4096)) := by
  lia

-- simdjson/fuzz_atpointer: lib/A/Zte.v (assert)
example
    {word : Type}
    (sp : word)
    (X : Int)
    (lo : Int)
    (d : Int)
    (spq : Int)
    (f : Int)
    (a : Int)
    (n : Int)
    (LMA_STACK : Int)
    (bv_unsigned : word → Int)
    (USTACK_TOP : Int)
    (h1 : (lo + LMA_STACK) ≤ (bv_unsigned sp))
    (h2 : ((bv_unsigned sp) + 16) ≤ USTACK_TOP)
    (h3 : ((d = 0 ∨ d = 16) ∧ spq = (((bv_unsigned sp) - 256) - d)))
    (h4 : ((f % 64) = 0 ∧ (6721536 ≤ f ∧ ((f + 2040) ≤ lo ∧ (((f + 2040) ≤ ((f / 8) + 2147450880) ∨ (((f / 8) + 2147450880) + 255) ≤ f) ∧ (0 ≤ ((f / 8) + 2147450880) ∧ (((f / 8) + 2147450880) + 255) ≤ lo))))))
    (h5 : (X % 8) = 0)
    (h6 : (6721536 ≤ X ∧ ((X + 504) ≤ lo ∧ (((X + 504) ≤ ((X / 8) + 2147450880) ∨ (((X / 8) + 2147450880) + 63) ≤ X) ∧ (0 ≤ ((X / 8) + 2147450880) ∧ (((X / 8) + 2147450880) + 63) ≤ lo)))))
    (h7 : (((X + 504) ≤ f ∨ (f + 2048) ≤ X) ∧ (((X + 504) ≤ ((f / 8) + 2147450880) ∨ (((f / 8) + 2147450880) + 256) ≤ X) ∧ (((((X / 8) + 2147450880) + 63) ≤ f ∨ (f + 2048) ≤ ((X / 8) + 2147450880)) ∧ ((((X / 8) + 2147450880) + 63) ≤ ((f / 8) + 2147450880) ∨ (((f / 8) + 2147450880) + 256) ≤ ((X / 8) + 2147450880))))))
    (h8 : 0 ≤ n)
    (h9 : (((a + n) ≤ (spq + 16) ∧ lo ≤ a) ∨ (((spq + 152) ≤ a ∧ (a + n) ≤ (bv_unsigned sp)) ∨ ((f ≤ a ∧ (a + n) ≤ (f + 528)) ∨ (((f / 8) + 2147450880) ≤ a ∧ (a + n) ≤ (((f / 8) + 2147450880) + 67)))))) :
    (0 ≤ d ∧ d ≤ 16) := by
  lia

-- simdjson/fuzz_atpointer: lib/B/Z3t.v (replace)
example {aenvA : Type} (E : aenvA) (i : Int) (ae_n : aenvA → Int) (h1 : (0 ≤ i ∧ i < (ae_n E))) :
    (8 * (Int.toNat i)) = (Int.toNat (8 * i)) := by
  lia

-- simdjson/fuzz_atpointer: lib/B/Z4v.v (replace)
example (Do : Int) (pos : Int) :
    (Do + (pos + 4)) = ((pos + 4) + Do) := by
  lia

-- simdjson/fuzz_atpointer: lib/B/Z4v.v (replace)
example
    {T1 : Type}
    (usp : Int)
    (Z_to_bv : Int → Int → T1)
    (bv_unsigned : T1 → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 (usp + (-80)))) = (usp + (-80))) :
    (usp + (-56)) = ((usp + (-80)) + ((24 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_atpointer: lib/B/Zj0.v (replace)
example
    {T1 : Type}
    (usp : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (h1 : (bv_unsigned (Z_to_bv 64 (usp + (-2128)))) = (usp + (-2128))) :
    (usp + (-2208)) = ((usp + (-2128)) - 80) := by
  lia

-- simdjson/fuzz_atpointer: lib/B/Zk3.v (replace)
example
    {T1 : Type}
    (s_mb : T1 → Int)
    (s : T1)
    (ru8 : Int → Int)
    (s_n : T1 → Int)
    (shad : Int → Int)
    (h1 : (8 ≤ (ru8 (s_n s)) ∧ ((ru8 (s_n s)) % 8) = 0))
    (h2 : 1 ≤ (((s_n s) + 7) / 8))
    (h3 : ((s_mb s) % 8) = 0)
    (h4 : (shad (((s_mb s) + 6128) + 16)) = ((shad (s_mb s)) + (6144 / 8))) :
    ((s_mb s) + 6144) = (((s_mb s) + 6128) + 16) := by
  lia

-- simdjson/fuzz_atpointer: lib/B/Zzt.v (replace)
example
    {s2env T2 T3 : Type}
    (E : s2env)
    (t40 : Int)
    (i48 : Int)
    (sbv : Int)
    (i : Int)
    (j : Int)
    (kk : Int)
    (Wv : Int)
    (fuel : Nat)
    (p : Int)
    (e_BUF : s2env → Int)
    (length : T2 → Nat)
    (e_sbs : s2env → T2)
    (e_scap : s2env → Int)
    (e_TAPE : s2env → Int)
    (e_IDX : s2env → Int)
    (e_bs : s2env → T3)
    (B : T3 → Int → Int)
    (t : Nat)
    (h1 : (((length (e_sbs E)) : Nat) : Int) = sbv)
    (h2 : (0 ≤ sbv ∧ ((sbv + (j - i)) + 4) ≤ (e_scap E)))
    (h3 : 0 ≤ i)
    (h4 : t40 = ((e_TAPE E) + (8 * Wv)))
    (h5 : i48 = ((e_IDX E) + (4 * (kk + 1))))
    (h6 : (B (e_bs E) p) = 92)
    (h7 : (j - p) < (((fuel + 1) : Nat) : Int))
    (h8 : (t = 8 ∨ (t = 9 ∨ (t = 10 ∨ t = 11)))) :
    ((e_BUF E) + (p + 12)) = (((e_BUF E) + p) + 12) := by
  lia

-- simdjson/fuzz_atpointer: lib/P/Z8l.v (replace)
example
    {rd_st T2 T3 : Type}
    (TID : Int)
    (fd : Int)
    (st : rd_st)
    (length : T2 → Nat)
    (DATA : T2)
    (zlength : T3 → Int)
    (rd_content : rd_st → T3)
    (rd_cap : rd_st → Int)
    (A' : Int)
    (A : Int)
    (h1 : (0 < TID ∧ TID < 4194304))
    (h2 : (3 ≤ fd ∧ fd < (2 ^ (32 : Nat))))
    (h3 : (zlength (rd_content st)) = (((length DATA) : Nat) : Int))
    (h4 : 67108864 ≤ (rd_cap st))
    (h5 : (rd_cap st) < 67108864)
    (h6 : ((A' + ((rd_cap st) * 2)) ≤ A ∨ (A + (rd_cap st)) ≤ A')) :
    (Int.toNat (((length DATA) : Nat) : Int)) = (length DATA) := by
  lia

-- simdjson/fuzz_atpointer: lib/P/Z8l.v (replace)
example
    {rd_st T2 T3 : Type}
    (TID : Int)
    (fd : Int)
    (st : rd_st)
    (rd_cap : rd_st → Int)
    (length : T2 → Nat)
    (DATA : T2)
    (zlength : T3 → Int)
    (rd_content : rd_st → T3)
    (A' : Int)
    (A : Int)
    (h1 : (0 < TID ∧ TID < 4194304))
    (h2 : (3 ≤ fd ∧ fd < (2 ^ (32 : Nat))))
    (h3 : (zlength (rd_content st)) = (((length DATA) : Nat) : Int))
    (h4 : 67108864 ≤ (rd_cap st))
    (h5 : (rd_cap st) < 67108864)
    (h6 : ((A' + ((rd_cap st) * 2)) ≤ A ∨ (A + (rd_cap st)) ≤ A')) :
    ((Int.toNat ((rd_cap st) * 2)) - (length DATA)) = (Int.toNat (((rd_cap st) * 2) - (((length DATA) : Nat) : Int))) := by
  lia

-- simdjson/fuzz_atpointer: lib/P/Zas.v (replace)
example
    {list_Z T2 : Type}
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
    (hex_digits : T2 → Int → list_Z)
    (l : T2)
    (x : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 475136)
    (h5 : ((489832 ≤ Fp ∧ (Fp + 232) ≤ 694976) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((694984 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : (x / 16) < 1152921504606846976)
    (h12 : 1 ≤ (zlength (hex_digits l x)))
    (h13 : (zlength (hex_digits l x)) = ((zlength (hex_digits l (x / 16))) + 1)) :
    (Int.toNat (j - ((zlength (hex_digits l (x / 16))) + 1))) = (Int.toNat ((j - 1) - (zlength (hex_digits l (x / 16))))) := by
  lia

-- simdjson/fuzz_atpointer: lib/U/Z3r.v (replace)
example
    {aenv T2 T3 : Type}
    (E : aenv)
    (q : Int)
    (ae_lo : aenv → Int)
    (length : T2 → Nat)
    (ae_sbs : aenv → T2)
    (zlength : T3 → Int)
    (ptr : T3)
    (ae_p1 : aenv → T3)
    (P : Int)
    (ae_PTR : aenv → Int)
    (h1 : 0 ≤ (ae_lo E))
    (h2 : (((length (ae_sbs E)) : Nat) : Int) < (2 ^ (56 : Nat)))
    (h3 : (zlength ptr) ≤ (zlength (ae_p1 E)))
    (h4 : (0 ≤ P ∧ (P + (zlength ptr)) = ((ae_PTR E) + (zlength (ae_p1 E)))))
    (h5 : (0 ≤ (zlength ptr) ∧ (zlength ptr) < (2 ^ (64 : Nat)))) :
    (q + (-56)) = ((q + (-72)) + ((16 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_atpointer: lib/U/Z4j.v (replace)
example
    {T1 : Type}
    (length : T1 → Nat)
    (l : T1)
    (to_bytes : T1 → T1)
    (h1 : (length (to_bytes l)) = (length l)) :
    (((length l) : Nat) : Int) = ((((length l) : Nat) : Int) - 0) := by
  lia

-- simdjson/fuzz_atpointer: lib/U/Z5m.v (replace)
example
    {aenv T2 T3 T4 : Type}
    (E : aenv)
    (P : Int)
    (ix : Nat)
    (ae_lo : aenv → Int)
    (ae_sn : aenv → Int)
    (alloc_ceiling : Int)
    (zlength : T2 → Int)
    (ptr : T2)
    (ae_p1 : aenv → T2)
    (ae_PTR : aenv → Int)
    (L0 : Int)
    (length : T3 → Nat)
    (k : T3)
    (L : Int)
    (map : T4 → T3 → T3)
    (Z_to_bv : Nat → T4)
    (rest0 : T3)
    (h1 : 0 ≤ (ae_lo E))
    (h2 : (ae_sn E) < (2 ^ (56 : Nat)))
    (h3 : (zlength ptr) ≤ (zlength (ae_p1 E)))
    (h4 : (0 ≤ P ∧ (P + (zlength ptr)) = ((ae_PTR E) + (zlength (ae_p1 E)))))
    (h5 : (0 ≤ (zlength ptr) ∧ (zlength ptr) < (2 ^ (26 : Nat))))
    (h6 : (((P + 1) + L0) ≤ alloc_ceiling ∧ (ae_PTR E) ≤ (P + 1)))
    (h7 : (((length k) : Nat) : Int) = L)
    (h8 : (((length (map (Z_to_bv 8) k)) : Nat) : Int) = L)
    (h9 : ((P + 1) + L) ≤ (ae_lo E))
    (h10 : (((length (map (Z_to_bv 8) rest0)) : Nat) : Int) = L0)
    (h11 : ((P + 1) + L0) ≤ (ae_lo E)) :
    ((P + 1) + ((ix : Nat) : Int)) = (P + (((ix + 1) : Nat) : Int)) := by
  lia

-- simdjson/fuzz_atpointer: lib/U/Z6d.v (replace)
example
    {T1 T2 : Type}
    (q : Int)
    (ae_lo : T1 → Int)
    (E : T1)
    (ae_sn : T1 → Int)
    (P : Int)
    (L0 : Int)
    (A' : Int)
    (cap : Int)
    (L : Int)
    (length : T2 → Nat)
    (jr : T2)
    (h1 : 0 ≤ (ae_lo E))
    (h2 : (ae_sn E) < (2 ^ (56 : Nat)))
    (h3 : (((P + 1) + L0) ≤ A' ∨ (A' + cap) ≤ (P + 1)))
    (h4 : (length jr) = (Int.toNat ((cap - L) - 1))) :
    (q - 336) = ((q + (-208)) - 128) := by
  lia

-- simdjson/fuzz_dump: lib/A/Dmp_pj_objA.v (replace)
example
    {T1 T2 T3 : Type}
    (ae_DOC : T1 → Int)
    (E : T1)
    (ae_sn : T1 → Int)
    (fs_size : T2 → Int)
    (ae_kD : T1 → T2)
    (bv_unsigned : T3 → Int)
    (Z_to_bv : Int → Int → T3)
    (k : Int)
    (q : Int)
    (h1 : (ae_sn E) < (2 ^ (56 : Nat)))
    (h2 : 0 ≤ (fs_size (ae_kD E)))
    (h3 : (bv_unsigned (Z_to_bv 64 (ae_DOC E))) = (ae_DOC E))
    (h4 : (bv_unsigned (Z_to_bv 64 k)) = k)
    (h5 : (bv_unsigned (Z_to_bv 64 (q - 256))) = (q - 256))
    (h6 : (bv_unsigned (Z_to_bv 64 (((ae_DOC E) / 8) + 2147450880))) = (((ae_DOC E) / 8) + 2147450880))
    (h7 : (bv_unsigned (Z_to_bv 64 ((((ae_DOC E) + 8) / 8) + 2147450880))) = ((((ae_DOC E) + 8) / 8) + 2147450880))
    (h8 : (bv_unsigned (Z_to_bv 64 ((ae_DOC E) + 8))) = ((ae_DOC E) + 8)) :
    ((ae_DOC E) + 8) = ((ae_DOC E) + ((8 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_dump: lib/A/Fe_printf_core_dloop.v (replace)
example
    {list_word : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (j : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_word → Int)
    (x : Int)
    (dec_digits : Int → list_word)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : ((1467432 ≤ Fp ∧ (Fp + 232) ≤ 1475200) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((7072944 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 7081984)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : (VA + (8 * (zlength slots))) ≤ (2 ^ (64 : Nat)))
    (h10 : 0 ≤ BS)
    (h11 : (x / 10) < 1844674407370955162)
    (h12 : 2 ≤ (zlength (dec_digits x))) :
    ((q + (-392)) + (j - 1)) = (((q + (-392)) + j) + (-1)) := by
  lia

-- simdjson/fuzz_dump: lib/A/Fe_printf_core_dloop.v (replace)
example
    {list_word : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (j : Int)
    (zlength : list_word → Int)
    (W' : list_word)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (x : Int)
    (dec_digits : Int → list_word)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : ((1467432 ≤ Fp ∧ (Fp + 232) ≤ 1475200) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((7072944 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 7081984)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : (VA + (8 * (zlength slots))) ≤ (2 ^ (64 : Nat)))
    (h10 : 0 ≤ BS)
    (h11 : (x / 10) < 1844674407370955162)
    (h12 : 2 ≤ (zlength (dec_digits x))) :
    (Int.toNat (j - ((zlength W') + 1))) = (Int.toNat ((j - 1) - (zlength W'))) := by
  lia

-- simdjson/fuzz_dump: lib/A/Fe_printf_core_flags.v (replace)
example
    {list_Z list_word : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (p : Int)
    (k : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_word → Int)
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : ((1467432 ≤ Fp ∧ (Fp + 232) ≤ 1475200) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((7072944 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 7081984)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : (VA + (8 * (zlength slots))) ≤ (2 ^ (64 : Nat)))
    (h10 : 0 ≤ BS)
    (h11 : (32 ≤ (znth fmt (p + k)) ∧ (znth fmt (p + k)) < 64)) :
    ((A + p) + (k + 1)) = (((A + p) + k) + 1) := by
  lia

-- simdjson/fuzz_dump: lib/A/Fe_printf_core_pro.v (replace)
example
    {list_word : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_word → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : ((1467432 ≤ Fp ∧ (Fp + 232) ≤ 1475200) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((7072944 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 7081984)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : (VA + (8 * (zlength slots))) ≤ (2 ^ (64 : Nat)))
    (h10 : 0 ≤ BS) :
    (q + (-368)) = (((q + (-544)) + ((152 : Nat) : Int)) + ((24 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_dump: lib/A/Fe_printf_core_xloop.v (replace)
example
    {list_word T2 : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (j : Int)
    (zlength : list_word → Int)
    (hex_digits : T2 → Int → list_word)
    (l : T2)
    (x : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : ((1467432 ≤ Fp ∧ (Fp + 232) ≤ 1475200) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((7072944 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 7081984)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : (VA + (8 * (zlength slots))) ≤ (2 ^ (64 : Nat)))
    (h10 : 0 ≤ BS)
    (h11 : (x / 16) < 1152921504606846976)
    (h12 : 1 ≤ (zlength (hex_digits l x)))
    (h13 : (zlength (hex_digits l x)) = ((zlength (hex_digits l (x / 16))) + 1)) :
    (Int.toNat (j - ((zlength (hex_digits l (x / 16))) + 1))) = (Int.toNat ((j - 1) - (zlength (hex_digits l (x / 16))))) := by
  lia

-- simdjson/fuzz_dump: lib/A/R_popfree.v (replace)
example
    {T1 T2 : Type}
    (rb : T1 → T2 → Int)
    (SB : T1)
    (c : T2)
    (muser : Int)
    (k : Int)
    (ClassSize : T2 → Int)
    (h1 : (k * (ClassSize c)) ≤ (2 ^ (22 : Nat))) :
    ((rb SB c) + muser) = (muser + (rb SB c)) := by
  lia

-- simdjson/fuzz_dump: lib/A/R_return_T.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (amo_aligned : T2 → T3 → Bool)
    (AD : T2)
    (Z_to_bv : Nat → T4 → T3)
    (R : T4)
    (h1 : (amo_aligned AD (Z_to_bv 64 R)) = true) :
    (bv_unsigned sp) = (((bv_unsigned sp) - 128) + 128) := by
  lia

-- simdjson/fuzz_dump: lib/A/Sj_stage2_entry.v (replace)
example {s2env : Type} (E : s2env) (e_OC : s2env → Int) :
    ((e_OC E) + 4) = ((e_OC E) + (4 * 1)) := by
  lia

-- simdjson/fuzz_dump: lib/A/Sj_stage2_strv2.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (e_BUF : T1 → Int)
    (E' : T1)
    (e_off : T1 → Int → Int)
    (k : T2 → Int)
    (s : T2)
    (e_n : T3 → Int)
    (E : T3)
    (length : T4 → Nat)
    (e_sbs : T1 → T4)
    (sb : T2 → Int)
    (j : Int)
    (e_scap : T1 → Int)
    (h1 : (k s) < (e_n E))
    (h2 : (((length (e_sbs E')) : Nat) : Int) = (sb s))
    (h3 : (0 ≤ (sb s) ∧ (((sb s) + (j - (e_off E' (k s)))) + 4) ≤ (e_scap E'))) :
    (((e_BUF E') + (e_off E' (k s))) + 1) = ((e_BUF E') + ((e_off E' (k s)) + 1)) := by
  lia

-- simdjson/fuzz_dump: lib/AS/AsanHeapSort.v (replace)
example (v : Int) (h1 : (0 ≤ v ∧ v < (2 ^ (32 : Nat)))) :
    ((v - (2 ^ (32 : Nat))) + (1 * (2 ^ (64 : Nat)))) = (v + ((2 ^ (64 : Nat)) - (2 ^ (32 : Nat)))) := by
  lia

-- simdjson/fuzz_dump: lib/Sj/SjTape.v (replace)
example
    (t : Int)
    (nxt : Int)
    (cv : Int)
    (CNT_MAX : Int)
    (h1 : (0 ≤ nxt ∧ nxt < (2 ^ (32 : Nat))))
    (h2 : (0 ≤ cv ∧ cv ≤ CNT_MAX)) :
    (nxt + (((t * (2 ^ (24 : Nat))) + cv) * (2 ^ (32 : Nat)))) = ((t * (2 ^ (56 : Nat))) + (nxt + (cv * (2 ^ (32 : Nat))))) := by
  lia

-- simdjson/fuzz_dump: lib/U/F_fmt_fp_pre4.v (replace)
example
    {list_byte : Type}
    (bf : list_byte)
    (s : Int)
    (n : Nat)
    (length : list_byte → Nat)
    (h1 : 9 ≤ (length bf))
    (h2 : (0 ≤ s ∧ s ≤ 9)) :
    (Int.toNat (s + ((n : Nat) : Int))) = ((Int.toNat s) + n) := by
  lia

-- simdjson/fuzz_dump: lib/U/F_fmt_fp_pre4.v (replace)
example
    {list_byte : Type}
    (bf : list_byte)
    (s : Int)
    (n : Int)
    (k : Nat)
    (length : list_byte → Nat)
    (h1 : 9 ≤ (length bf))
    (h2 : 0 ≤ s)
    (h3 : 0 ≤ n)
    (h4 : (s + n) ≤ 9) :
    (Int.toNat (s + ((k : Nat) : Int))) = ((Int.toNat s) + k) := by
  lia

-- simdjson/fuzz_dump: lib/U/Sj_num_wrap.v (replace)
example
    {nwenv : Type}
    (E : nwenv)
    (cur : Int)
    (w_A : nwenv → Int)
    (w_stop : nwenv → Int)
    (w_TL : nwenv → Int)
    (h1 : (w_stop E) < (w_TL E)) :
    (cur + 1) = ((((w_A E) + cur) + 1) - (w_A E)) := by
  lia

-- simdjson/fuzz_dump: lib/U/Sj_stage2_numkit.v (replace)
example (b3 : Int) (b4 : Int) (h1 : (0 ≤ b3 ∧ b3 < 256)) (h2 : (0 ≤ b4 ∧ b4 < 256)) :
    (((b4 * 256) + b3) * (2 ^ (16 : Nat))) = ((b4 * (2 ^ (24 : Nat))) + (b3 * (2 ^ (16 : Nat)))) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/A/Drt_lftoi1A.v (replace)
example
    {T1 : Type}
    (usp : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (h1 : (bv_unsigned (Z_to_bv 64 usp)) = usp) :
    (usp - 88) = (((usp + (-144)) + ((40 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/A/Drt_topA.v (replace)
example
    {T1 : Type}
    (f : Int)
    (Z_to_bv : Int → Int → T1)
    (d : Int)
    (bv_unsigned : T1 → Int)
    (sp' : Int)
    (shad : Int → Int)
    (SHB : Int)
    (h1 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h2 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h3 : (shad (f + 512)) = ((shad f) + 64))
    (h4 : (shad f) = ((f / 8) + SHB))
    (h5 : 0 ≤ (shad f)) :
    (f + 56) = ((f + 32) + 24) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/A/El_os_pad4A.v (replace)
example
    {T1 : Type}
    (sp : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (E1 : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 (sp - 64))) = (sp - 64))
    (h2 : (bv_unsigned (Z_to_bv 64 E1)) = E1) :
    sp = ((sp + (-64)) + ((64 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/A/El_setfillA.v (replace)
example
    {T1 : Type}
    (OS : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (f : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 f)) = f)
    (h2 : (bv_unsigned (Z_to_bv 64 ((f / 8) + 2147450880))) = ((f / 8) + 2147450880)) :
    (OS + 136) = ((OS + 128) + 8) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/A/F_fmt_fp_r3.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (B : Int)
    (junk0 : list_byte)
    (t : Int)
    (bv_unsigned : word → Int)
    (d : Int)
    (Fp : Int)
    (Z_lor : Int → Nat → Int)
    (length : list_byte → Nat)
    (h1 : 5152 ≤ (bv_unsigned sp))
    (h2 : (bv_unsigned sp) < (2 ^ (63 : Nat)))
    (h3 : 7078064 ≤ ((bv_unsigned sp) - 6944))
    (h4 : (bv_unsigned sp) ≤ Fp)
    (h5 : (bv_unsigned sp) ≤ B)
    (h6 : (0 ≤ t ∧ t < 256))
    (h7 : (Z_lor t 32) ≠ 97)
    (h8 : (length junk0) < 256)
    (h9 : (0 ≤ Fp ∧ Fp < (2 ^ (64 : Nat)))) :
    (((bv_unsigned sp) + (-1056)) + (4 * ((d - 1) - 1))) = ((((bv_unsigned sp) + (-1056)) + (4 * (d - 1))) + (-4)) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/A/Fe_printf_core_scan.v (replace)
example
    {list_word : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (i : Int)
    (j : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_word → Int)
    (n : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : ((1471272 ≤ Fp ∧ (Fp + 232) ≤ 1480320) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((7078064 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 7086080)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : (VA + (8 * (zlength slots))) ≤ (2 ^ (64 : Nat)))
    (h10 : 0 ≤ BS)
    (h11 : j = n) :
    ((A + i) + (j + 1)) = (((A + i) + j) + 1) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/A/Sj_stage2_pro.v (replace)
example
    {T1 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (h1 : (((bv_unsigned sp) % 32) = 0 ∨ ((bv_unsigned sp) % 32) = 16)) :
    (((bv_unsigned sp) + (-120)) + ((16 : Nat) : Int)) = ((bv_unsigned sp) + (-104)) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/Lib/Decode.v (replace)
example
    {T1 T2 : Type}
    (req : Int)
    (r : T1)
    (vm_brk : T2 → T1)
    (h_1 : T2)
    (page_round_up_Z : Int → Int)
    (bv_unsigned : T1 → Int)
    (alloc_ceiling : Int)
    (h1 : (page_round_up_Z (bv_unsigned (vm_brk h_1))) ≤ (page_round_up_Z (bv_unsigned r)))
    (h2 : req ≤ alloc_ceiling)
    (h3 : (page_round_up_Z req) = req) :
    (((req / 4096) * 4096) + 4095) = (((4096 * (req / 4096)) + 4096) - 1) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/P/Sj_num_kit.v (replace)
example {T1 : Type} (length : T1 → Nat) (w1 : T1) (k : Nat) (w3 : T1) :
    ((8 * (((length w1) : Nat) : Int)) + ((8 * ((k : Nat) : Int)) + (8 * (((length w3) : Nat) : Int)))) = (8 * ((((length w1) + (k + (length w3))) : Nat) : Int)) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/P/Sj_num_kit.v (replace)
example {T1 : Type} (length : T1 → Nat) (b1 : T1) (k : Nat) (b3 : T1) :
    ((((length b1) : Nat) : Int) + (((k : Nat) : Int) + (((length b3) : Nat) : Int))) = ((((length b1) + (k + (length b3))) : Nat) : Int) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/Spec/SoftFloatProps2.v (assert)
example
    (hh : Int)
    (hl : Int)
    (lh : Int)
    (ll : Int)
    (M : Int)
    (h1 : (0 ≤ hh ∧ hh < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ hl ∧ hl < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ lh ∧ lh < (2 ^ (64 : Nat))))
    (h4 : (0 ≤ ll ∧ ll < (2 ^ (64 : Nat))))
    (h5 : 0 ≤ M)
    (h6 : ((((hh * (2 ^ (192 : Nat))) + (hl * (2 ^ (128 : Nat)))) + (lh * (2 ^ (64 : Nat)))) + ll) = (M * (2 ^ (128 : Nat)))) :
    ll = 0 := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/Spec/SoftFloatProps2.v (assert)
example
    (hh : Int)
    (hl : Int)
    (lh : Int)
    (ll : Int)
    (M : Int)
    (h1 : (0 ≤ hh ∧ hh < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ hl ∧ hl < (2 ^ (64 : Nat))))
    (h3 : (0 ≤ lh ∧ lh < (2 ^ (64 : Nat))))
    (h4 : (0 ≤ ll ∧ ll < (2 ^ (64 : Nat))))
    (h5 : 0 ≤ M)
    (h6 : ((((hh * (2 ^ (192 : Nat))) + (hl * (2 ^ (128 : Nat)))) + (lh * (2 ^ (64 : Nat)))) + ll) = (M * (2 ^ (128 : Nat))))
    (h7 : ll = 0) :
    lh = 0 := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/Spec/SoftFloatProps2.v (assert)
example (sa : Int) (h1 : (0 ≤ sa ∧ sa ≤ 1)) :
    (sa = 0 ∨ sa = 1) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/U/El_dump_kit.v (replace)
example {T1 : Type} (dsp : T1 → Int) (D : T1) :
    ((dsp D) + ((72 : Nat) : Int)) = ((dsp D) + 72) := by
  lia

-- simdjson/fuzz_dump_raw_tape: lib/U/Sj_num_memmoveN.v (replace)
example
    {list_byte : Type}
    (bs : list_byte)
    (j : Nat)
    (n : Nat)
    (k : Int)
    (length : list_byte → Nat)
    (h1 : 0 ≤ k)
    (h2 : (k + 8) ≤ ((n : Nat) : Int))
    (h3 : (j + n) ≤ (length bs)) :
    (j + (Int.toNat k)) = (Int.toNat (((j : Nat) : Int) + k)) := by
  lia

-- simdjson/fuzz_element: lib/B/Atp_objpA.v (replace)
example (q : Int) :
    (q + (-272)) = ((q + (-256)) - 16) := by
  lia

-- simdjson/fuzz_element: lib/B/El_arm1wA.v (replace)
example
    {T1 T2 : Type}
    (ae_TAPE : T1 → Int)
    (E : T1)
    (ae_sn : T1 → Int)
    (ttype : T2 → Int)
    (ae_T : T1 → Int → T2)
    (h1 : (ae_sn E) < (2 ^ (56 : Nat)))
    (h2 : (0 ≤ (ttype (ae_T E 1)) ∧ (ttype (ae_T E 1)) < 256)) :
    (((ae_TAPE E) + (8 * 1)) + 7) = (((ae_TAPE E) + (8 * 1)) + 7) := by
  lia

-- simdjson/fuzz_element: lib/B/El_arm20A.v (replace)
example
    {T1 : Type}
    (sp' : Int)
    (bv_unsigned : T1 → Int)
    (wz : Int → T1)
    (f : Int)
    (h1 : (bv_unsigned (wz sp')) = sp')
    (h2 : (f + 1024) ≤ (sp' - 176)) :
    (sp' + (-72)) = ((sp' + (-80)) + ((8 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_element: lib/B/El_dispA.v (replace)
example
    {T1 : Type}
    (sp' : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (usp : Int)
    (x : Int)
    (shad : Int → Int)
    (f : Int)
    (SHB : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h2 : ((7172416 ≤ x ∧ x < 7172424) ∨ usp ≤ x))
    (h3 : (shad f) = ((f / 8) + SHB)) :
    (sp' + 128) = ((sp' + 104) + ((24 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_element: lib/B/El_lf2bA.v (replace)
example
    {list_byte T2 T3 : Type}
    (usp : Int)
    (sp' : Int)
    (d : Int)
    (n : Int)
    (bs : list_byte)
    (length : list_byte → Nat)
    (SEGTOP_A : Int)
    (shad : Int → Int)
    (bv_unsigned : T2 → Int)
    (nth : Nat → list_byte → T3 → T2)
    (z8 : T3)
    (Z_to_bv : Int → Int → T2)
    (h1 : n = (((length bs) : Nat) : Int))
    (h2 : 0 ≤ d)
    (h3 : (d + n) < (2 ^ (63 : Nat)))
    (h4 : SEGTOP_A ≤ sp')
    (h5 : (sp' + 152) ≤ (usp - 104))
    (h6 : usp < (2 ^ (63 : Nat)))
    (h7 : ((d + n) ≤ sp' ∨ usp ≤ d))
    (h8 : (shad (d + n)) < sp')
    (h9 : (0 ≤ (bv_unsigned (nth 1 bs z8)) ∧ (bv_unsigned (nth 1 bs z8)) < 256))
    (h10 : (bv_unsigned (Z_to_bv 64 (d + 1))) = (d + 1)) :
    (d + 2) = ((d + 1) + 1) := by
  lia

-- simdjson/fuzz_element: lib/B/El_setfillA.v (replace)
example
    {T1 : Type}
    (f : Int)
    (bv_unsigned : T1 → Int)
    (wz : Int → T1)
    (q : Int)
    (shad : Int → Int)
    (lo : Int)
    (OS : Int)
    (CP : Int)
    (h1 : (bv_unsigned (wz q)) = q)
    (h2 : (bv_unsigned (wz (q - 160))) = (q - 160))
    (h3 : (shad (f + 64)) = ((shad f) + 8))
    (h4 : 0 ≤ (f / 8))
    (h5 : 897536 ≤ (f / 8))
    (h6 : 140735332483072 ≤ lo)
    (h7 : (((OS / 8) + 2147450880) + 37) ≤ lo)
    (h8 : ((OS + 288) ≤ f ∨ (f + 64) ≤ OS))
    (h9 : ((f + 64) ≤ ((OS / 8) + 2147450880) ∨ (((OS + 288) / 8) + 2147450880) ≤ f))
    (h10 : ((OS + 288) ≤ ((f / 8) + 2147450880) ∨ (((f / 8) + 2147450880) + 8) ≤ OS))
    (h11 : ((OS + 288) ≤ ((OS / 8) + 2147450880) ∨ (((OS / 8) + 2147450880) + 37) ≤ OS))
    (h12 : ((OS + 288) ≤ 2147446784 ∨ 17594333495296 ≤ OS))
    (h13 : ((CP + 1) ≤ f ∨ (f + 64) ≤ CP))
    (h14 : ((CP + 1) ≤ OS ∨ (OS + 288) ≤ CP))
    (h15 : ((CP + 1) ≤ ((f / 8) + 2147450880) ∨ (((f / 8) + 2147450880) + 8) ≤ CP)) :
    (f + 56) = ((f + 64) - 8) := by
  lia

-- simdjson/fuzz_element: lib/B/F_fmt_fp_dn.v (replace)
example
    {word list_byte T3 T4 T5 : Type}
    (sp : word)
    (B : Int)
    (junk0 : list_byte)
    (t : Int)
    (z1 : Int)
    (b : Int)
    (bv_unsigned : word → Int)
    (Fp : Int)
    (Z_lor : Int → Nat → Int)
    (length : list_byte → Nat)
    (need : Int)
    (sh : Int)
    (a : Int)
    (dn_a1 : T3 → Int → Int)
    (bigI : T3)
    (z : Int)
    (snd : T4 → Int)
    (dn_bz : T3 → Int → T5 → T4)
    (cI : T5)
    (fst : T4 → list_byte)
    (zf : Int)
    (e2 : Int)
    (a1 : Int)
    (h1 : 5152 ≤ (bv_unsigned sp))
    (h2 : (bv_unsigned sp) < (2 ^ (63 : Nat)))
    (h3 : 7171824 ≤ ((bv_unsigned sp) - 6944))
    (h4 : (bv_unsigned sp) ≤ Fp)
    (h5 : (bv_unsigned sp) ≤ B)
    (h6 : (0 ≤ t ∧ t < 256))
    (h7 : (Z_lor t 32) ≠ 97)
    (h8 : (length junk0) < 256)
    (h9 : (0 ≤ Fp ∧ Fp < (2 ^ (64 : Nat))))
    (h10 : (1 ≤ need ∧ need < (2 ^ (31 : Nat))))
    (h11 : (1 ≤ sh ∧ sh ≤ 9))
    (h12 : ((a ≤ (dn_a1 bigI a) ∧ (dn_a1 bigI a) ≤ z) ∧ (dn_a1 bigI a) ≤ (a + 1)))
    (h13 : (z ≤ (snd (dn_bz bigI z cI)) ∧ (snd (dn_bz bigI z cI)) ≤ (z + 1)))
    (h14 : (length (fst (dn_bz bigI z cI))) = 128)
    (h15 : (0 ≤ zf ∧ zf ≤ z1))
    (h16 : (e2 + sh) = 0)
    (h17 : (e2 + sh) < 0)
    (h18 : (0 ≤ b ∧ b ≤ a1)) :
    ((z1 - b) * (2 ^ (2 : Nat))) = ((((bv_unsigned sp) + (-1056)) + (4 * z1)) - (((bv_unsigned sp) + (-1056)) + (4 * b))) := by
  lia

-- simdjson/fuzz_element: lib/B/F_printf_core_scan.v (replace)
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
    (j : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (n : Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 1515520)
    (h5 : ((1561464 ≤ Fp ∧ (Fp + 232) ≤ 1571136) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((7171824 ≤ B ∧ ((B + BS) ≤ lo ∧ (B + BS) ≤ 7180288)) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : j = n) :
    ((A + i) + (j + 1)) = (((A + i) + j) + 1) := by
  lia

-- simdjson/fuzz_element: lib/B/I_frexpl.v (replace)
example
    {T1 : Type}
    (p : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (h1 : (bv_unsigned (Z_to_bv 64 p)) = p) :
    (p + 3) = ((p + 4) - 1) := by
  lia

-- simdjson/fuzz_element: lib/B/RT_dsec_nw.v (replace)
example {T1 : Type} (l_ACEIL : T1 → Int) (L : T1) :
    (max 0 (((2 ^ (47 : Nat)) - (l_ACEIL L)) / 8)) = (((Int.toNat (((2 ^ (47 : Nat)) - (l_ACEIL L)) / 8)) : Nat) : Int) := by
  lia

-- simdjson/fuzz_element: lib/B/Sj_num_fc_dc.v (replace)
example
    {T1 T2 T3 : Type}
    (q_spq : T1 → Int)
    (E : T1)
    (q_lo : T1 → Int)
    (length : T2 → Nat)
    (bs0 : T2)
    (SUB : T2)
    (q_LAST : T1 → Int)
    (q_FIRST : T1 → Int)
    (bv_unsigned : T3 → Int)
    (Z_to_bv : Nat → Int → T3)
    (q_f : T1 → Int)
    (h1 : 0 ≤ (q_lo E))
    (h2 : (length bs0) = 496)
    (h3 : (((length SUB) : Nat) : Int) = ((q_LAST E) - (q_FIRST E)))
    (h4 : (bv_unsigned (Z_to_bv 64 (q_spq E))) = (q_spq E))
    (h5 : ((((q_f E) + 32) / 8) + 2147450880) = (((q_f E) / 8) + 2147450884)) :
    (((q_spq E) + 72) + 32) = (((q_spq E) + 72) + ((32 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_element: lib/B/Sj_num_fc_pro.v (replace)
example
    {fcbenv : Type}
    (E : fcbenv)
    (q_SP : fcbenv → Int)
    (q_lo : fcbenv → Int)
    (SPB_STACK : Int)
    (USTACK_TOP : Int)
    (q_spq : fcbenv → Int)
    (FCB_GTOP : Int)
    (h1 : ((q_lo E) + SPB_STACK) ≤ (q_SP E))
    (h2 : ((q_SP E) + 16) ≤ USTACK_TOP)
    (h3 : ((((q_SP E) - 272) ≤ (q_spq E) ∧ (q_spq E) ≤ ((q_SP E) - 256)) ∧ ((q_spq E) % 32) = 0))
    (h4 : FCB_GTOP ≤ (q_lo E))
    (h5 : ((q_SP E) % 16) = 0)
    (h6 : (q_spq E) = ((q_SP E) + (-272))) :
    ((q_SP E) + (-272)) = (((q_SP E) + (-256)) - 16) := by
  lia

-- simdjson/fuzz_element: lib/B/Sj_num_lm_pro.v (replace)
example
    {word : Type}
    (sp : word)
    (lo : Int)
    (bv_unsigned : word → Int)
    (LMB_STACK : Int)
    (USTACK_TOP : Int)
    (h1 : (lo + LMB_STACK) ≤ (bv_unsigned sp))
    (h2 : ((bv_unsigned sp) + 16) ≤ USTACK_TOP)
    (h3 : ((bv_unsigned sp) % 16) = 0)
    (h4 : 7180288 ≤ lo) :
    ((bv_unsigned sp) + (-224)) = (((bv_unsigned sp) + (-240)) + 16) := by
  lia

-- simdjson/fuzz_element: lib/B/Sj_stage2_defs.v (replace)
example (a : Int) (w : Int) :
    (w * (2 ^ (3 : Nat))) = ((a + (8 * w)) - a) := by
  lia

-- simdjson/fuzz_element: lib/B/Sj_stage2_tapek.v (replace)
example (A : Int) (Wv : Int) (h1 : (0 ≤ (Wv + 1) ∧ (Wv + 1) < (2 ^ (32 : Nat)))) :
    ((Wv + 1) * (2 ^ (3 : Nat))) = (((A + (8 * Wv)) + 8) - A) := by
  lia

-- simdjson/fuzz_element: lib/P/El_h2.v (replace)
example
    {T1 : Type}
    (len1 : Int)
    (zlength : T1 → Int)
    (d : T1)
    (length : T1 → Nat)
    (to_bytes : T1 → T1)
    (el_str : T1 → T1)
    (alloc_ceiling : Int)
    (doc_cap : T1 → Int)
    (a : Int)
    (h1 : (zlength d) = (((length d) : Nat) : Int))
    (h2 : (length (to_bytes d)) = (length d))
    (h3 : (0 ≤ len1 ∧ len1 ≤ (zlength d)))
    (h4 : (0 ≤ (zlength (el_str d)) ∧ (zlength (el_str d)) ≤ (zlength d)))
    (h5 : (doc_cap d) = 32)
    (h6 : a < alloc_ceiling) :
    ((Int.toNat len1) + 64) = (Int.toNat (len1 + 64)) := by
  lia

-- simdjson/fuzz_element: lib/P/El_xalloc.v (replace)
example
    {T1 T2 T3 T4 T5 T6 T7 T8 : Type}
    (snd : T1 → Int)
    (c : T1)
    (stride : Int)
    (IB : Int)
    (st : T2)
    (bm : T1)
    (i : Int)
    (P : Int)
    (B : Int)
    (off : Int)
    (m_last_idx : T3 → Int)
    (mr : T3)
    (res : Int)
    (E : Int)
    (r_base : T4 → Int)
    (r : T4)
    (round_up_pg : T5 → Int)
    (r_len : T4 → T5)
    (n : Int)
    (c_init_done : T6 → Int)
    (ctx : T2 → T6)
    (G : Int)
    (rg : T4)
    (a : T1)
    (AREA_HDR : Int)
    (META_SIZE : Int)
    (ka : Int)
    (A : Int)
    (Z_land : T7 → Int → Int)
    (b3 : T7)
    (size_class : T8 → Int)
    (m_sizeclass : T3 → T8)
    (m_maplen : T3 → Int)
    (j : Nat)
    (h1 : (stride * (i + 1)) = ((stride * i) + stride))
    (h2 : (snd c) = (((snd bm) + 16) + (stride * i)))
    (h3 : P = (((B + 16) + (stride * i)) + (16 * off)))
    (h4 : ((stride * i) + stride) ≤ (stride * ((m_last_idx mr) + 1)))
    (h5 : 0 ≤ (stride * i))
    (h6 : res < (2 ^ (31 : Nat)))
    (h7 : 0 ≤ res)
    (h8 : (E + 1) ≤ ((r_base r) + (round_up_pg (r_len r))))
    (h9 : res = (((stride - 4) - (16 * off)) - n))
    (h10 : (16 ≤ (snd c) ∧ ((((snd c) + stride) - 4) + 1) ≤ (round_up_pg (r_len r))))
    (h11 : (c_init_done (ctx st)) ≠ 0)
    (h12 : G = (((r_base rg) + (snd a)) + (AREA_HDR + (META_SIZE * ka))))
    (h13 : ((((r_base rg) + (snd a)) + (AREA_HDR + (META_SIZE * ka))) % 4096) = (AREA_HDR + (META_SIZE * ka)))
    (h14 : A = (G - (G % 4096)))
    (h15 : (Z_land b3 31) = i)
    (h16 : (stride = (16 * (size_class (m_sizeclass mr))) ∨ (m_last_idx mr) = 0))
    (h17 : (stride ≤ (16 * (size_class (m_sizeclass mr))) ∨ 292 ≤ (size_class (m_sizeclass mr))))
    (h18 : (((m_maplen mr) * 4096) / 16) = ((m_maplen mr) * 256))
    (h19 : (0 ≤ (((((snd c) + stride) - IB) - 4) + ((j : Nat) : Int)) ∧ (((((snd c) + stride) - IB) - 4) + ((j : Nat) : Int)) < (round_up_pg (r_len r)))) :
    ((((snd c) + stride) - IB) - 3) = (((((snd c) + stride) - IB) - 4) + 1) := by
  lia

-- simdjson/fuzz_element: lib/P/El_xs_kitP.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (a0 : T1) (i : Nat) :
    ((bv_unsigned a0) + (8 * ((i : Nat) : Int))) = ((bv_unsigned a0) + (((8 * i) : Nat) : Int)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/I_ammovew.v (replace)
example
    {T1 : Type}
    (sp : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (d : Int)
    (s : Int)
    (n : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 sp)) = sp)
    (h2 : (bv_unsigned (Z_to_bv 64 d)) = d)
    (h3 : (bv_unsigned (Z_to_bv 64 s)) = s)
    (h4 : (bv_unsigned (Z_to_bv 64 n)) = n)
    (h5 : (bv_unsigned (Z_to_bv 64 (18446744073709551615 - s))) = (18446744073709551615 - s)) :
    (sp + (-2136)) = ((sp + (-2048)) + (-88)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_lftoi3A.v (replace)
example (f : Int) (k : Int) (h1 : (0 < k ∨ k = 0)) :
    (((f + 160) + (136 * (k - 1))) + 8) = (((f + 160) + (136 * k)) + (-128)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_okarmA.v (replace)
example (A : Int) :
    (((((((A + ((4 : Nat) : Int)) + ((11 : Nat) : Int)) + ((5 : Nat) : Int)) + ((68 : Nat) : Int)) + ((16 : Nat) : Int)) + ((33 : Nat) : Int)) + ((9 : Nat) : Int)) = (A + 146) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_sb_overflowA.v (replace)
example
    {T1 T2 : Type}
    (cap : Int)
    (lim : Int)
    (q : Int)
    (bv_unsigned : T1 → Int)
    (wz : Int → T1)
    (oa_heap : T2 → Bool)
    (st : T2)
    (D : Int)
    (lo : Int)
    (NEW : Int)
    (h1 : 0 ≤ (q - 96))
    (h2 : (bv_unsigned (wz q)) = q)
    (h3 : (bv_unsigned (wz (q + (-80)))) = (q + (-80)))
    (h4 : (22 ≤ lim ∧ lim < cap))
    (h5 : ((oa_heap st) = true → (cap % 16) = 0))
    (h6 : (0 < D ∧ (D + cap) ≤ lo))
    (h7 : (NEW + (2 * cap)) < (2 ^ (47 : Nat))) :
    ((2 * cap) - 1) = ((lim + 1) + (((2 * cap) - lim) - 2)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_segA2.v (replace)
example
    {T1 : Type}
    (f : T1)
    (i : Int)
    (k : Nat)
    (shad : T1 → Int)
    (h1 : 20 ≤ i)
    (h2 : (i + ((k : Nat) : Int)) ≤ 88)
    (h3 : 0 ≤ (shad f)) :
    ((shad f) + i) = (((shad f) + 20) + (((Int.toNat (i - 20)) : Nat) : Int)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_segA2.v (replace)
example
    {T1 : Type}
    (f : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp' : Int)
    (shad : Int → Int)
    (SHB : Int)
    (n : Int)
    (d : Int)
    (a : T1)
    (USTACK_TOP : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h2 : (shad f) = ((f / 8) + SHB))
    (h3 : (shad (f + 2048)) = ((shad f) + 256))
    (h4 : (0 ≤ n ∧ n < (2 ^ (26 : Nat))))
    (h5 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h6 : (¬ ((sp' - 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < USTACK_TOP))) :
    (f + 168) = ((f + 160) + ((8 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_segA2.v (replace)
example
    {T1 : Type}
    (sp' : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (shad : Int → Int)
    (f : Int)
    (SHB : Int)
    (n : Int)
    (d : Int)
    (a : T1)
    (USTACK_TOP : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h2 : (shad f) = ((f / 8) + SHB))
    (h3 : (shad (f + 2048)) = ((shad f) + 256))
    (h4 : (0 ≤ n ∧ n < (2 ^ (26 : Nat))))
    (h5 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h6 : (¬ ((sp' - 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < USTACK_TOP))) :
    (sp' + 192) = (sp' + ((192 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_segA2.v (replace)
example
    {T1 : Type}
    (f : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp' : Int)
    (shad : Int → Int)
    (SHB : Int)
    (n : Int)
    (d : Int)
    (a : T1)
    (USTACK_TOP : Int)
    (imp_okarm_costA : Int → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h2 : (shad f) = ((f / 8) + SHB))
    (h3 : (shad (f + 2048)) = ((shad f) + 256))
    (h4 : (0 ≤ n ∧ n < (2 ^ (26 : Nat))))
    (h5 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h6 : (¬ ((sp' - 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < USTACK_TOP)))
    (h7 : 0 ≤ (imp_okarm_costA ((max n 32) + 67))) :
    (f + 272) = ((f + 248) + ((24 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_segA2.v (replace)
example
    {T1 T2 : Type}
    (f : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp' : Int)
    (shad : Int → Int)
    (SHB : Int)
    (n : Int)
    (d : Int)
    (a : T1)
    (USTACK_TOP : Int)
    (imp_okarm_costA : Int → Int)
    (bv_eqb : T2 → T1 → Bool)
    (r : T2)
    (h1 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h2 : (shad f) = ((f / 8) + SHB))
    (h3 : (shad (f + 2048)) = ((shad f) + 256))
    (h4 : (0 ≤ n ∧ n < (2 ^ (26 : Nat))))
    (h5 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h6 : (¬ ((sp' - 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < USTACK_TOP)))
    (h7 : 0 ≤ (imp_okarm_costA ((max n 32) + 67)))
    (h8 : (bv_eqb r (Z_to_bv 64 0)) = false) :
    (f + 264) = ((f + 248) + ((16 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_segA2.v (replace)
example
    {T1 : Type}
    (sp' : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (shad : Int → Int)
    (f : Int)
    (SHB : Int)
    (n : Int)
    (d : Int)
    (a : T1)
    (USTACK_TOP : Int)
    (imp_okarm_costA : Int → Int)
    (bv_eqb : T1 → T1 → Bool)
    (r : T1)
    (h1 : (bv_unsigned (Z_to_bv 64 sp')) = sp')
    (h2 : (shad f) = ((f / 8) + SHB))
    (h3 : (shad (f + 2048)) = ((shad f) + 256))
    (h4 : (0 ≤ n ∧ n < (2 ^ (26 : Nat))))
    (h5 : (0 ≤ d ∧ d < (2 ^ (64 : Nat))))
    (h6 : (¬ ((sp' - 32) ≤ (bv_unsigned a) ∧ (bv_unsigned a) < USTACK_TOP)))
    (h7 : 0 ≤ (imp_okarm_costA ((max n 32) + 67)))
    (h8 : (bv_eqb r (Z_to_bv 64 0)) = false)
    (h9 : (¬ (sp' ≤ (bv_unsigned a) ∧ (bv_unsigned a) < USTACK_TOP)))
    (h10 : (¬ (f ≤ (bv_unsigned a) ∧ (bv_unsigned a) < (f + 2040)))) :
    (sp' + 80) = (sp' + ((80 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_segA3.v (replace)
example (f : Int) :
    (f + 168) = (((f + 160) + (136 * 0)) + 8) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_segA3a.v (replace)
example (f : Int) :
    (((f + 160) + (136 * 3)) + 8) = (f + 576) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Imp_syncA.v (replace)
example {T1 : Type} (bv_unsigned : T1 → Int) (sp : T1) :
    ((bv_unsigned sp) + (-56)) = (((((bv_unsigned sp) + (-80)) + 8) + 8) + 8) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Pj_ser_intkA.v (replace)
example
    (g : Nat)
    (i : Int)
    (shad : Int → Int)
    (f : Int)
    (h1 : ((i / 8) = 0 ∨ ((i / 8) = 1 ∨ ((i / 8) = 2 ∧ (i % 8) < 4))))
    (h2 : (shad ((f + (8 * ((g : Nat) : Int))) + i)) = (((f / 8) + 2147450880) + (((g : Nat) : Int) + (i / 8)))) :
    (((g + 1) : Nat) : Int) = (((g : Nat) : Int) + 1) := by
  lia

-- simdjson/fuzz_implementations: lib/A/Pj_ser_objA.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (D : T1)
    (f : Int)
    (pa_lo : T2 → Int)
    (E : T2)
    (ser_needA : T1 → Int)
    (b : Int)
    (bv_unsigned : T3 → Int)
    (wz : Int → T3)
    (pa_F : T2 → Int)
    (fs_size : T4 → Int)
    (pa_kF : T2 → T4)
    (h1 : ((pa_lo E) + (ser_needA D)) ≤ b)
    (h2 : ((pa_lo E) + 65936) ≤ b)
    (h3 : (bv_unsigned (wz b)) = b)
    (h4 : (f + 128) ≤ (pa_lo E))
    (h5 : (8 * (f / 8)) = f)
    (h6 : (8 * ((pa_F E) / 8)) = (pa_F E))
    (h7 : ((f + 128) / 8) = ((f / 8) + 16))
    (h8 : (((pa_F E) + (fs_size (pa_kF E))) / 8) = (((pa_F E) / 8) + ((fs_size (pa_kF E)) / 8)))
    (h9 : (((f / 8) + 2147450880) + 16) ≤ (pa_lo E)) :
    (f + 120) = ((f + 24) + 96) := by
  lia

-- simdjson/fuzz_implementations: lib/A/R_depot_defs.v (replace)
example {T1 : Type} (l : T1) (length : T1 → Nat) :
    (length l) = (Int.toNat (((((length l) : Nat) : Int) + 1) - 1)) := by
  lia

-- simdjson/fuzz_implementations: lib/P/F_printf_core_dloop.v (replace)
example
    {list_word : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (j : Int)
    (zlength : list_word → Int)
    (W' : list_word)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (x : Int)
    (dec_digits : Int → list_word)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : ((878264 ≤ Fp ∧ (Fp + 232) ≤ 1089544) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((1089552 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : (VA + (8 * (zlength slots))) ≤ (2 ^ (64 : Nat)))
    (h10 : 0 ≤ BS)
    (h11 : (x / 10) < 1844674407370955162)
    (h12 : 2 ≤ (zlength (dec_digits x))) :
    (Int.toNat (j - ((zlength W') + 1))) = (Int.toNat ((j - 1) - (zlength W'))) := by
  lia

-- simdjson/fuzz_implementations: lib/P/Sj_num_lm_top.v (replace)
example
    {word : Type}
    (zlen : Int)
    (xs5 : word)
    (bv_unsigned : word → Int)
    (Z_to_bv : Nat → Nat → word)
    (Z_shiftl : Int → Nat → Nat)
    (k : Int)
    (h1 : (0 ≤ zlen ∧ zlen ≤ 62))
    (h2 : ((bv_unsigned xs5) = 0 ↔ zlen = 0))
    (h3 : ((bv_unsigned (Z_to_bv 64 (Z_shiftl k 48))) = 0 ↔ k = 0))
    (h4 : zlen = 0)
    (h5 : ((bv_unsigned (Z_to_bv 64 0)) = 0 ↔ (0 : Int) = 0))
    (h6 : zlen ≠ 0) :
    (Int.toNat (8 * zlen)) = (8 * ((Int.toNat zlen) - 0)) := by
  lia

-- simdjson/fuzz_implementations: lib/P/Sj_stage2_arrv.v (replace)
example {s2env T2 : Type} (E : s2env) (e_TAPE : s2env → Int) (W : T2 → Int) (s : T2) :
    ((e_TAPE E) + (8 * ((W s) + 2))) = (((e_TAPE E) + (8 * (W s))) + 16) := by
  lia

-- simdjson/fuzz_implementations: lib/Sj/SjPjDig.v (replace)
example (n : Int) (e : Int) (h1 : ((-2147483648) ≤ (n + e) ∧ (n + e) < 2147483648)) :
    ((n + 2147483648) + (e % 4294967296)) = ((n + (e % 4294967296)) + 2147483648) := by
  lia

-- simdjson/fuzz_implementations: lib/Sj/SjPjSer.v (assert)
example
    (sn : Int)
    (i : Int)
    (j : Int)
    (e : Int)
    (h1 : (0 ≤ sn ∧ sn < (2 ^ (56 : Nat))))
    (h2 : 0 ≤ i)
    (h3 : j < (2 ^ (32 : Nat)))
    (h4 : i < e)
    (h5 : (0 ≤ (e + 1) ∧ (e + 1) < (2 ^ (32 : Nat)))) :
    (0 ≤ (e + 1) ∧ (e + 1) < (2 ^ (32 : Nat))) := by
  lia

-- simdjson/fuzz_implementations: lib/U/F_printf_core_dirs.v (replace)
example
    {list_Z list_word : Type}
    (Fp : Int)
    (B : Int)
    (BS : Int)
    (q : Int)
    (lo : Int)
    (A : Int)
    (fmt : list_Z)
    (AP : Int)
    (VA : Int)
    (slots : list_word)
    (i : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_word → Int)
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : ((924512 ≤ Fp ∧ (Fp + 232) ≤ 1136568) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h5 : ((1136576 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h6 : q ≤ AP)
    (h7 : (AP + 8) ≤ VA)
    (h8 : 0 ≤ A)
    (h9 : (VA + (8 * (zlength slots))) ≤ (2 ^ (64 : Nat)))
    (h10 : 0 ≤ BS)
    (h11 : (32 ≤ (znth fmt (i + 1)) ∧ (znth fmt (i + 1)) < 64)) :
    (i + 2) = ((i + 1) + 1) := by
  lia

-- simdjson/fuzz_implementations: lib/U/Imp_ios_sb.v (replace)
example (SA : Int) (i : Int) (h1 : SA = (1000368 + (8 * (i - 1)))) :
    SA = (1000368 + ((i + (-1)) * (2 ^ (3 : Nat)))) := by
  lia

-- simdjson/fuzz_implementations: lib/U/Pj_itoa.v (replace)
example
    (q : Int)
    (lo : Int)
    (OUT : Int)
    (k : Int)
    (GLOBALS_TOP : Int)
    (h1 : lo ≤ (q - 48))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (63 : Nat)))
    (h4 : q ≤ OUT)
    (h5 : (OUT + 20) < (2 ^ (63 : Nat))) :
    (k + 1) = ((q + (-24)) + (-((q + (-25)) - k))) := by
  lia

-- simdjson/fuzz_implementations: lib/U/Pj_ser_disp.v (replace)
example
    {senv T2 T3 : Type}
    (E : senv)
    (i : Int)
    (i2 : Int)
    (e_T : senv → Int → Int)
    (ttype : T2 → Int)
    (w : T2)
    (bv_signed : T3 → Int)
    (Z_to_bv : Int → Int → T3)
    (t : Int)
    (c2 : Int)
    (c : Int)
    (h1 : (0 ≤ (e_T E i) ∧ (e_T E i) < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ (ttype w) ∧ (ttype w) < 256))
    (h3 : (bv_signed (Z_to_bv 64 t)) = t)
    (h4 : ((t = 108 ∧ (i2 = (i + 2) ∧ c2 = c)) ∨ ((t = 110 ∧ (i2 = (i + 1) ∧ c2 = c)) ∨ ((t = 116 ∧ (i2 = (i + 1) ∧ c2 = c)) ∨ (t = 117 ∧ (i2 = (i + 2) ∧ c2 = c))))))
    (h5 : (i2 = (i + 2) ∧ c2 = c))
    (h6 : (i2 = (i + 1) ∧ c2 = c)) :
    i = (i2 - 1) := by
  lia

-- simdjson/fuzz_implementations: lib/U/Pj_ser_open.v (replace)
example
    {senv list_bool sbst : Type}
    (E : senv)
    (D : Nat)
    (f : Nat)
    (d' : Nat)
    (ks : list_bool)
    (i : Int)
    (c : Int)
    (st : sbst)
    (e_j : senv → Int)
    (length : list_bool → Nat)
    (sb_size : sbst → Int)
    (sb_cap : sbst → Int)
    (t : Int)
    (h1 : ((e_j E) - (i + 1)) ≤ ((f : Nat) : Int))
    (h2 : ((d' + 1) + (length ks)) = D)
    (h3 : ((length ks) + 1) ≤ 15)
    (h4 : 1 ≤ i)
    (h5 : 0 ≤ c)
    (h6 : (sb_size st) ≤ (((41 * (i - 1)) + (6 * c)) + 3))
    (h7 : ((sb_size st) + 1) ≤ (sb_cap st))
    (h8 : (0 ≤ t ∧ t < 256)) :
    (i + 2) = ((i + 1) + 1) := by
  lia

-- simdjson/fuzz_implementations: lib/U/Sj_stage2_numr2.v (replace)
example
    {s2env list_Z T3 : Type}
    (E : s2env)
    (CP : Int)
    (t : list_Z)
    (p : Int)
    (d : Int)
    (x : Int)
    (blen : list_Z → Int)
    (e_lo : s2env → Int)
    (B : T3 → Int → Int)
    (crs : list_Z → T3)
    (h1 : 0 < CP)
    (h2 : ((CP + (blen t)) + 64) ≤ (e_lo E))
    (h3 : 0 ≤ p)
    (h4 : 1 ≤ d)
    (h5 : (p + d) ≤ (blen t))
    (h6 : (0 ≤ x ∧ x < (2 ^ (64 : Nat))))
    (h7 : (x % 256) = (B (crs t) (p + d))) :
    (CP + (p + d)) = ((CP + p) + d) := by
  lia

-- simdjson/fuzz_implementations: lib/U/Sj_stage2_numr3.v (replace)
example
    {s2env list_Z T3 : Type}
    (E : s2env)
    (CP : Int)
    (t : list_Z)
    (p : Int)
    (x : Int)
    (blen : list_Z → Int)
    (e_lo : s2env → Int)
    (B : T3 → Int → Int)
    (crs : list_Z → T3)
    (h1 : 0 < CP)
    (h2 : ((CP + (blen t)) + 64) ≤ (e_lo E))
    (h3 : (0 ≤ p ∧ p ≤ (blen t)))
    (h4 : (0 ≤ x ∧ x < (2 ^ (64 : Nat))))
    (h5 : (x % 256) = (B (crs t) p))
    (h6 : p < (blen t))
    (h7 : (p + 1) < (blen t)) :
    (CP + (p + 2)) = ((CP + p) + 2) := by
  lia

-- simdjson/fuzz_implementations: lib/U/Sj_stage2_numr3.v (replace)
example
    {s2env list_Z : Type}
    (E : s2env)
    (CP : Int)
    (t : list_Z)
    (q0 : Int)
    (blen : list_Z → Int)
    (e_lo : s2env → Int)
    (c' : Int)
    (Zpow : Int → Int → Int)
    (q' : Int)
    (h1 : 0 < CP)
    (h2 : ((CP + (blen t)) + 64) ≤ (e_lo E))
    (h3 : (0 ≤ q0 ∧ q0 ≤ (blen t)))
    (h4 : q0 < (blen t))
    (h5 : (Zpow 10 c') ≤ (10 ^ (18 : Nat)))
    (h6 : q' ≤ (q0 + c')) :
    q0 = (q0 + 0) := by
  lia

-- simdjson/fuzz_implementations: lib/U/Sj_stage2_objf.v (replace)
example
    {T1 T2 : Type}
    (e_TAPE : T1 → Int)
    (E : T1)
    (W : T2 → Int)
    (s : T2)
    (k : T2 → Int)
    (e_n : T1 → Int)
    (h1 : (k s) < (e_n E))
    (h2 : ((k s) + 1) < (e_n E))
    (h3 : ((k s) + 2) < (e_n E)) :
    ((e_TAPE E) + (8 * ((W s) + 2))) = (((e_TAPE E) + (8 * (W s))) + 16) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/AsanW/ALooseSet.v (replace)
example
    {alayout xbusy T3 T4 T5 T6 : Type}
    (L : alayout)
    (b0 : xbusy)
    (granules : T3 → Int)
    (xb_n : xbusy → T3)
    (xb_class : xbusy → Int)
    (shad : T4 → Int)
    (xb_user : alayout → xbusy → T4)
    (aslot_addr : alayout → Int → T5 → T4)
    (xb_slot : xbusy → T5)
    (shlen : T6 → Int)
    (rz_size : T3 → T6)
    (size_of_class : Int → T6)
    (h1 : (shad (xb_user L b0)) = ((shad (aslot_addr L (xb_class b0) (xb_slot b0))) + (shlen (rz_size (xb_n b0)))))
    (h2 : ((shlen (rz_size (xb_n b0))) + (granules (xb_n b0))) ≤ (shlen (size_of_class (xb_class b0))))
    (h3 : 0 ≤ (shlen (rz_size (xb_n b0)))) :
    0 = ((Int.toNat (granules (xb_n b0))) - (Int.toNat (granules (xb_n b0)))) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/AsanW/AM_kitB.v (replace)
example (n : Int) :
    0 = ((((Int.toNat (n / 8)) + 1) - (Int.toNat (n / 8))) - 1) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/AsanW/AM_lambda.v (replace)
example
    {T1 T2 : Type}
    (F1 : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (ALAM_STRDEL_RET : Int)
    (R : Int)
    (KLS : Int)
    (shad : Int → Int)
    (A : Int)
    (zlength : T2 → Int)
    (payload : T2)
    (ATOP : Int)
    (a : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) - 128))) = ((bv_unsigned sp) - 128))
    (h2 : (bv_unsigned (Z_to_bv 64 ALAM_STRDEL_RET)) = ALAM_STRDEL_RET)
    (h3 : ((R + 24) ≤ KLS ∨ 17594333495296 ≤ R))
    (h4 : (F1 % 8) = 0)
    (h5 : ((F1 + 128) ≤ KLS ∨ 17594333495296 ≤ F1))
    (h6 : (2148339200 ≤ (shad F1) ∧ ((shad F1) + 16) ≤ 17594333495296))
    (h7 : (0 ≤ A ∧ ((A + (zlength payload)) ≤ ATOP ∧ ((A % 8) = 0 ∧ (((A + (zlength payload)) ≤ 2147446784 ∨ 17594333495296 ≤ A) ∧ (((A + (zlength payload)) ≤ F1 ∨ (F1 + 128) ≤ A) ∧ ((A + (zlength payload)) ≤ R ∨ (R + 24) ≤ A)))))))
    (h8 : (zlength payload) = 0)
    (h9 : (¬ (A ≤ a ∧ a < (A + (zlength payload))))) :
    (F1 + 64) = (F1 + ((64 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/AsanW/AM_lambda.v (replace)
example
    {T1 T2 : Type}
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (Z_to_bv : Int → Int → T1)
    (ALAM_STRDEL_RET : Int)
    (R : Int)
    (KLS : Int)
    (F1 : Int)
    (shad : Int → Int)
    (A : Int)
    (zlength : T2 → Int)
    (payload : T2)
    (ATOP : Int)
    (a : Int)
    (P : Int)
    (A' : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) - 128))) = ((bv_unsigned sp) - 128))
    (h2 : (bv_unsigned (Z_to_bv 64 ALAM_STRDEL_RET)) = ALAM_STRDEL_RET)
    (h3 : ((R + 24) ≤ KLS ∨ 17594333495296 ≤ R))
    (h4 : (F1 % 8) = 0)
    (h5 : ((F1 + 128) ≤ KLS ∨ 17594333495296 ≤ F1))
    (h6 : (2148339200 ≤ (shad F1) ∧ ((shad F1) + 16) ≤ 17594333495296))
    (h7 : (0 ≤ A ∧ ((A + (zlength payload)) ≤ ATOP ∧ ((A % 8) = 0 ∧ (((A + (zlength payload)) ≤ 2147446784 ∨ 17594333495296 ≤ A) ∧ (((A + (zlength payload)) ≤ F1 ∨ (F1 + 128) ≤ A) ∧ ((A + (zlength payload)) ≤ R ∨ (R + 24) ≤ A)))))))
    (h8 : (zlength payload) = 0)
    (h9 : (¬ (A ≤ a ∧ a < (A + (zlength payload)))))
    (h10 : ((P + 56) ≤ KLS ∨ 17594333495296 ≤ P))
    (h11 : (A' % 8) = 0)
    (h12 : (2148339200 ≤ (shad A') ∧ ((shad A') + 7) ≤ 17594333495296))
    (h13 : (((shad A') + 7) ≤ (shad F1) ∨ ((shad F1) + 16) ≤ (shad A'))) :
    ((bv_unsigned sp) - 16) = (((bv_unsigned sp) - 128) + ((112 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/AsanW/AM_lambda.v (replace)
example
    {T1 T2 : Type}
    (F1 : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (ALAM_STRDEL_RET : Int)
    (R : Int)
    (KLS : Int)
    (shad : Int → Int)
    (A : Int)
    (zlength : T2 → Int)
    (payload : T2)
    (ATOP : Int)
    (a : Int)
    (P : Int)
    (A' : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) - 128))) = ((bv_unsigned sp) - 128))
    (h2 : (bv_unsigned (Z_to_bv 64 ALAM_STRDEL_RET)) = ALAM_STRDEL_RET)
    (h3 : ((R + 24) ≤ KLS ∨ 17594333495296 ≤ R))
    (h4 : (F1 % 8) = 0)
    (h5 : ((F1 + 128) ≤ KLS ∨ 17594333495296 ≤ F1))
    (h6 : (2148339200 ≤ (shad F1) ∧ ((shad F1) + 16) ≤ 17594333495296))
    (h7 : (0 ≤ A ∧ ((A + (zlength payload)) ≤ ATOP ∧ ((A % 8) = 0 ∧ (((A + (zlength payload)) ≤ 2147446784 ∨ 17594333495296 ≤ A) ∧ (((A + (zlength payload)) ≤ F1 ∨ (F1 + 128) ≤ A) ∧ ((A + (zlength payload)) ≤ R ∨ (R + 24) ≤ A)))))))
    (h8 : (zlength payload) = 0)
    (h9 : (¬ (A ≤ a ∧ a < (A + (zlength payload)))))
    (h10 : ((P + 56) ≤ KLS ∨ 17594333495296 ≤ P))
    (h11 : (A' % 8) = 0)
    (h12 : (2148339200 ≤ (shad A') ∧ ((shad A') + 7) ≤ 17594333495296))
    (h13 : (((shad A') + 7) ≤ (shad F1) ∨ ((shad F1) + 16) ≤ (shad A'))) :
    (F1 + 120) = ((F1 + 88) + ((32 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/AsanW/AM_minify.v (replace)
example
    {word list_Z : Type}
    (sp : word)
    (D : Int)
    (DST : Int)
    (RS : Int)
    (pl : list_Z)
    (lo : Int)
    (bv_unsigned : word → Int)
    (zlength : list_Z → Int)
    (KHIGH : Int)
    (KLOW : Int)
    (KEND : Int)
    (h1 : 0 ≤ D)
    (h2 : (D % 8) = 0)
    (h3 : (DST % 8) = 0)
    (h4 : (RS % 8) = 0)
    (h5 : (zlength pl) < (2 ^ (26 : Nat)))
    (h6 : lo ≤ ((bv_unsigned sp) - 16))
    (h7 : KHIGH ≤ lo)
    (h8 : (D + (zlength pl)) ≤ lo)
    (h9 : (DST + (zlength pl)) ≤ lo)
    (h10 : (RS + 8) ≤ lo)
    (h11 : ((DST + (zlength pl)) ≤ KLOW ∨ KHIGH ≤ DST))
    (h12 : ((DST + (zlength pl)) ≤ D ∨ (D + (zlength pl)) ≤ DST))
    (h13 : ((DST + (zlength pl)) ≤ RS ∨ (RS + 8) ≤ DST))
    (h14 : 0 ≤ DST)
    (h15 : ((DST + (zlength pl)) + 8) ≤ KEND)
    (h16 : ((D + (zlength pl)) + 8) ≤ KEND)
    (h17 : 0 ≤ RS)
    (h18 : (RS + 8) ≤ KEND)
    (h19 : 0 ≤ (zlength pl)) :
    ((bv_unsigned sp) + (-16)) = ((bv_unsigned sp) - 16) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/AM_fake_arep3.v (replace)
example {T1 : Type} (al_fake : T1 → Int) (L : T1) :
    (((al_fake L) + 24) + 8) = ((((al_fake L) + ((8 : Nat) : Int)) + ((16 : Nat) : Int)) + ((8 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/AM_fake_arep3.v (replace)
example
    {T1 : Type}
    (shad : Int → Int)
    (F : Int)
    (al_fake : T1 → Int)
    (L : T1)
    (pos : Int)
    (fk_frame : T1 → Int → Int → Int)
    (shlen : Int → Int)
    (h1 : (0 ≤ pos ∧ pos < 2048))
    (h2 : F = (fk_frame L 3 pos))
    (h3 : (shad F) = (2147450880 + (F / 8)))
    (h4 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h5 : ((((shad (al_fake L)) + 397824) + (64 * pos)) = (shad F) ∧ (((shad F) + 64) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 64) ≤ 17594333495296)))
    (h6 : (((shad F) + 64) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F))) :
    (((shad F) + 16) + 16) = (((shad F) + ((16 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/AM_harness.v (replace)
example
    (shad : Int → Int)
    (SPA : Int)
    (h1 : (0 ≤ (shad (SPA + 128)) ∧ ((shad (SPA + 128)) + 3) ≤ (2 ^ (64 : Nat)))) :
    ((shad (SPA + 128)) + 1) = ((shad (SPA + 128)) + ((1 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/AM_lambda.v (replace)
example
    {T1 T2 : Type}
    (F1 : Int)
    (bv_unsigned : T1 → Int)
    (Z_to_bv : Int → Int → T1)
    (sp : T1)
    (ALAM_STRDEL_RET : Int)
    (R : Int)
    (KLS : Int)
    (shad : Int → Int)
    (A : Int)
    (zlength : T2 → Int)
    (payload : T2)
    (ATOP : Int)
    (D : Int)
    (a : Int)
    (P : Int)
    (A' : Int)
    (h1 : (bv_unsigned (Z_to_bv 64 ((bv_unsigned sp) - 128))) = ((bv_unsigned sp) - 128))
    (h2 : (bv_unsigned (Z_to_bv 64 ALAM_STRDEL_RET)) = ALAM_STRDEL_RET)
    (h3 : ((R + 24) ≤ KLS ∨ 17594333495296 ≤ R))
    (h4 : (F1 % 8) = 0)
    (h5 : ((F1 + 128) ≤ KLS ∨ 17594333495296 ≤ F1))
    (h6 : (2148345856 ≤ (shad F1) ∧ ((shad F1) + 16) ≤ 17594333495296))
    (h7 : (0 ≤ A ∧ ((A + (zlength payload)) ≤ ATOP ∧ ((A % 8) = 0 ∧ (((A + (zlength payload)) ≤ 2147446784 ∨ 17594333495296 ≤ A) ∧ (((A + (zlength payload)) ≤ F1 ∨ (F1 + 128) ≤ A) ∧ ((A + (zlength payload)) ≤ R ∨ (R + 24) ≤ A)))))))
    (h8 : (zlength payload) = 0)
    (h9 : 0 < D)
    (h10 : (¬ (A ≤ a ∧ a < (A + (zlength payload)))))
    (h11 : ((P + 56) ≤ KLS ∨ 17594333495296 ≤ P))
    (h12 : (A' % 8) = 0)
    (h13 : (2148345856 ≤ (shad A') ∧ ((shad A') + 7) ≤ 17594333495296))
    (h14 : (((shad A') + 7) ≤ (shad F1) ∨ ((shad F1) + 16) ≤ (shad A'))) :
    (F1 + 120) = ((F1 + 88) + ((32 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/AM_vdtorf.v (replace)
example
    (n : Int)
    (beg : Int)
    (V : Int)
    (rup8 : Int → Int)
    (shad : Int → Int)
    (Z_shiftr : Int → Int → Int)
    (G : Int)
    (X : Int)
    (ATOP : Int)
    (h1 : ((V + 24) ≤ 2147446784 ∨ 17594333495296 ≤ V))
    (h2 : (beg % 8) = 0)
    (h3 : (n ≤ (rup8 n) ∧ (rup8 n) ≤ (n + 7)))
    (h4 : ((V + 24) ≤ beg ∨ (beg + (rup8 n)) ≤ V))
    (h5 : (shad V) = ((Z_shiftr V 3) + 2147450880))
    (h6 : ((Z_shiftr (V + 16) 3) + 2147450880) = ((shad V) + 2))
    (h7 : (2147450880 ≤ (shad V) ∧ ((shad V) + 3) ≤ 17594333495296))
    (h8 : (2147450880 ≤ (shad beg) ∧ ((shad beg) + G) ≤ 17594333495296))
    (h9 : (((shad V) + 3) ≤ (shad beg) ∨ ((shad beg) + G) ≤ (shad V)))
    (h10 : (((shad beg) + G) ≤ ((Z_shiftr X 3) + 2147450880) ∧ ((((Z_shiftr X 3) + 2147450880) + 1) ≤ ATOP ∧ (2147450880 ≤ ((Z_shiftr X 3) + 2147450880) ∧ (((Z_shiftr X 3) + 2147450880) + 1) ≤ 17594333495296)))) :
    n = ((beg + n) - beg) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/ATsafeClient.v (replace)
example {T1 : Type} (v : Int) (CUB : T1 → Int) (CLIENT_VEC_BYTES : T1) (COSTF : Int) :
    (v - (CUB CLIENT_VEC_BYTES)) = ((v - ((CUB CLIENT_VEC_BYTES) + COSTF)) + COSTF) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/ATsafeEv.v (replace)
example
    {T1 T2 T3 : Type}
    (st : T1)
    (c : Int)
    (nf : Int)
    (extra : Int)
    (region_beg : T1 → Int → Int)
    (K_FREEARR_OFF : Int)
    (c_mapped_free_array : T2 → Int)
    (get_cls : T1 → Int → T2)
    (rup : Int → T3 → Int)
    (K_FREEARR_MAP : T3)
    (FCAP : Int → Int)
    (h1 : (1 ≤ c ∧ c ≤ 31))
    (h2 : 0 ≤ extra)
    (h3 : (rup (nf * 4) K_FREEARR_MAP) ≤ (FCAP c))
    (h4 : 0 ≤ nf)
    (h5 : ((c_mapped_free_array (get_cls st c)) % 4096) = 0) :
    ((region_beg st c) + (K_FREEARR_OFF + (c_mapped_free_array (get_cls st c)))) = (((region_beg st c) + K_FREEARR_OFF) + (c_mapped_free_array (get_cls st c))) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/ATsafeEv.v (replace)
example
    {T1 T2 T3 T4 : Type}
    (st : T1)
    (c : Int)
    (nf : Int)
    (extra : Int)
    (PHI : T1 → Int)
    (put_cls : Int → T2 → T1 → T1)
    (r' : T2)
    (nm : Int)
    (c_mapped_free_array : T3 → Int)
    (get_cls : T1 → Int → T3)
    (rup : Int → T4 → Int)
    (K_FREEARR_MAP : T4)
    (FCAP : Int → Int)
    (h1 : (1 ≤ c ∧ c ≤ 31))
    (h2 : 0 ≤ extra)
    (h3 : (rup (nf * 4) K_FREEARR_MAP) ≤ (FCAP c))
    (h4 : 0 ≤ nf)
    (h5 : (nm % 4096) = 0)
    (h6 : ((c_mapped_free_array (get_cls st c)) % 4096) = 0)
    (h7 : (PHI (put_cls c r' st)) = ((PHI st) - (nm - (c_mapped_free_array (get_cls st c))))) :
    ((PHI (put_cls c r' st)) + extra) = (((PHI st) + extra) - (nm - (c_mapped_free_array (get_cls st c)))) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/AU_first_C.v (replace)
example
    {T1 : Type}
    (V : Int)
    (Z_shiftr : Int → Int → Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (h1 : (2148323080 ≤ ((Z_shiftr V 3) + 2147450880) ∧ (((Z_shiftr V 3) + 2147450880) + 1) ≤ 17594333495296))
    (h2 : (2148323080 ≤ ((Z_shiftr ((bv_unsigned sp) + (-216)) 3) + 2147450880) ∧ ((((Z_shiftr ((bv_unsigned sp) + (-184)) 3) + 2147450880) + 1) ≤ 17594333495296 ∧ ((Z_shiftr ((bv_unsigned sp) + (-208)) 3) = ((Z_shiftr ((bv_unsigned sp) + (-216)) 3) + 1) ∧ ((Z_shiftr ((bv_unsigned sp) + (-200)) 3) = ((Z_shiftr ((bv_unsigned sp) + (-216)) 3) + 2) ∧ ((Z_shiftr ((bv_unsigned sp) + (-192)) 3) = ((Z_shiftr ((bv_unsigned sp) + (-216)) 3) + 3) ∧ (Z_shiftr ((bv_unsigned sp) + (-184)) 3) = ((Z_shiftr ((bv_unsigned sp) + (-216)) 3) + 4))))))) :
    (V + 8) = (8 + V) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/BM_clear.v (replace)
example
    (k : Int)
    (beg : Int)
    (V : Int)
    (n : Int)
    (rup8 : Int → Int)
    (shad : Int → Int)
    (Z_shiftr : Int → Int → Int)
    (G : Int)
    (h1 : ((V + 24) ≤ 2147446784 ∨ 17594333495296 ≤ V))
    (h2 : (n ≤ (rup8 n) ∧ (rup8 n) ≤ (n + 7)))
    (h3 : (shad V) = ((Z_shiftr V 3) + 2147450880))
    (h4 : ((Z_shiftr (V + 8) 3) + 2147450880) = ((shad V) + 1))
    (h5 : (2147450880 ≤ (shad V) ∧ ((shad V) + 3) ≤ 17594333495296))
    (h6 : (2147450880 ≤ (shad beg) ∧ ((shad beg) + G) ≤ 17594333495296))
    (h7 : (((shad V) + 3) ≤ (shad beg) ∨ ((shad beg) + G) ≤ (shad V))) :
    k = ((beg + k) - beg) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/BothW/F_printf_core_flags.v (replace)
example
    {region list_Z : Type}
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
    (p : Int)
    (k : Int)
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (KHIGH : Int)
    (r_lo : region → Int)
    (r_hi : region → Int)
    (znth : list_Z → Int → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 1495040)
    (h5 : ((1531176 ≤ Fp ∧ (Fp + 232) ≤ 1561720) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((7151344 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS)
    (h11 : KHIGH ≤ lo)
    (h12 : ((r_lo rstk) ≤ lo ∧ q ≤ (r_hi rstk)))
    (h13 : (p + k) < (zlength fmt))
    (h14 : (32 ≤ (znth fmt (p + k)) ∧ (znth fmt (p + k)) < 64)) :
    ((p + k) + 1) = (p + (k + 1)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/Malloc/ASlot_M4P.v (replace)
example
    {region : Type}
    (sc : Int)
    (cnt : Int)
    (ai : Int)
    (ml : Int)
    (r0 : region)
    (req : Int)
    (nd : Int)
    (size_class : Int → Int)
    (r_len : region → Int)
    (round_up_pg : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (1 ≤ cnt ∧ cnt ≤ 32))
    (h3 : (0 ≤ ai ∧ ai ≤ (cnt - 1)))
    (h4 : (1 ≤ ml ∧ ml < (2 ^ (28 : Nat))))
    (h5 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h6 : (req + 4) ≤ (16 * (size_class sc)))
    (h7 : (r_len r0) = nd)
    (h8 : nd = (4096 * ml))
    (h9 : (req + 20) ≤ nd)
    (h10 : (16 * (size_class sc)) < (2 ^ (18 : Nat)))
    (h11 : ((cnt = 1 ∧ nd < ((req + 20) + 4096)) ∨ ((((16 * (size_class sc)) * cnt) + 16) ≤ nd ∧ nd < ((((16 * (size_class sc)) * cnt) + 16) + 4096))))
    (h12 : (round_up_pg nd) = nd) :
    ((-ml) * 4096) = (-(4096 * ml)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/Malloc/ASlot_M4P.v (replace)
example
    {aptr region T3 mstate : Type}
    (sc : Int)
    (cnt : Int)
    (ai : Int)
    (ml : Int)
    (mt : aptr)
    (r0 : region)
    (req : Int)
    (nd : Int)
    (get_stride : T3 → Int)
    (get_meta_rec : mstate → aptr → T3)
    (stF : mstate)
    (size_class : Int → Int)
    (r_len : region → Int)
    (round_up_pg : Int → Int)
    (mask_upto : Int → Int)
    (h1 : (0 ≤ sc ∧ sc < 48))
    (h2 : (1 ≤ cnt ∧ cnt ≤ 32))
    (h3 : (0 ≤ ai ∧ ai ≤ (cnt - 1)))
    (h4 : (1 ≤ ml ∧ ml < (2 ^ (28 : Nat))))
    (h5 : (0 ≤ req ∧ req < (2 ^ (32 : Nat))))
    (h6 : (req + 4) ≤ (16 * (size_class sc)))
    (h7 : (r_len r0) = nd)
    (h8 : nd = (4096 * ml))
    (h9 : (req + 20) ≤ nd)
    (h10 : (16 * (size_class sc)) < (2 ^ (18 : Nat)))
    (h11 : ((cnt = 1 ∧ nd < ((req + 20) + 4096)) ∨ ((((16 * (size_class sc)) * cnt) + 16) ≤ nd ∧ nd < ((((16 * (size_class sc)) * cnt) + 16) + 4096))))
    (h12 : (round_up_pg nd) = nd)
    (h13 : (mask_upto ai) ≤ (mask_upto (cnt - 1))) :
    16 = ((0 + 16) + ((get_stride (get_meta_rec stF mt)) * 0)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/Plain/F_printf_core_pro.v (replace)
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
    (PC_DEPTH : Int)
    (GLOBALS_TOP : Int)
    (zlength : list_Z → Int)
    (h1 : lo ≤ (q - PC_DEPTH))
    (h2 : GLOBALS_TOP ≤ lo)
    (h3 : q < (2 ^ (47 : Nat)))
    (h4 : (A + (zlength fmt)) ≤ 131072)
    (h5 : ((852800 ≤ Fp ∧ (Fp + 232) ≤ 1064088) ∨ ((AP + 8) ≤ Fp ∧ (Fp + 232) ≤ VA)))
    (h6 : ((1064096 ≤ B ∧ (B + BS) ≤ lo) ∨ ((AP + 8) ≤ B ∧ (B + BS) ≤ VA)))
    (h7 : q ≤ AP)
    (h8 : (AP + 8) ≤ VA)
    (h9 : 0 ≤ A)
    (h10 : 0 ≤ BS) :
    (q + (-432)) = ((q + (-112)) - ((320 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/Plain/PIosFxSound.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (E : T1)
    (allkn : T2)
    (rb : T3)
    (rk : T4)
    (n : Nat)
    (K : T5)
    (estart : T1 → T6 → Int)
    (SA : T3 → T4 → T6)
    (kb : T3)
    (kk : T4)
    (j : Nat)
    (kentry_overlay : T2 → T3 → T4 → Nat → T5 → Bool)
    (h1 : 1 ≤ n)
    (h2 : n ≤ 8)
    (h3 : (kentry_overlay allkn rb rk n K) = true) :
    ((estart E (SA kb kk)) + (((estart E (SA rb rk)) - (estart E (SA kb kk))) + ((j : Nat) : Int))) = ((estart E (SA rb rk)) + ((j : Nat) : Int)) := by
  lia

-- simdjson/fuzz_minifyimpl: lib/Plain/PM_minify.v (replace)
example
    {list_Z : Type}
    (D : Int)
    (B : Int)
    (R : Int)
    (pl : list_Z)
    (k : Int)
    (zlength : list_Z → Int)
    (PJT : Int)
    (length : list_Z → Nat)
    (h1 : 0 ≤ D)
    (h2 : 0 ≤ B)
    (h3 : (zlength pl) < (2 ^ (26 : Nat)))
    (h4 : (D + (zlength pl)) < (2 ^ (47 : Nat)))
    (h5 : (B + (zlength pl)) < (2 ^ (47 : Nat)))
    (h6 : (0 ≤ R ∧ (R + 8) < (2 ^ (64 : Nat))))
    (h7 : ((D + (zlength pl)) ≤ B ∨ (B + (zlength pl)) ≤ D))
    (h8 : ((R + 8) ≤ B ∨ (B + (zlength pl)) ≤ R))
    (h9 : ((R + 8) ≤ D ∨ (D + (zlength pl)) ≤ R))
    (h10 : ((PJT + 768) ≤ D ∨ (D + (zlength pl)) ≤ PJT))
    (h11 : (length pl) = (Int.toNat (zlength pl))) :
    (D + (k + 1)) = ((D + k) + 1) := by
  lia

-- simdjson/fuzz_ondemand: lib/A/Atp_h_pushA.v (replace)
example (c : Int) (h1 : 0 ≤ c) :
    ((2 * c) * (2 ^ (3 : Nat))) = (16 * c) := by
  lia

-- simdjson/fuzz_ondemand: lib/A/Atp_h_pushA.v (replace)
example
    {T1 : Type}
    (usp : Int)
    (Z_to_bv : Int → Int → T1)
    (bv_unsigned : T1 → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 (usp + (-96)))) = (usp + (-96)))
    (h2 : ((usp + (-96)) % 16) = 0) :
    (usp + ((-6) * 16)) = (usp + (-96)) := by
  lia

-- simdjson/fuzz_ondemand: lib/A/Od_s1zA.v (replace)
example
    {s1env T2 : Type}
    (E : s1env)
    (bv_unsigned : T2 → Int)
    (e_sp : s1env → T2)
    (e_len : s1env → Int)
    (e_lo : s1env → Int)
    (h1 : (e_len E) = 0)
    (h2 : 0 ≤ (e_lo E)) :
    ((bv_unsigned (e_sp E)) + (-144)) = (((bv_unsigned (e_sp E)) + (-400)) + ((256 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_ondemand: lib/A/Od_setupaA.v (replace)
example
    {T1 T2 : Type}
    (S1 : Int)
    (Z_to_bv : Int → Int → T1)
    (n : Int)
    (d : Int)
    (lo : Int)
    (bv_unsigned : T1 → Int)
    (shad : Int → Int)
    (f : Int)
    (length : T2 → Nat)
    (bs' : T2)
    (h1 : (0 ≤ n ∧ n < (2 ^ (64 : Nat))))
    (h2 : ((0 ≤ d ∧ d < (2 ^ (64 : Nat))) ∧ (d + n) ≤ lo))
    (h3 : (bv_unsigned (Z_to_bv 64 S1)) = S1)
    (h4 : (shad (f + 512)) = ((shad f) + 64))
    (h5 : 0 ≤ (f / 8))
    (h6 : n = ((((length bs') : Nat) : Int) + 1))
    (h7 : 0 ≤ (d / 8))
    (h8 : (((d / 8) + 2147450880) + 1) ≤ S1) :
    (S1 + 376) = ((S1 + 352) + ((24 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_ondemand: lib/B/Atp_h_destroyA.v (replace)
example
    {T1 : Type}
    (usp : Int)
    (Z_to_bv : Int → Int → T1)
    (bv_unsigned : T1 → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 (usp + (-16)))) = (usp + (-16))) :
    (usp + ((-1) * 16)) = (usp + (-16)) := by
  lia

-- simdjson/fuzz_ondemand: lib/B/Atp_h_pushA.v (replace)
example
    {T1 : Type}
    (A : Int)
    (size : Int)
    (Z_to_bv : Int → Int → T1)
    (usp : Int)
    (bv_unsigned : T1 → Int)
    (h1 : (bv_unsigned (Z_to_bv 64 (usp + (-80)))) = (usp + (-80)))
    (h2 : ((usp + (-80)) % 16) = 0)
    (h3 : ((A + (16 * size)) % 8) = 0)
    (h4 : (((A + (16 * (size + 1))) - 16) % 8) = 0) :
    (A + (16 * size)) = ((A + (16 * (size + 1))) - 16) := by
  lia

-- simdjson/fuzz_ondemand: lib/B/Od_setupc1B.v (replace)
example
    {T1 T2 : Type}
    (F : Int)
    (len0 : Int)
    (od_copied : T1 → Bool)
    (dz : T1)
    (shad : Int → Int)
    (sc_idx : T2 → Int)
    (L : T2)
    (SB : Int)
    (CAP : Int)
    (lo : Int)
    (CN : Int)
    (COPY : Int)
    (h1 : 0 ≤ len0)
    (h2 : (od_copied dz) = (decide (len0 ≤ 1048512)))
    (h3 : (shad (F + 512)) = ((shad F) + 64))
    (h4 : 0 ≤ (F / 8))
    (h5 : (sc_idx L) ≤ 4194340)
    (h6 : (SB + CAP) ≤ lo)
    (h7 : (CN = 0 ∨ ((SB + CAP) ≤ COPY ∨ (COPY + CN) ≤ SB))) :
    (F + 112) = ((F + 104) + ((8 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_ondemand: lib/B/Od_setupc1B.v (replace)
example
    {T1 T2 : Type}
    (F : Int)
    (len0 : Int)
    (od_copied : T1 → Bool)
    (dz : T1)
    (shad : Int → Int)
    (sc_idx : T2 → Int)
    (L : T2)
    (SB : Int)
    (CAP : Int)
    (lo : Int)
    (CN : Int)
    (COPY : Int)
    (IMPL : Int)
    (IDX : Int)
    (h1 : 0 ≤ len0)
    (h2 : (od_copied dz) = (decide (len0 ≤ 1048512)))
    (h3 : (shad (F + 512)) = ((shad F) + 64))
    (h4 : 0 ≤ (F / 8))
    (h5 : (sc_idx L) ≤ 4194340)
    (h6 : (SB + CAP) ≤ lo)
    (h7 : (CN = 0 ∨ ((SB + CAP) ≤ COPY ∨ (COPY + CN) ≤ SB)))
    (h8 : ((IMPL + 96) ≤ lo ∧ (IDX + (sc_idx L)) ≤ lo))
    (h9 : ((IMPL + 96) ≤ IDX ∨ (IDX + (sc_idx L)) ≤ IMPL))
    (h10 : (CN = 0 ∨ (((IMPL + 96) ≤ COPY ∨ (COPY + CN) ≤ IMPL) ∧ ((IDX + (sc_idx L)) ≤ COPY ∨ (COPY + CN) ≤ IDX)))) :
    (F + 112) = ((F + 104) + ((8 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_ondemand: lib/B/Od_setupc1B.v (replace)
example
    {T1 : Type}
    (F : Int)
    (len0 : Int)
    (od_copied : T1 → Bool)
    (dz : T1)
    (shad : Int → Int)
    (sc_idx : Int → Int)
    (L : Int)
    (SB : Int)
    (CAP : Int)
    (lo : Int)
    (CN : Int)
    (COPY : Int)
    (IMPL : Int)
    (IDX : Int)
    (icap : Nat)
    (roundup64 : Int → Int)
    (h1 : 0 ≤ len0)
    (h2 : (od_copied dz) = (decide (len0 ≤ 1048512)))
    (h3 : (shad (F + 512)) = ((shad F) + 64))
    (h4 : 0 ≤ (F / 8))
    (h5 : (sc_idx L) ≤ 4194340)
    (h6 : (SB + CAP) ≤ lo)
    (h7 : (CN = 0 ∨ ((SB + CAP) ≤ COPY ∨ (COPY + CN) ≤ SB)))
    (h8 : ((IMPL + 96) ≤ lo ∧ (IDX + (sc_idx L)) ≤ lo))
    (h9 : ((IMPL + 96) ≤ IDX ∨ (IDX + (sc_idx L)) ≤ IMPL))
    (h10 : (CN = 0 ∨ (((IMPL + 96) ≤ COPY ∨ (COPY + CN) ≤ IMPL) ∧ ((IDX + (sc_idx L)) ≤ COPY ∨ (COPY + CN) ≤ IDX))))
    (h11 : ((IMPL % 8) = 0 ∧ ((IDX % 8) = 0 ∧ (SB % 8) = 0)))
    (h12 : ((4 * ((icap : Nat) : Int)) = (sc_idx L) ∧ (L + 9) ≤ ((icap : Nat) : Int)))
    (h13 : (0 ≤ ((roundup64 L) + 9) ∧ L ≤ (roundup64 L))) :
    (F + 136) = ((F + 120) + ((16 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_ondemand: lib/B/Od_setupkB.v (replace)
example
    (n : Nat)
    (a : Nat)
    (c : Int)
    (s : Int)
    (vcap_after : Int → Int → Int)
    (h1 : ((a : Nat) : Int) = (c - s))
    (h2 : a < n)
    (h3 : (vcap_after c c) = (2 * c)) :
    ((((n : Nat) : Int) - ((a : Nat) : Int)) - 1) = ((((n - a) - 1) : Nat) : Int) := by
  lia

-- simdjson/fuzz_ondemand: lib/B/Sj_num_lm_tkit.v (assert)
example
    {word : Type}
    (sp : word)
    (X : Int)
    (lo : Int)
    (d : Int)
    (spq : Int)
    (f : Int)
    (a : Int)
    (n : Int)
    (LMB_STACK : Int)
    (bv_unsigned : word → Int)
    (USTACK_TOP : Int)
    (h1 : (lo + LMB_STACK) ≤ (bv_unsigned sp))
    (h2 : ((bv_unsigned sp) + 16) ≤ USTACK_TOP)
    (h3 : ((d = 0 ∨ d = 16) ∧ spq = (((bv_unsigned sp) - 224) - d)))
    (h4 : ((f % 64) = 0 ∧ (6787072 ≤ f ∧ ((f + 2040) ≤ lo ∧ (((f + 2040) ≤ ((f / 8) + 2147450880) ∨ (((f / 8) + 2147450880) + 255) ≤ f) ∧ (0 ≤ ((f / 8) + 2147450880) ∧ (((f / 8) + 2147450880) + 255) ≤ lo))))))
    (h5 : (X % 8) = 0)
    (h6 : (6787072 ≤ X ∧ ((X + 504) ≤ lo ∧ (((X + 504) ≤ ((X / 8) + 2147450880) ∨ (((X / 8) + 2147450880) + 63) ≤ X) ∧ (0 ≤ ((X / 8) + 2147450880) ∧ (((X / 8) + 2147450880) + 63) ≤ lo)))))
    (h7 : (((X + 504) ≤ f ∨ (f + 2048) ≤ X) ∧ (((X + 504) ≤ ((f / 8) + 2147450880) ∨ (((f / 8) + 2147450880) + 256) ≤ X) ∧ (((((X / 8) + 2147450880) + 63) ≤ f ∨ (f + 2048) ≤ ((X / 8) + 2147450880)) ∧ ((((X / 8) + 2147450880) + 63) ≤ ((f / 8) + 2147450880) ∨ (((f / 8) + 2147450880) + 256) ≤ ((X / 8) + 2147450880))))))
    (h8 : 0 ≤ n)
    (h9 : (((spq + 120) ≤ a ∧ (a + n) ≤ (bv_unsigned sp)) ∨ ((f ≤ a ∧ (a + n) ≤ (f + 528)) ∨ (((f / 8) + 2147450880) ≤ a ∧ (a + n) ≤ (((f / 8) + 2147450880) + 67))))) :
    (0 ≤ d ∧ d ≤ 16) := by
  lia

-- simdjson/fuzz_ondemand: lib/MallocP/RF_enframe.v (replace)
example
    (P0 : Int)
    (B : Int)
    (stride : Int)
    (k : Int)
    (mword : Int)
    (Z_land : Int → Int → Int)
    (last_idx : Int)
    (Z_shiftr : Int → Int → Int)
    (sc : Int)
    (maplen : Int)
    (sxv : Int → Int)
    (ctr : Int)
    (off0 : Int)
    (off : Int)
    (n : Int)
    (fold_off : Int → Int → Int)
    (slack : Int)
    (h1 : (0 ≤ mword ∧ mword < (2 ^ (64 : Nat))))
    (h2 : (Z_land mword 31) = last_idx)
    (h3 : (Z_land (Z_shiftr mword 5) 126) = (2 * sc))
    (h4 : (Z_land mword 18446744073709547520) = (4096 * maplen))
    (h5 : (Z_shiftr mword 12) = maplen)
    (h6 : (Z_land (sxv ctr) 255) = (Z_land ctr 255))
    (h7 : (0 ≤ off0 ∧ off0 < 256))
    (h8 : 0 ≤ (stride * k))
    (h9 : (16 ≤ stride ∧ (B + 16) ≤ P0))
    (h10 : P0 = ((B + 16) + (stride * k)))
    (h11 : off = (fold_off off0 slack))
    (h12 : slack = (((stride - 4) - n) / 16)) :
    P0 = ((B + (stride * k)) + 16) := by
  lia

-- simdjson/fuzz_ondemand: lib/P/Sj_h_bom.v (replace)
example (d : Int) (h1 : ((-256) < d ∧ d < 256)) (h2 : d ≠ 0) :
    ((d + 18446744073709551616) + ((-1) * 18446744073709551616)) = d := by
  lia

-- simdjson/fuzz_ondemand: lib/P/Sj_stage1_tail.v (replace)
example
    {s1env list_Z : Type}
    (E : s1env)
    (out : list_Z)
    (n : Int)
    (e_IDX : s1env → Int)
    (length : list_Z → Nat)
    (e_len : s1env → Int)
    (h1 : (((length out) : Nat) : Int) ≤ (e_len E)) :
    (n * (2 ^ (2 : Nat))) = (((e_IDX E) + (4 * n)) - (e_IDX E)) := by
  lia

-- simdjson/fuzz_ondemand: lib/U/Od_arm_nest.v (replace)
example
    {odenv T2 : Type}
    (E : odenv)
    (o_IDX : odenv → Int)
    (o_pos : T2 → Int)
    (st : T2)
    (o_depth : T2 → Int)
    (h1 : (o_depth st) = 2)
    (h2 : 1 ≤ (o_pos st))
    (h3 : ((((o_IDX E) + (4 * (o_pos st))) + 4) % 4) = 0) :
    ((o_IDX E) + (4 * ((o_pos st) + 1))) = (((o_IDX E) + (4 * (o_pos st))) + 4) := by
  lia

-- simdjson/fuzz_ondemand: lib/U/Od_fromch.v (replace)
example
    {word list_byte : Type}
    (sp : word)
    (A : Int)
    (off : Int)
    (stop : Int)
    (lo : Int)
    (txt : list_byte)
    (cur : Int)
    (FFU_STACK : Int)
    (bv_unsigned : word → Int)
    (NUMU_GTOP : Int)
    (length : list_byte → Nat)
    (NUM_TXT_MAX : Int)
    (h1 : (lo + FFU_STACK) ≤ (bv_unsigned sp))
    (h2 : NUMU_GTOP ≤ lo)
    (h3 : ((bv_unsigned sp) % 16) = 0)
    (h4 : (A + (((length txt) : Nat) : Int)) ≤ lo)
    (h5 : (((length txt) : Nat) : Int) < NUM_TXT_MAX)
    (h6 : 0 < A)
    (h7 : (0 ≤ off ∧ off ≤ stop))
    (h8 : 0 ≤ lo) :
    (cur + 1) = (((A + cur) + 1) - A) := by
  lia

-- simdjson/fuzz_parser: lib/AsanW/APC_create.v (replace)
example (AIM : Int) (h1 : (AIM % 8) = 0) :
    (AIM + 50) = ((AIM + 48) + ((2 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_parser: lib/AsanW/APC_create.v (replace)
example
    {T1 : Type}
    (AIM : Int)
    (bv_unsigned : T1 → Int)
    (sp : T1)
    (ATOP : Int)
    (h1 : (AIM % 8) = 0)
    (h2 : ATOP ≤ (bv_unsigned sp)) :
    (((AIM + 56) + 8) + 8) = (AIM + 72) := by
  lia

-- simdjson/fuzz_parser: lib/BothW/AD_handoff0.v (replace)
example
    {list_mfact T2 : Type}
    (l : list_mfact)
    (lo : Int)
    (n : Int)
    (i : Int)
    (a' : Int)
    (existsb : T2 → list_mfact → Bool)
    (mzero_covb : Int → Int → T2)
    (h1 : (existsb (mzero_covb lo n) l) = true)
    (h2 : (0 ≤ i ∧ i < n)) :
    (a' + ((lo + i) - a')) = (lo + i) := by
  lia

-- simdjson/fuzz_parser: lib/BothW/AFake_arep4m.v (replace)
example
    {T1 : Type}
    (al_fake : T1 → Int)
    (L : T1)
    (h_1 : Int)
    (pos0 : Int)
    (flag0 : Int)
    (fk_flag : T1 → Int → Int → Int)
    (fk_frame : T1 → Int → Int → Int)
    (pos1 : Int)
    (flag : Int)
    (pos : Int)
    (F : Int)
    (fflag : T1 → Int → Int → Int)
    (shad : Int → Int)
    (shlen : Int → Int)
    (Z_land : Int → Int → Int)
    (pos' : Int)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ pos0 ∧ pos0 < 1024))
    (h3 : flag0 = (fk_flag L 4 pos0))
    (h4 : (0 ≤ pos1 ∧ pos1 < 1024))
    (h5 : pos0 ≠ pos1)
    (h6 : flag = (fk_flag L 4 pos))
    (h7 : F = (fk_frame L 4 pos))
    (h8 : (fflag L 4 F) = flag)
    (h9 : (shad F) = (2147450880 + (F / 8)))
    (h10 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h11 : ((((shad (al_fake L)) + 528896) + (128 * pos)) = (shad F) ∧ (((shad F) + 128) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 128) ≤ 17594333495296)))
    (h12 : (((shad F) + 128) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h13 : flag = (((al_fake L) + 34816) + pos))
    (h14 : F = (((al_fake L) + 4231168) + (pos * 1024)))
    (h15 : flag0 = (((al_fake L) + 34816) + pos0))
    (h16 : pos0 = (Z_land h_1 1023))
    (h17 : (F % 1024) = 0)
    (h18 : pos' = pos) :
    ((al_fake L) + 8) = ((al_fake L) + ((8 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_parser: lib/BothW/AFake_arep4m.v (replace)
example
    {T1 : Type}
    (al_fake : T1 → Int)
    (L : T1)
    (h_1 : Int)
    (pos0 : Int)
    (flag0 : Int)
    (fk_flag : T1 → Int → Int → Int)
    (fk_frame : T1 → Int → Int → Int)
    (pos1 : Int)
    (flag : Int)
    (pos : Int)
    (F : Int)
    (fflag : T1 → Int → Int → Int)
    (shad : Int → Int)
    (shlen : Int → Int)
    (Z_land : Int → Int → Int)
    (pos' : Int)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ pos0 ∧ pos0 < 1024))
    (h3 : flag0 = (fk_flag L 4 pos0))
    (h4 : (0 ≤ pos1 ∧ pos1 < 1024))
    (h5 : pos0 ≠ pos1)
    (h6 : flag = (fk_flag L 4 pos))
    (h7 : F = (fk_frame L 4 pos))
    (h8 : (fflag L 4 F) = flag)
    (h9 : (shad F) = (2147450880 + (F / 8)))
    (h10 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h11 : ((((shad (al_fake L)) + 528896) + (128 * pos)) = (shad F) ∧ (((shad F) + 128) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 128) ≤ 17594333495296)))
    (h12 : (((shad F) + 128) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h13 : flag = (((al_fake L) + 34816) + pos))
    (h14 : F = (((al_fake L) + 4231168) + (pos * 1024)))
    (h15 : flag0 = (((al_fake L) + 34816) + pos0))
    (h16 : pos0 = (Z_land h_1 1023))
    (h17 : (F % 1024) = 0)
    (h18 : pos' = pos) :
    ((al_fake L) + 24) = (((al_fake L) + ((8 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_parser: lib/BothW/AFake_arep5m.v (replace)
example
    {T1 : Type}
    (F : Int)
    (al_fake : T1 → Int)
    (L : T1)
    (h_1 : Int)
    (pos0 : Int)
    (flag0 : Int)
    (fk_flag : T1 → Int → Int → Int)
    (fk_frame : T1 → Int → Int → Int)
    (pos1 : Int)
    (flag : Int)
    (pos : Int)
    (fflag : T1 → Int → Int → Int)
    (shad : Int → Int)
    (shlen : Int → Int)
    (Z_land : Int → Int → Int)
    (a' : Int)
    (h1 : (0 ≤ h_1 ∧ h_1 < (2 ^ (64 : Nat))))
    (h2 : (0 ≤ pos0 ∧ pos0 < 512))
    (h3 : flag0 = (fk_flag L 5 pos0))
    (h4 : (0 ≤ pos1 ∧ pos1 < 512))
    (h5 : pos0 ≠ pos1)
    (h6 : flag = (fk_flag L 5 pos))
    (h7 : F = (fk_frame L 5 pos))
    (h8 : (fflag L 5 F) = flag)
    (h9 : (shad F) = (2147450880 + (F / 8)))
    (h10 : ((shad (al_fake L)) = (2147450880 + ((al_fake L) / 8)) ∧ (shlen 11571200) = 1446400))
    (h11 : ((((shad (al_fake L)) + 659968) + (256 * pos)) = (shad F) ∧ (((shad F) + 256) ≤ ((shad (al_fake L)) + 1446400) ∧ ((shad F) + 256) ≤ 17594333495296)))
    (h12 : (((shad F) + 256) ≤ (al_fake L) ∨ ((al_fake L) + 11571200) ≤ (shad F)))
    (h13 : flag = (((al_fake L) + 35840) + pos))
    (h14 : F = (((al_fake L) + 5279744) + (pos * 2048)))
    (h15 : flag0 = (((al_fake L) + 35840) + pos0))
    (h16 : pos0 = (Z_land h_1 511))
    (h17 : (F % 2048) = 0)
    (h18 : (shad a') = (2147450880 + (a' / 8))) :
    (F + 24) = ((F + ((8 : Nat) : Int)) + ((16 : Nat) : Int)) := by
  lia

-- simdjson/fuzz_parser: lib/BothW/F_adepot.v (replace)
example
    {alayout word list_Z : Type}
    (L : alayout)
    (sp : word)
    (lo : Int)
    (T : Int)
    (sz : Int)
    (tr : list_Z)
    (length : list_Z → Nat)
    (ATOP : Int)
    (bv_unsigned : word → Int)
    (AIMG_HI : Int)
    (al_nodes : alayout → Int)
    (al_store : alayout → Int)
    (h1 : ATOP ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 1024))
    (h3 : sz = (1 + (((length tr) : Nat) : Int)))
    (h4 : sz ≤ 255)
    (h5 : (bv_unsigned sp) ≤ T)
    (h6 : (T + 2040) ≤ (2 ^ (47 : Nat)))
    (h7 : AIMG_HI ≤ (al_nodes L))
    (h8 : ((al_nodes L) + 1048576) ≤ ATOP)
    (h9 : AIMG_HI ≤ (al_store L))
    (h10 : ((al_store L) + 8388608) ≤ ATOP)
    (h11 : 0 ≤ lo)
    (h12 : (1 ≤ sz ∧ sz ≤ 255)) :
    ((length tr) + 1) = (Int.toNat sz) := by
  lia

-- simdjson/fuzz_parser: lib/BothW/F_adepot.v (replace)
example
    {alayout word list_Z : Type}
    (L : alayout)
    (sp : word)
    (lo : Int)
    (T : Int)
    (sz : Int)
    (tr : list_Z)
    (FA : Int)
    (ATOP : Int)
    (bv_unsigned : word → Int)
    (length : list_Z → Nat)
    (AIMG_HI : Int)
    (al_nodes : alayout → Int)
    (al_store : alayout → Int)
    (h1 : ATOP ≤ lo)
    (h2 : lo ≤ ((bv_unsigned sp) - 1024))
    (h3 : sz = (1 + (((length tr) : Nat) : Int)))
    (h4 : sz ≤ 255)
    (h5 : (bv_unsigned sp) ≤ T)
    (h6 : (T + 2040) ≤ (2 ^ (47 : Nat)))
    (h7 : AIMG_HI ≤ (al_nodes L))
    (h8 : ((al_nodes L) + 1048576) ≤ ATOP)
    (h9 : AIMG_HI ≤ (al_store L))
    (h10 : ((al_store L) + 8388608) ≤ ATOP)
    (h11 : 0 ≤ lo)
    (h12 : (1 ≤ sz ∧ sz ≤ 255)) :
    FA = ((FA + (8 * (sz + 1))) - (((Int.toNat (8 * (sz + 1))) : Nat) : Int)) := by
  lia

-- simdjson/fuzz_parser: lib/Plain/RF_main_B2.v (replace)
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
    (arg1 : T1)
    (h1 : (zlength (rd_content st1)) = (((length DATA) : Nat) : Int))
    (h2 : ((1 ≤ CNT ∧ CNT ≤ 65536) ∧ CNT ≤ ((rd_cap st1) - (((length DATA) : Nat) : Int))))
    (h3 : LEN = (((length DATA) : Nat) : Int))
    (h4 : 0 ≤ LEN)
    (h5 : (((length arg1) : Nat) : Int) ≤ 131071) :
    (LEN + (((length bs) : Nat) : Int)) = ((((length bs) : Nat) : Int) + LEN) := by
  lia

-- simdjson/fuzz_parser: lib/Seg/SegSR.v (replace)
example
    {env T2 T3 : Type}
    (E : env)
    (a : T2)
    (s : Int)
    (s' : Int)
    (Z_shiftr : Int → Int → Int)
    (bv_unsigned : T3 → Int)
    (edenot : env → T2 → T3)
    (Zpow : Int → Int → Int)
    (h1 : ((Int.fmod s (2 ^ (64 : Nat))) % 64) = s')
    (h2 : (0 ≤ (Z_shiftr (bv_unsigned (edenot E a)) s') ∧ (Z_shiftr (bv_unsigned (edenot E a)) s') ≤ ((Zpow 2 (64 - s')) - 1)))
    (h3 : (Int.fdiv (bv_unsigned (edenot E a)) (Zpow 2 s')) < (Zpow 2 (64 - s'))) :
    64 = (s' + (64 - s')) := by
  lia

-- simdjson/fuzz_parser: lib/Seg/SegSrl.v (replace)
example (s : Int) (A : Int) (c : Int) (Zpow : Int → Int → Int) (q : Int) (h1 : 0 < (Zpow 2 s)) :
    ((A + (Int.fdiv c (Zpow 2 s))) + (q * (2 ^ (64 : Nat)))) = (((0 + A) + (q * (2 ^ (64 : Nat)))) + (Int.fdiv c (Zpow 2 s))) := by
  lia

-- simdjson/fuzz_parser: lib/SegN/ABR_mvBN.v (replace)
example
    (sp : Int)
    (D : Int)
    (D8 : Int)
    (N_1 : Int)
    (N8 : Int)
    (r : Int)
    (h1 : D = (8 * D8))
    (h2 : N_1 = (8 * N8))
    (h3 : 0 ≤ (8 * r)) :
    sp = ((sp - 4096) + 4096) := by
  lia

-- simdjson/fuzz_parser: lib/SegN/I_asan_memmoveC.v (replace)
example (K : Int) :
    (Int.toNat K) = (min ((Int.toNat K) + 1) (Int.toNat K)) := by
  lia

-- simdjson/fuzz_parser: lib/SegN/SWARZ.v (replace)
example
    {T1 : Type}
    (rep : Int → Nat → Int)
    (n : Nat)
    (Zpow : Int → Int → Int)
    (Z_testbit : Int → Int → Bool)
    (A : Int)
    (B : Int)
    (Z_land : T1 → Int → Int)
    (Z_lor : Int → Int → T1)
    (h1 : 0 < (Zpow 2 (8 * ((n : Nat) : Int))))
    (h2 : (Zpow 2 (8 * (((n + 1) : Nat) : Int))) = (256 * (Zpow 2 (8 * ((n : Nat) : Int)))))
    (h3 : ((Z_testbit A 7) = false ∧ (Z_testbit B 7) = false))
    (h4 : (Z_testbit (Z_land (Z_lor A B) (128 + (256 * (rep 128 n)))) 7) = false)
    (h5 : (Z_testbit (128 + (256 * (rep 128 n))) 7) = true) :
    (128 + ((rep 128 n) * (2 ^ (8 : Nat)))) = (128 + (256 * (rep 128 n))) := by
  lia

-- simdjson/fuzz_parser: lib/SegN/SWARZ.v (replace)
example
    {T1 T2 : Type}
    (rep : Int → Nat → Int)
    (n : Nat)
    (Zpow : Int → Int → Int)
    (Z_testbit : Int → Int → Bool)
    (A : Int)
    (B : Int)
    (Z_land : T1 → Int → Int)
    (Z_lor : Int → Int → T1)
    (b : Int)
    (lev : T2 → Int)
    (r : T2)
    (Z_shiftr : Int → Int → Int)
    (h1 : 0 < (Zpow 2 (8 * ((n : Nat) : Int))))
    (h2 : (Zpow 2 (8 * (((n + 1) : Nat) : Int))) = (256 * (Zpow 2 (8 * ((n : Nat) : Int)))))
    (h3 : ((Z_testbit A 7) = false ∧ (Z_testbit B 7) = false))
    (h4 : (Z_testbit (Z_land (Z_lor A B) (128 + (256 * (rep 128 n)))) 7) = false)
    (h5 : (Z_testbit (128 + (256 * (rep 128 n))) 7) = true)
    (h6 : (48 ≤ b ∧ b ≤ 57))
    (h7 : ((((b - 48) + ((lev r) * 256)) - ((rep 48 n) * 256)) % 256) = ((b - 48) % 256))
    (h8 : ((b - 48) % 256) = ((b - 48) + 256))
    (h9 : A = ((b + 70) + (256 * (Int.fmod ((lev r) + (rep 70 n)) (Zpow 2 (8 * ((n : Nat) : Int)))))))
    (h10 : B = ((b - 48) + (256 * (Int.fmod ((lev r) - (rep 48 n)) (Zpow 2 (8 * ((n : Nat) : Int)))))))
    (h11 : (Z_shiftr (Z_land (Z_lor A B) (128 + (256 * (rep 128 n)))) 8) = 0) :
    (128 + ((rep 128 n) * 256)) = (128 + (256 * (rep 128 n))) := by
  lia

-- simdjson/fuzz_parser: lib/SegP2/S2StrVC.v (replace)
example
    {env list_sidecond expr T4 : Type}
    (TD : Int)
    (E : env)
    (l : list_sidecond)
    (B : expr)
    (P : expr)
    (uL : Int)
    (uQ : Int)
    (j : Int)
    (bv_unsigned : T4 → Int)
    (edenot : env → expr → T4)
    (i : Int)
    (hex4_ev : Int → expr → expr → Int → list_sidecond → Bool)
    (h1 : (0 ≤ TD ∧ (TD + 3544) < (2 ^ (64 : Nat))))
    (h2 : (((bv_unsigned (edenot E B)) + uL) + 64) < (2 ^ (64 : Nat)))
    (h3 : uQ < uL)
    (h4 : 0 ≤ j)
    (h5 : ((((bv_unsigned (edenot E B)) + (bv_unsigned (edenot E P))) + j) + 3) < (2 ^ (64 : Nat)))
    (h6 : (hex4_ev TD B P j l) = true) :
    ((((bv_unsigned (edenot E B)) + (bv_unsigned (edenot E P))) + j) + i) = ((bv_unsigned (edenot E B)) + (((bv_unsigned (edenot E P)) + j) + i)) := by
  lia

-- simdjson/fuzz_parser: lib/SegP2/S2WalkLem.v (replace)
example
    {T1 : Type}
    (a : Int)
    (bs : T1)
    (i : Int)
    (w : Nat)
    (length : T1 → Nat)
    (h1 : 0 ≤ a)
    (h2 : 0 ≤ i)
    (h3 : (i + ((w : Nat) : Int)) ≤ (((length bs) : Nat) : Int))
    (h4 : (a + (((length bs) : Nat) : Int)) ≤ (2 ^ (64 : Nat))) :
    0 = ((Int.toNat i) - (min (Int.toNat i) (length bs))) := by
  lia

-- simdjson/fuzz_parser: lib/SegP2/S2WalkVCok.v (replace)
example
    {T1 T2 T3 T4 T5 T6 : Type}
    (j : Int)
    (byte_at : T1 → Int → Int)
    (mdata : T2 → T3 → Int → Int → T1)
    (segs : T2)
    (m : T3)
    (bv_unsigned : T4 → Int)
    (edenot : T5 → T6 → T4)
    (E : T5)
    (B0 : T6)
    (L0 : T6)
    (P0 : T6)
    (KO0 : T6)
    (eaddl : T6 → Int → T6)
    (h1 : (byte_at (mdata segs m (bv_unsigned (edenot E B0)) (bv_unsigned (edenot E L0))) (bv_unsigned (edenot E P0))) = 34)
    (h2 : (bv_unsigned (edenot E KO0)) = (4 * j))
    (h3 : (bv_unsigned (edenot E (eaddl KO0 4))) = ((4 * j) + 4))
    (h4 : (bv_unsigned (edenot E (eaddl P0 1))) = ((bv_unsigned (edenot E P0)) + 1)) :
    ((j + 1) * 4) = ((4 * j) + 4) := by
  lia

-- simdjson/fuzz_parser: lib/SegP2A/PA2_t0e.v (replace)
example
    {list_byte : Type}
    (SP16 : Int)
    (T8 : Int)
    (DOC8 : Int)
    (B8 : Int)
    (LEN : Int)
    (I8 : Int)
    (N_1 : Int)
    (TB8 : Int)
    (CAPT : Int)
    (SB8 : Int)
    (CAPS : Int)
    (OC8 : Int)
    (IA8 : Int)
    (BO : Int)
    (BG : Int)
    (IG : Int)
    (SG : Int)
    (zsp : Int)
    (THIS : Int)
    (DOC : Int)
    (BUF : Int)
    (IDX : Int)
    (TBASE : Int)
    (SBASE : Int)
    (OCB : Int)
    (IAB : Int)
    (lo : Int)
    (jbuf : list_byte)
    (i : Int)
    (ATOPM : Int)
    (length : list_byte → Nat)
    (h1 : zsp = (16 * SP16))
    (h2 : THIS = (8 * T8))
    (h3 : DOC = (8 * DOC8))
    (h4 : BUF = ((8 * B8) + BO))
    (h5 : IDX = (8 * I8))
    (h6 : TBASE = (8 * TB8))
    (h7 : SBASE = (8 * SB8))
    (h8 : OCB = (8 * OC8))
    (h9 : IAB = (8 * IA8))
    (h10 : (1 ≤ LEN ∧ LEN ≤ 1048512))
    (h11 : (1 ≤ N_1 ∧ N_1 ≤ LEN))
    (h12 : ((N_1 + 3) ≤ CAPT ∧ CAPT ≤ 16777216))
    (h13 : ((LEN + 60) ≤ CAPS ∧ CAPS ≤ 16777216))
    (h14 : ((5 * LEN) + 182) ≤ (3 * CAPS))
    (h15 : (140733193388032 ≤ zsp ∧ zsp ≤ (2 ^ (47 : Nat))))
    (h16 : (6705152 ≤ THIS ∧ ((THIS + 96) ≤ ATOPM ∧ ((THIS + 96) + 8608) ≤ zsp)))
    (h17 : (6705152 ≤ DOC ∧ ((DOC + 16) ≤ ATOPM ∧ ((DOC + 16) + 8608) ≤ zsp)))
    (h18 : ((0 ≤ BO ∧ BO ≤ 7) ∧ (6705152 ≤ (BUF - BO) ∧ (((BUF + LEN) + 64) ≤ ATOPM ∧ (((BUF + LEN) + 64) + 8608) ≤ zsp))))
    (h19 : (6705152 ≤ IDX ∧ (((IDX + (4 * N_1)) + 12) ≤ ATOPM ∧ (((IDX + (4 * N_1)) + 12) + 8608) ≤ zsp)))
    (h20 : (6705152 ≤ TBASE ∧ ((TBASE + (8 * CAPT)) ≤ ATOPM ∧ ((TBASE + (8 * CAPT)) + 8608) ≤ zsp)))
    (h21 : (6705152 ≤ SBASE ∧ ((SBASE + CAPS) ≤ ATOPM ∧ ((SBASE + CAPS) + 8608) ≤ zsp)))
    (h22 : (6705152 ≤ OCB ∧ ((OCB + 8192) ≤ ATOPM ∧ ((OCB + 8192) + 8608) ≤ zsp)))
    (h23 : (6705152 ≤ IAB ∧ ((IAB + 1024) ≤ ATOPM ∧ ((IAB + 1024) + 8608) ≤ zsp)))
    (h24 : ((8 ≤ BG ∧ BG ≤ 131080) ∧ (0 ≤ (((LEN + BO) + 64) - (8 * BG)) ∧ (((LEN + BO) + 64) - (8 * BG)) ≤ 7)))
    (h25 : ((2 ≤ IG ∧ IG ≤ 2097152) ∧ (0 ≤ ((8 * IG) - ((4 * N_1) + 12)) ∧ ((8 * IG) - ((4 * N_1) + 12)) ≤ 7)))
    (h26 : ((7 ≤ SG ∧ SG ≤ 2097152) ∧ (0 ≤ (CAPS - (8 * SG)) ∧ (CAPS - (8 * SG)) ≤ 7)))
    (h27 : (IDX + (8 * IG)) ≤ ATOPM)
    (h28 : (((length jbuf) : Nat) : Int) = (LEN + 64))
    (h29 : (6705152 ≤ lo ∧ lo ≤ (zsp - 8608))) :
    (LEN + i) = ((((((8 * B8) + BO) + LEN) + 0) - BUF) + i) := by
  lia

-- simdjson/fuzz_parser: lib/SegP2U/PU2_xnew.v (replace)
example
    {word list_Z T3 : Type}
    (sp : word)
    (lo : Int)
    (B : Int)
    (d : list_Z)
    (idx : list_Z)
    (ACP : Int)
    (DOC : Int)
    (BUF : Int)
    (nsi : Int)
    (ncp : Int)
    (ntp : Int)
    (nsb : Int)
    (bv_unsigned : word → Int)
    (zlength : list_Z → Int)
    (ATOP : Int)
    (PS2_STACK : Int)
    (s1buf : list_Z → T3)
    (length : T3 → Nat)
    (h1 : ((4 * (zlength idx)) + 12) ≤ nsi)
    (h2 : ACP ≤ BUF)
    (h3 : ((BUF + (zlength d)) + 64) ≤ (ACP + ncp))
    (h4 : (ntp % 8) = 0)
    (h5 : ((8 * ((zlength idx) + 3)) ≤ ntp ∧ ntp ≤ (2 ^ (27 : Nat))))
    (h6 : ((5 * (zlength d)) + 182) ≤ (3 * nsb))
    (h7 : (((zlength d) + 60) ≤ nsb ∧ nsb ≤ (2 ^ (24 : Nat))))
    (h8 : ((zlength d) + 64) ≤ (2 ^ (20 : Nat)))
    (h9 : (bv_unsigned sp) ≤ DOC)
    (h10 : (DOC + 16) ≤ B)
    (h11 : (DOC % 8) = 0)
    (h12 : (bv_unsigned sp) ≤ B)
    (h13 : ATOP ≤ lo)
    (h14 : lo ≤ ((bv_unsigned sp) - PS2_STACK))
    (h15 : ((bv_unsigned sp) % 16) = 0)
    (h16 : (bv_unsigned sp) ≤ (2 ^ (47 : Nat)))
    (h17 : B ≤ ((2 ^ (64 : Nat)) - 160))
    (h18 : (8 * (ntp / 8)) = ntp)
    (h19 : (((length (s1buf d)) : Nat) : Int) = ((zlength d) + 64)) :
    ((bv_unsigned sp) + (-304)) = ((bv_unsigned sp) - 304) := by
  lia
