import Init.Data.Nat.Basic
import Init.Data.List.Lemmas

/-!
  This file provides examples of use of the commands #discr_tree_key and #discr_tree_simp_key
  and guards against any breakage of the commands.
-/

universe u

open Nat List

/-!
  We can produce `simp` keys for theorems of the form `=`, `↔`, `¬`, and `≠` by supplying the name
  of the declaration.
-/

#check Nat.mul_one
/-- info: @HMul.hMul Nat Nat Nat _ _ 1 -/
#guard_msgs in
#discr_tree_simp_key Nat.mul_one

#check Nat.not_le
/-- info: Not (@LE.le Nat _ _ _) -/
#guard_msgs in
#discr_tree_simp_key Nat.not_le

#check and_not_self
/-- info: And _ (Not _) -/
#guard_msgs in
#discr_tree_simp_key and_not_self

#check Nat.add_one_ne_zero
/-- info: @Eq Nat _ 0 -/
#guard_msgs in
#discr_tree_simp_key Nat.add_one_ne_zero

#check zero_le
#discr_tree_simp_key zero_le

#check succ_eq_add_one
#discr_tree_simp_key succ_eq_add_one

#check Nat.pred_succ
#discr_tree_simp_key Nat.pred_succ

#check get?_nil
#discr_tree_simp_key get?_nil

#check or_cons
#discr_tree_simp_key or_cons

#check not_mem_nil
#discr_tree_simp_key not_mem_nil

#check mem_cons
#discr_tree_simp_key mem_cons

#check singleton_append
#discr_tree_simp_key singleton_append

#check append_nil
#discr_tree_simp_key append_eq_nil

#check mapM_nil
#discr_tree_simp_key mapM_nil

/-!
  We can produce keys for a general declarations by name using the default configuration
  for generating keys.
-/

#check Nat.instIdempotentOpGcd
#discr_tree_key Nat.instIdempotentOpGcd

#check List.instDecidableMemOfLawfulBEq
#discr_tree_key List.instDecidableMemOfLawfulBEq

#check List.instForIn'InferInstanceMembership
#discr_tree_key List.instForIn'InferInstanceMembership

/-!
  We can also specify a term directly.
-/
def bar (_ _ : Nat) : Nat := default

#discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n) = default)

#discr_tree_simp_key (∀ {a n : Nat}, bar a (no_index (OfNat.ofNat n)) = default)

#discr_tree_simp_key (∀ m : Nat, ∃ n : Nat, m ≠ n)

#discr_tree_simp_key (∀ m : Nat, m > 0 → m ≠ 0)
