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

/-- info: Nat.mul_one (n : Nat) : n * 1 = n -/
#guard_msgs in
#check Nat.mul_one

/-- info: @HMul.hMul Nat Nat Nat _ _ 1 -/
#guard_msgs in
#discr_tree_simp_key Nat.mul_one

/-- info: Nat.not_le {a b : Nat} : ¬a ≤ b ↔ b < a -/
#guard_msgs in
#check Nat.not_le

/-- info: Not (@LE.le Nat _ _ _) -/
#guard_msgs in
#discr_tree_simp_key Nat.not_le

/-- info: and_not_self {a : Prop} : ¬(a ∧ ¬a) -/
#guard_msgs in
#check and_not_self

/-- info: And _ (Not _) -/
#guard_msgs in
#discr_tree_simp_key and_not_self

/-- info: Nat.add_one_ne_zero (n : Nat) : n + 1 ≠ 0 -/
#guard_msgs in
#check Nat.add_one_ne_zero

/-- info: @Eq Nat _ 0 -/
#guard_msgs in
#discr_tree_simp_key Nat.add_one_ne_zero

/-- info: Nat.zero_le (n : Nat) : 0 ≤ n -/
#guard_msgs in
#check zero_le

/-- info: @LE.le Nat _ 0 _ -/
#guard_msgs in
#discr_tree_simp_key zero_le

/-- info: Nat.succ_eq_add_one (n : Nat) : n.succ = n + 1 -/
#guard_msgs in
#check succ_eq_add_one

/-- info: succ _ -/
#guard_msgs in
#discr_tree_simp_key succ_eq_add_one

/-- info: Nat.pred_succ (n : Nat) : n.succ.pred = n -/
#guard_msgs in
#check Nat.pred_succ

/-- info: pred _ -/
#guard_msgs in
#discr_tree_simp_key Nat.pred_succ

/-- info: List.getElem?_nil.{u_1} {α : Type u_1} {i : Nat} : [][i]? = none -/
#guard_msgs in
#check getElem?_nil

/-- info: @getElem? (List _) Nat _ _ _ (@nil _) _ -/
#guard_msgs in
#discr_tree_simp_key getElem?_nil

/-- info: List.or_cons {a : Bool} {l : List Bool} : (a :: l).or = (a || l.or) -/
#guard_msgs in
#check or_cons

/-- info: List.or (@cons Bool _ _) -/
#guard_msgs in
#discr_tree_simp_key or_cons

/-- info: List.not_mem_nil.{u_1} {α : Type u_1} {a : α} : ¬a ∈ [] -/
#guard_msgs in
#check not_mem_nil

/-- info: @Membership.mem _ (List _) _ (@nil _) _ -/
#guard_msgs in
#discr_tree_simp_key not_mem_nil

/--
info: List.mem_cons.{u_1} {α✝ : Type u_1} {b : α✝} {l : List α✝} {a : α✝} : a ∈ b :: l ↔ a = b ∨ a ∈ l
-/
#guard_msgs in
#check mem_cons

/-- info: @Membership.mem _ (List _) _ (@cons _ _ _) _ -/
#guard_msgs in
#discr_tree_simp_key mem_cons

/-- info: List.singleton_append.{u_1} {α✝ : Type u_1} {x : α✝} {l : List α✝} : [x] ++ l = x :: l -/
#guard_msgs in
#check singleton_append

/-- info: @HAppend.hAppend (List _) (List _) (List _) _ (@cons _ _ (@nil _)) _ -/
#guard_msgs in
#discr_tree_simp_key singleton_append

/-- info: List.append_nil.{u} {α : Type u} (as : List α) : as ++ [] = as -/
#guard_msgs in
#check append_nil

/-- info: @Eq (List _) (@HAppend.hAppend (List _) (List _) (List _) _ _ _) (@nil _) -/
#guard_msgs in
#discr_tree_simp_key append_eq_nil_iff

/--
info: List.mapM_nil.{u_1, u_2, u_3} {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [Monad m] {f : α → m β} :
  mapM f [] = pure []
-/
#guard_msgs in
#check mapM_nil

/-- info: @mapM _ _ _ _ _ (@nil _) -/
#guard_msgs in
#discr_tree_simp_key mapM_nil

/-!
We can produce keys for a general declarations by name using the default configuration
for generating keys.
-/

/-- info: Nat.instIdempotentOpGcd : Std.IdempotentOp gcd -/
#guard_msgs in
#check Nat.instIdempotentOpGcd

/-- info: @Std.IdempotentOp Nat gcd -/
#guard_msgs in
#discr_tree_key Nat.instIdempotentOpGcd

/--
info: List.instDecidableMemOfLawfulBEq.{u} {α : Type u} [BEq α] [LawfulBEq α] (a : α) (as : List α) : Decidable (a ∈ as)
-/
#guard_msgs in
#check List.instDecidableMemOfLawfulBEq

/-- info: Decidable (@Membership.mem _ (List _) _ _ _) -/
#guard_msgs in
#discr_tree_key List.instDecidableMemOfLawfulBEq

/--
info: List.instForIn'InferInstanceMembershipOfMonad.{u_1, u_2, u_3} {m : Type u_1 → Type u_2} {α : Type u_3} [Monad m] :
  ForIn' m (List α) α inferInstance
-/
#guard_msgs in
#check List.instForIn'InferInstanceMembershipOfMonad

/-- info: ForIn' _ (List _) _ (@instMembership _) -/
#guard_msgs in
#discr_tree_key List.instForIn'InferInstanceMembershipOfMonad

/-!
We can also specify a term directly.
-/
def bar (_ _ : Nat) : Nat := default

/-- info: @Eq Nat (bar _ (@OfNat.ofNat Nat _ _)) (@default Nat _) -/
#guard_msgs in
#discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n) = default)

/-- info: bar _ _ -/
#guard_msgs in
#discr_tree_simp_key (∀ {a n : Nat}, bar a (no_index (OfNat.ofNat n)) = default)

/-- info: @Exists Nat <other> -/
#guard_msgs in
#discr_tree_simp_key (∀ m : Nat, ∃ n : Nat, m ≠ n)

/-- info: @Eq Nat _ 0 -/
#guard_msgs in
#discr_tree_simp_key (∀ m : Nat, m > 0 → m ≠ 0)

/-!
Tests for different kinds of patterns
-/

/-!
The `.arrow` pattern: Only the domain is included
-/

/-- info: ∀ (∀ Nat) -/
#guard_msgs in
#discr_tree_simp_key (((a : Nat) → Fin a) → Nat) = _

/-!
The `.proj` pattern
-/

structure MyStruct where
  thing : Nat → Nat → Nat

def foo : MyStruct := { thing := Nat.add }

/-- info: foo.1 3 4 -/
#guard_msgs in
#discr_tree_key foo.thing 3 4

/-!
The `.other` pattern
-/

/-- info: <other> -/
#guard_msgs in
#discr_tree_key fun x => x + 2

/-!
The `.star` pattern
-/

/-- info: _ -/
#guard_msgs in
#discr_tree_key _

/-!
The `.const` pattern
-/

inductive Tree where
  | a | b | c
  | branch (a b c : Tree)

/-- info: Tree.branch Tree.a Tree.b Tree.c -/
#guard_msgs in
#discr_tree_key Tree.branch Tree.a Tree.b Tree.c

/-!
The `.lit` patterns
-/

/-- info: 32 -/
#guard_msgs in
#discr_tree_key nat_lit 32

/-- info: "hello" -/
#guard_msgs in
#discr_tree_key "hello"

-- we can't test the `.fvar` pattern here
