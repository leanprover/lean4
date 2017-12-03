/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.logic init.algebra.classes init.meta init.meta.decl_cmds init.meta.smt.rsimp

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

universe u
variables {α : Type u}

class semigroup (α : Type u) extends has_mul α :=
(mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))

class comm_semigroup (α : Type u) extends semigroup α :=
(mul_comm : ∀ a b : α, a * b = b * a)

class left_cancel_semigroup (α : Type u) extends semigroup α :=
(mul_left_cancel : ∀ a b c : α, a * b = a * c → b = c)

class right_cancel_semigroup (α : Type u) extends semigroup α :=
(mul_right_cancel : ∀ a b c : α, a * b = c * b → a = c)

class monoid (α : Type u) extends semigroup α, has_one α :=
(one_mul : ∀ a : α, 1 * a = a) (mul_one : ∀ a : α, a * 1 = a)

class comm_monoid (α : Type u) extends monoid α, comm_semigroup α

class group (α : Type u) extends monoid α, has_inv α :=
(mul_left_inv : ∀ a : α, a⁻¹ * a = 1)

class comm_group (α : Type u) extends group α, comm_monoid α

lemma mul_assoc [semigroup α] : ∀ a b c : α, a * b * c = a * (b * c) :=
semigroup.mul_assoc

instance semigroup_to_is_associative [semigroup α] : is_associative α (*) :=
⟨mul_assoc⟩

lemma mul_comm [comm_semigroup α] : ∀ a b : α, a * b = b * a :=
comm_semigroup.mul_comm

instance comm_semigroup_to_is_commutative [comm_semigroup α] : is_commutative α (*) :=
⟨mul_comm⟩

lemma mul_left_comm [comm_semigroup α] : ∀ a b c : α, a * (b * c) = b * (a * c) :=
left_comm has_mul.mul mul_comm mul_assoc

local attribute [simp] mul_comm mul_assoc mul_left_comm

lemma mul_right_comm [comm_semigroup α] : ∀ a b c : α, a * b * c = a * c * b :=
right_comm has_mul.mul mul_comm mul_assoc

lemma mul_left_cancel [left_cancel_semigroup α] {a b c : α} : a * b = a * c → b = c :=
left_cancel_semigroup.mul_left_cancel a b c

lemma mul_right_cancel [right_cancel_semigroup α] {a b c : α} : a * b = c * b → a = c :=
right_cancel_semigroup.mul_right_cancel a b c

lemma mul_left_cancel_iff [left_cancel_semigroup α] {a b c : α} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

lemma mul_right_cancel_iff [right_cancel_semigroup α] {a b c : α} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

@[simp] lemma one_mul [monoid α] : ∀ a : α, 1 * a = a :=
monoid.one_mul

@[simp] lemma mul_one [monoid α] : ∀ a : α, a * 1 = a :=
monoid.mul_one

@[simp] lemma mul_left_inv [group α] : ∀ a : α, a⁻¹ * a = 1 :=
group.mul_left_inv

def inv_mul_self := @mul_left_inv

@[simp] lemma inv_mul_cancel_left [group α] (a b : α) : a⁻¹ * (a * b) = b :=
by rw [← mul_assoc, mul_left_inv, one_mul]

@[simp] lemma inv_mul_cancel_right [group α] (a b : α) : a * b⁻¹ * b = a :=
by simp

@[simp] lemma inv_eq_of_mul_eq_one [group α] {a b : α} (h : a * b = 1) : a⁻¹ = b :=
by rw [← mul_one a⁻¹, ←h, ←mul_assoc, mul_left_inv, one_mul]

@[simp] lemma one_inv [group α] : 1⁻¹ = (1 : α) :=
inv_eq_of_mul_eq_one (one_mul 1)

@[simp] lemma inv_inv [group α] (a : α) : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

@[simp] lemma mul_right_inv [group α] (a : α) : a * a⁻¹ = 1 :=
have a⁻¹⁻¹ * a⁻¹ = 1, by rw mul_left_inv,
by rwa [inv_inv] at this

def mul_inv_self := @mul_right_inv

lemma inv_inj [group α] {a b : α} (h : a⁻¹ = b⁻¹) : a = b :=
have a = a⁻¹⁻¹, by simp,
begin rw this, simp [h] end

lemma group.mul_left_cancel [group α] {a b c : α} (h : a * b = a * c) : b = c :=
have a⁻¹ * (a * b) = b, by simp,
begin simp [h] at this, rw this end

lemma group.mul_right_cancel [group α] {a b c : α} (h : a * b = c * b) : a = c :=
have a * b * b⁻¹ = a, by simp,
begin simp [h] at this, rw this end

instance group.to_left_cancel_semigroup [s : group α] : left_cancel_semigroup α :=
{ mul_left_cancel := @group.mul_left_cancel α s, ..s }

instance group.to_right_cancel_semigroup [s : group α] : right_cancel_semigroup α :=
{ mul_right_cancel := @group.mul_right_cancel α s, ..s }

lemma mul_inv_cancel_left [group α] (a b : α) : a * (a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_right_inv, one_mul]

lemma mul_inv_cancel_right [group α] (a b : α) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_right_inv, mul_one]

@[simp] lemma mul_inv_rev [group α] (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
inv_eq_of_mul_eq_one begin rw [mul_assoc, ← mul_assoc b, mul_right_inv, one_mul, mul_right_inv] end

lemma eq_inv_of_eq_inv [group α] {a b : α} (h : a = b⁻¹) : b = a⁻¹ :=
by simp [h]

lemma eq_inv_of_mul_eq_one [group α] {a b : α} (h : a * b = 1) : a = b⁻¹ :=
have a⁻¹ = b, from inv_eq_of_mul_eq_one h,
by simp [this.symm]

lemma eq_mul_inv_of_mul_eq [group α] {a b c : α} (h : a * c = b) : a = b * c⁻¹ :=
by simp [h.symm]

lemma eq_inv_mul_of_mul_eq [group α] {a b c : α} (h : b * a = c) : a = b⁻¹ * c :=
by simp [h.symm]

lemma inv_mul_eq_of_eq_mul [group α] {a b c : α} (h : b = a * c) : a⁻¹ * b = c :=
by simp [h]

lemma mul_inv_eq_of_eq_mul [group α] {a b c : α} (h : a = c * b) : a * b⁻¹ = c :=
by simp [h]

lemma eq_mul_of_mul_inv_eq [group α] {a b c : α} (h : a * c⁻¹ = b) : a = b * c :=
by simp [h.symm]

lemma eq_mul_of_inv_mul_eq [group α] {a b c : α} (h : b⁻¹ * a = c) : a = b * c :=
by simp [h.symm, mul_inv_cancel_left]

lemma mul_eq_of_eq_inv_mul [group α] {a b c : α} (h : b = a⁻¹ * c) : a * b = c :=
by rw [h, mul_inv_cancel_left]

lemma mul_eq_of_eq_mul_inv [group α] {a b c : α} (h : a = c * b⁻¹) : a * b = c :=
by simp [h]

lemma mul_inv [comm_group α] (a b : α) : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
by rw [mul_inv_rev, mul_comm]

/- αdditive "sister" structures.
   Example, add_semigroup mirrors semigroup.
   These structures exist just to help automation.
   In an alternative design, we could have the binary operation as an
   extra argument for semigroup, monoid, group, etc. However, the lemmas
   would be hard to index since they would not contain any constant.
   For example, mul_assoc would be

   lemma mul_assoc {α : Type u} {op : α → α → α} [semigroup α op] :
                   ∀ a b c : α, op (op a b) c = op a (op b c) :=
    semigroup.mul_assoc

   The simplifier cannot effectively use this lemma since the pattern for
   the left-hand-side would be

        ?op (?op ?a ?b) ?c

   Remark: we use a tactic for transporting theorems from the multiplicative fragment
   to the additive one.
-/

class add_semigroup (α : Type u) extends has_add α :=
(add_assoc : ∀ a b c : α, a + b + c = a + (b + c))

class add_comm_semigroup (α : Type u) extends add_semigroup α :=
(add_comm : ∀ a b : α, a + b = b + a)

class add_left_cancel_semigroup (α : Type u) extends add_semigroup α :=
(add_left_cancel : ∀ a b c : α, a + b = a + c → b = c)

class add_right_cancel_semigroup (α : Type u) extends add_semigroup α :=
(add_right_cancel : ∀ a b c : α, a + b = c + b → a = c)

class add_monoid (α : Type u) extends add_semigroup α, has_zero α :=
(zero_add : ∀ a : α, 0 + a = a) (add_zero : ∀ a : α, a + 0 = a)

class add_comm_monoid (α : Type u) extends add_monoid α, add_comm_semigroup α

class add_group (α : Type u) extends add_monoid α, has_neg α :=
(add_left_neg : ∀ a : α, -a + a = 0)

class add_comm_group (α : Type u) extends add_group α, add_comm_monoid α

open tactic

meta def transport_with_dict (dict : name_map name) (src : name) (tgt : name) : command :=
copy_decl_using dict src tgt
>> copy_attribute `reducible src tt tgt
>> copy_attribute `simp src tt tgt
>> copy_attribute `instance src tt tgt

/- Transport multiplicative to additive -/
meta def transport_multiplicative_to_additive (ls : list (name × name)) : command :=
let dict := native.rb_map.of_list ls in
ls.foldl (λ t ⟨src, tgt⟩, do
  env ← get_env,
  if (env.get tgt).to_bool = ff
  then t >> transport_with_dict dict src tgt
  else t)
skip

run_cmd transport_multiplicative_to_additive
  [/- map operations -/
   (`has_mul.mul, `has_add.add), (`has_one.one, `has_zero.zero), (`has_inv.inv, `has_neg.neg),
   (`has_mul, `has_add), (`has_one, `has_zero), (`has_inv, `has_neg),
   /- map constructors -/
   (`has_mul.mk, `has_add.mk), (`has_one, `has_zero.mk), (`has_inv, `has_neg.mk),
   /- map structures -/
   (`semigroup, `add_semigroup),
   (`monoid, `add_monoid),
   (`group, `add_group),
   (`comm_semigroup, `add_comm_semigroup),
   (`comm_monoid, `add_comm_monoid),
   (`comm_group, `add_comm_group),
   (`left_cancel_semigroup, `add_left_cancel_semigroup),
   (`right_cancel_semigroup, `add_right_cancel_semigroup),
   (`left_cancel_semigroup.mk, `add_left_cancel_semigroup.mk),
   (`right_cancel_semigroup.mk, `add_right_cancel_semigroup.mk),
   /- map instances -/
   (`semigroup.to_has_mul, `add_semigroup.to_has_add),
   (`monoid.to_has_one, `add_monoid.to_has_zero),
   (`group.to_has_inv, `add_group.to_has_neg),
   (`comm_semigroup.to_semigroup, `add_comm_semigroup.to_add_semigroup),
   (`monoid.to_semigroup, `add_monoid.to_add_semigroup),
   (`comm_monoid.to_monoid, `add_comm_monoid.to_add_monoid),
   (`comm_monoid.to_comm_semigroup, `add_comm_monoid.to_add_comm_semigroup),
   (`group.to_monoid, `add_group.to_add_monoid),
   (`comm_group.to_group, `add_comm_group.to_add_group),
   (`comm_group.to_comm_monoid, `add_comm_group.to_add_comm_monoid),
   (`left_cancel_semigroup.to_semigroup, `add_left_cancel_semigroup.to_add_semigroup),
   (`right_cancel_semigroup.to_semigroup, `add_right_cancel_semigroup.to_add_semigroup),
   /- map projections -/
   (`semigroup.mul_assoc, `add_semigroup.add_assoc),
   (`comm_semigroup.mul_comm, `add_comm_semigroup.add_comm),
   (`left_cancel_semigroup.mul_left_cancel, `add_left_cancel_semigroup.add_left_cancel),
   (`right_cancel_semigroup.mul_right_cancel, `add_right_cancel_semigroup.add_right_cancel),
   (`monoid.one_mul, `add_monoid.zero_add),
   (`monoid.mul_one, `add_monoid.add_zero),
   (`group.mul_left_inv, `add_group.add_left_neg),
   (`group.mul, `add_group.add),
   (`group.mul_assoc, `add_group.add_assoc),
   /- map lemmas -/
   (`mul_assoc, `add_assoc),
   (`mul_comm, `add_comm),
   (`mul_left_comm, `add_left_comm),
   (`mul_right_comm, `add_right_comm),
   (`one_mul, `zero_add),
   (`mul_one, `add_zero),
   (`mul_left_inv, `add_left_neg),
   (`mul_left_cancel, `add_left_cancel),
   (`mul_right_cancel, `add_right_cancel),
   (`mul_left_cancel_iff, `add_left_cancel_iff),
   (`mul_right_cancel_iff, `add_right_cancel_iff),
   (`inv_mul_cancel_left, `neg_add_cancel_left),
   (`inv_mul_cancel_right, `neg_add_cancel_right),
   (`eq_inv_mul_of_mul_eq, `eq_neg_add_of_add_eq),
   (`inv_eq_of_mul_eq_one, `neg_eq_of_add_eq_zero),
   (`inv_inv, `neg_neg),
   (`mul_right_inv, `add_right_neg),
   (`mul_inv_cancel_left, `add_neg_cancel_left),
   (`mul_inv_cancel_right, `add_neg_cancel_right),
   (`mul_inv_rev, `neg_add_rev),
   (`mul_inv, `neg_add),
   (`inv_inj, `neg_inj),
   (`group.mul_left_cancel, `add_group.add_left_cancel),
   (`group.mul_right_cancel, `add_group.add_right_cancel),
   (`group.to_left_cancel_semigroup, `add_group.to_left_cancel_add_semigroup),
   (`group.to_right_cancel_semigroup, `add_group.to_right_cancel_add_semigroup),
   (`eq_inv_of_eq_inv, `eq_neg_of_eq_neg),
   (`eq_inv_of_mul_eq_one, `eq_neg_of_add_eq_zero),
   (`eq_mul_inv_of_mul_eq, `eq_add_neg_of_add_eq),
   (`inv_mul_eq_of_eq_mul, `neg_add_eq_of_eq_add),
   (`mul_inv_eq_of_eq_mul, `add_neg_eq_of_eq_add),
   (`eq_mul_of_mul_inv_eq, `eq_add_of_add_neg_eq),
   (`eq_mul_of_inv_mul_eq, `eq_add_of_neg_add_eq),
   (`mul_eq_of_eq_inv_mul, `add_eq_of_eq_neg_add),
   (`mul_eq_of_eq_mul_inv, `add_eq_of_eq_add_neg),
   (`one_inv, `neg_zero)
]

instance add_semigroup_to_is_eq_associative [add_semigroup α] : is_associative α (+) :=
⟨add_assoc⟩

instance add_comm_semigroup_to_is_eq_commutative [add_comm_semigroup α] : is_commutative α (+) :=
⟨add_comm⟩

local attribute [simp] add_assoc add_comm add_left_comm

def neg_add_self := @add_left_neg
def add_neg_self := @add_right_neg
def eq_of_add_eq_add_left := @add_left_cancel
def eq_of_add_eq_add_right := @add_right_cancel

@[reducible] protected def algebra.sub [add_group α] (a b : α) : α :=
a + -b

instance add_group_has_sub [add_group α] : has_sub α :=
⟨algebra.sub⟩

@[simp] lemma sub_eq_add_neg [add_group α] (a b : α) : a - b = a + -b :=
rfl

lemma sub_self [add_group α] (a : α) : a - a = 0 :=
add_right_neg a

lemma sub_add_cancel [add_group α] (a b : α) : a - b + b = a :=
neg_add_cancel_right a b

lemma add_sub_cancel [add_group α] (a b : α) : a + b - b = a :=
add_neg_cancel_right a b

lemma add_sub_assoc [add_group α] (a b c : α) : a + b - c = a + (b - c) :=
by rw [sub_eq_add_neg, add_assoc, ←sub_eq_add_neg]

lemma eq_of_sub_eq_zero [add_group α] {a b : α} (h : a - b = 0) : a = b :=
have 0 + b = b, by rw zero_add,
have (a - b) + b = b, by rwa h,
by rwa [sub_eq_add_neg, neg_add_cancel_right] at this

lemma sub_eq_zero_of_eq [add_group α] {a b : α} (h : a = b) : a - b = 0 :=
by rw [h, sub_self]

lemma sub_eq_zero_iff_eq [add_group α] {a b : α} : a - b = 0 ↔ a = b :=
⟨eq_of_sub_eq_zero, sub_eq_zero_of_eq⟩

lemma zero_sub [add_group α] (a : α) : 0 - a = -a :=
zero_add (-a)

lemma sub_zero [add_group α] (a : α) : a - 0 = a :=
by rw [sub_eq_add_neg, neg_zero, add_zero]

lemma sub_ne_zero_of_ne [add_group α] {a b : α} (h : a ≠ b) : a - b ≠ 0 :=
begin
  intro hab,
  apply h,
  apply eq_of_sub_eq_zero hab
end

lemma sub_neg_eq_add [add_group α] (a b : α) : a - (-b) = a + b :=
by rw [sub_eq_add_neg, neg_neg]

lemma neg_sub [add_group α] (a b : α) : -(a - b) = b - a :=
neg_eq_of_add_eq_zero (by rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, neg_add_cancel_left, add_right_neg])

lemma add_sub [add_group α] (a b c : α) : a + (b - c) = a + b - c :=
by simp

lemma sub_add_eq_sub_sub_swap [add_group α] (a b c : α) : a - (b + c) = a - c - b :=
by simp

lemma add_sub_add_right_eq_sub [add_group α] (a b c : α) : (a + c) - (b + c) = a - b :=
by rw [sub_add_eq_sub_sub_swap]; simp

lemma eq_sub_of_add_eq [add_group α] {a b c : α} (h : a + c = b) : a = b - c :=
by simp [h.symm]

lemma sub_eq_of_eq_add [add_group α] {a b c : α} (h : a = c + b) : a - b = c :=
by simp [h]

lemma eq_add_of_sub_eq [add_group α] {a b c : α} (h : a - c = b) : a = b + c :=
by simp [h.symm]

lemma add_eq_of_eq_sub [add_group α] {a b c : α} (h : a = c - b) : a + b = c :=
by simp [h]

lemma sub_add_eq_sub_sub [add_comm_group α] (a b c : α) : a - (b + c) = a - b - c :=
by simp

lemma neg_add_eq_sub [add_comm_group α] (a b : α) : -a + b = b - a :=
by simp

lemma sub_add_eq_add_sub [add_comm_group α] (a b c : α) : a - b + c = a + c - b :=
by simp

lemma sub_sub [add_comm_group α] (a b c : α) : a - b - c = a - (b + c) :=
by simp

lemma sub_add [add_comm_group α] (a b c : α) : a - b + c = a - (b - c) :=
by simp

lemma add_sub_add_left_eq_sub [add_comm_group α] (a b c : α) : (c + a) - (c + b) = a - b :=
by simp

lemma eq_sub_of_add_eq' [add_comm_group α] {a b c : α} (h : c + a = b) : a = b - c :=
by simp [h.symm]

lemma sub_eq_of_eq_add' [add_comm_group α] {a b c : α} (h : a = b + c) : a - b = c :=
begin simp [h], rw [add_left_comm], simp end

lemma eq_add_of_sub_eq' [add_comm_group α] {a b c : α} (h : a - b = c) : a = b + c :=
by simp [h.symm]

lemma add_eq_of_eq_sub' [add_comm_group α] {a b c : α} (h : b = c - a) : a + b = c :=
begin simp [h], rw [add_comm c, add_neg_cancel_left] end

lemma sub_sub_self [add_comm_group α] (a b : α) : a - (a - b) = b :=
begin simp, rw [add_comm b, add_neg_cancel_left] end

lemma add_sub_comm [add_comm_group α] (a b c d : α) : a + b - (c + d) = (a - c) + (b - d) :=
by simp

lemma sub_eq_sub_add_sub [add_comm_group α] (a b c : α) : a - b = c - b + (a - c) :=
begin simp, rw [add_left_comm c], simp end

lemma neg_neg_sub_neg [add_comm_group α] (a b : α) : - (-a - -b) = a - b :=
by simp

/- The following lemmas generate too many instances for rsimp -/
attribute [no_rsimp]
  mul_assoc mul_comm mul_left_comm
  add_assoc add_comm add_left_comm
