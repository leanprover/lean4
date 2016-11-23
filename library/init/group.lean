/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.logic init.binary init.combinator init.meta.interactive init.meta.decl_cmds
import init.monad_combinators

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

universe variable u
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

@[simp] lemma mul_assoc [semigroup α] : ∀ a b c : α, a * b * c = a * (b * c) :=
semigroup.mul_assoc

@[simp] lemma mul_comm [comm_semigroup α] : ∀ a b : α, a * b = b * a :=
comm_semigroup.mul_comm

@[simp] lemma mul_left_comm [comm_semigroup α] : ∀ a b c : α, a * (b * c) = b * (a * c) :=
left_comm mul mul_comm mul_assoc

lemma mul_left_cancel [left_cancel_semigroup α] {a b c : α} : a * b = a * c → b = c :=
left_cancel_semigroup.mul_left_cancel a b c

lemma mul_right_cancel [right_cancel_semigroup α] {a b c : α} : a * b = c * b → a = c :=
right_cancel_semigroup.mul_right_cancel a b c

@[simp] lemma one_mul [monoid α] : ∀ a : α, 1 * a = a :=
monoid.one_mul

@[simp] lemma mul_one [monoid α] : ∀ a : α, a * 1 = a :=
monoid.mul_one

@[simp] lemma mul_left_inv [group α] : ∀ a : α, a⁻¹ * a = 1 :=
group.mul_left_inv

@[simp] lemma inv_mul_cancel_left [group α] (a b : α) : a⁻¹ * (a * b) = b :=
by rw [-mul_assoc, mul_left_inv, one_mul]

@[simp] lemma inv_mul_cancel_right [group α] (a b : α) : a * b⁻¹ * b = a :=
by simp

@[simp] lemma inv_eq_of_mul_eq_one [group α] {a b : α} (h : a * b = 1) : a⁻¹ = b :=
by rw [-mul_one a⁻¹, -h, -mul_assoc, mul_left_inv, one_mul]

@[simp] lemma one_inv [group α] : 1⁻¹ = (1 : α) :=
inv_eq_of_mul_eq_one (one_mul 1)

@[simp] lemma inv_inv [group α] (a : α) : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

@[simp] lemma mul_right_inv [group α] (a : α) : a * a⁻¹ = 1 :=
have a⁻¹⁻¹ * a⁻¹ = 1, by rw mul_left_inv,
begin rw [inv_inv] at this, assumption end

lemma group.mul_left_cancel [group α] {a b c : α} (h : a * b = a * c) : b = c :=
have a⁻¹ * (a * b) = b, by simp,
begin simp [h] at this, rw this end

lemma group.mul_right_cancel [group α] {a b c : α} (h : a * b = c * b) : a = c :=
have a * b * b⁻¹ = a, by simp,
begin simp [h] at this, rw this end

instance group.to_left_cancel_semigroup [s : group α] : left_cancel_semigroup α :=
{ s with mul_left_cancel := @group.mul_left_cancel α s }

instance group.to_right_cancel_semigroup [s : group α] : right_cancel_semigroup α :=
{ s with mul_right_cancel := @group.mul_right_cancel α s }

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

@[class] def add_semigroup              := semigroup
@[class] def add_monoid                 := monoid
@[class] def add_group                  := group
@[class] def add_comm_semigroup         := comm_semigroup
@[class] def add_comm_monoid            := comm_monoid
@[class] def add_comm_group             := comm_group
@[class] def add_left_cancel_semigroup  := left_cancel_semigroup
@[class] def add_right_cancel_semigroup := right_cancel_semigroup

instance add_semigroup.to_has_add {α : Type u} [s : add_semigroup α] : has_add α :=
⟨@semigroup.mul α s⟩
instance add_monoid.to_has_zero {α : Type u} [s : add_monoid α] : has_zero α :=
⟨@monoid.one α s⟩
instance add_group.to_has_neg {α : Type u} [s : add_group α] : has_neg α :=
⟨@group.inv α s⟩

open tactic

meta def transport_with_dict (dict : name_map name) (src : name) (tgt : name) : command :=
copy_decl_updating_type dict src tgt
>> copy_attribute `reducible src tt tgt
>> copy_attribute `simp src tt tgt
>> copy_attribute `instance src tt tgt

meta def name_map_of_list_name (l : list name) : tactic (name_map name) :=
do list_pair_name ← monad.for l (λ nm, do e ← mk_const nm, eval_expr (list (name × name)) e),
   return $ rb_map.of_list (list.join list_pair_name)

meta def transport_using_attr (attr : caching_user_attribute (name_map name))
    (src : name) (tgt : name) : command :=
do dict ← caching_user_attribute.get_cache attr,
   transport_with_dict dict src tgt

meta def multiplicative_to_additive_transport_attr : caching_user_attribute (name_map name) :=
{ name  := `multiplicative_to_additive_transport,
  descr := "list of name pairs for transporting multiplicative facts to additive ones",
  mk_cache := name_map_of_list_name,
  dependencies := [] }

run_command attribute.register `multiplicative_to_additive_transport_attr

meta def transport_to_additive : name → name → command :=
transport_using_attr multiplicative_to_additive_transport_attr

@[multiplicative_to_additive_transport]
meta def multiplicative_to_additive_pairs : list (name × name) :=
  [/- map operations -/
   (`mul, `add), (`one, `zero), (`inv, `neg),
   /- map structures -/
   (`semigroup, `add_semigroup),
   (`monoid, `add_monoid),
   (`group, `add_group),
   (`comm_semigroup, `add_comm_semigroup),
   (`comm_monoid, `add_comm_monoid),
   (`comm_group, `add_comm_group),
   (`left_cancel_semigroup, `add_left_cancel_semigroup),
   (`right_cancel_semigroup, `add_right_cancel_semigroup),
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
   (`right_cancel_semigroup.to_semigroup, `add_right_cancel_semigroup.to_add_semigroup)
 ]

/- Make sure all constants at multiplicative_to_additive are declared -/
meta def init_multiplicative_to_additive : command :=
list.foldl (λ (tac : tactic unit) (p : name × name), do
  (s, t) ← return p,
  env ← get_env,
  if (env^.get t)^.to_bool = ff
  then tac >> transport_to_additive s t
  else tac) skip multiplicative_to_additive_pairs

run_command init_multiplicative_to_additive
run_command transport_to_additive `mul_assoc `add_assoc
run_command transport_to_additive `mul_comm  `add_comm
run_command transport_to_additive `mul_left_comm `add_left_comm
run_command transport_to_additive `one_mul `zero_add
run_command transport_to_additive `mul_one `add_zero
run_command transport_to_additive `mul_left_inv `add_left_neg
