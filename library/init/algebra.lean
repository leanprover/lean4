/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
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

class distrib (α : Type u) extends has_mul α, has_add α :=
(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))

lemma left_distrib [distrib α] (a b c : α) : a * (b + c) = a * b + a * c :=
distrib.left_distrib a b c

lemma right_distrib [distrib α] (a b c : α) : (a + b) * c = a * c + b * c :=
distrib.right_distrib a b c

class mul_zero_class (α : Type u) extends has_mul α, has_zero α :=
(zero_mul : ∀ a : α, 0 * a = 0)
(mul_zero : ∀ a : α, a * 0 = 0)

@[simp] lemma zero_mul [mul_zero_class α] (a : α) : 0 * a = 0 :=
mul_zero_class.zero_mul a

@[simp] lemma mul_zero [mul_zero_class α] (a : α) : a * 0 = 0 :=
mul_zero_class.mul_zero a

class zero_ne_one_class (α : Type u) extends has_zero α, has_one α :=
(zero_ne_one : 0 ≠ (1:α))

lemma zero_ne_one [s: zero_ne_one_class α] : 0 ≠ (1:α) :=
@zero_ne_one_class.zero_ne_one α s

/- semiring -/

structure semiring (α : Type u) extends comm_monoid α renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero mul_comm→add_comm,
  monoid α, distrib α, mul_zero_class α

attribute [class] semiring

instance add_comm_monoid_of_semiring (α : Type u) [s : semiring α] : add_comm_monoid α :=
@semiring.to_comm_monoid α s

instance monoid_of_semiring (α : Type u) [s : semiring α] : monoid α :=
@semiring.to_monoid α s

instance distrib_of_semiring (α : Type u) [s : semiring α] : distrib α :=
@semiring.to_distrib α s

instance mul_zero_class_of_semiring (α : Type u) [s : semiring α] : mul_zero_class α :=
@semiring.to_mul_zero_class α s

class comm_semiring (α : Type u) extends semiring α, comm_monoid α

/- ring -/

structure ring (α : Type u) extends comm_group α renaming mul→add mul_assoc→add_assoc
  one→zero one_mul→zero_add mul_one→add_zero inv→neg mul_left_inv→add_left_inv mul_comm→add_comm,
  monoid α, distrib α

attribute [class] ring

instance to_add_comm_group_of_ring (α : Type u) [s : ring α] : add_comm_group α :=
@ring.to_comm_group α s

instance monoid_of_ring (α : Type u) [s : ring α] : monoid α := @ring.to_monoid α s

instance distrib_of_ring (α : Type u) [s : ring α] : distrib α :=
@ring.to_distrib α s

/- ordered structures -/

structure ordered_mul_cancel_comm_monoid (α : Type u)
      extends comm_monoid α, left_cancel_semigroup α,
              right_cancel_semigroup α, order_pair α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c)
(mul_lt_mul_left       : ∀ a b : α, a < b → ∀ c : α, c * a < c * b)
(lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c)

@[class] def ordered_cancel_comm_monoid : Type u → Type (max 1 u) :=
ordered_mul_cancel_comm_monoid

instance add_comm_monoid_of_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_cancel_comm_monoid α] : add_comm_monoid α :=
@ordered_mul_cancel_comm_monoid.to_comm_monoid α s

instance add_left_cancel_semigroup_of_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_cancel_comm_monoid α] : add_left_cancel_semigroup α :=
@ordered_mul_cancel_comm_monoid.to_left_cancel_semigroup α s

instance add_right_cancel_semigroup_of_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_cancel_comm_monoid α] : add_right_cancel_semigroup α :=
@ordered_mul_cancel_comm_monoid.to_right_cancel_semigroup α s

instance order_pair_of_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_cancel_comm_monoid α] : order_pair α :=
@ordered_mul_cancel_comm_monoid.to_order_pair α s

section
variables [s : ordered_cancel_comm_monoid α]

lemma add_le_add_left {a b : α} (h : a ≤ b) (c : α) : c + a ≤ c + b :=
@ordered_mul_cancel_comm_monoid.mul_le_mul_left α s a b h c

lemma le_of_add_le_add_left {a b c : α} (h : a + b ≤ a + c) : b ≤ c :=
@ordered_mul_cancel_comm_monoid.le_of_mul_le_mul_left α s a b c h

lemma add_lt_add_left {a b : α} (h : a < b) (c : α) : c + a < c + b :=
@ordered_mul_cancel_comm_monoid.mul_lt_mul_left α s a b h c

lemma lt_of_add_lt_add_left {a b c : α} (h : a + b < a + c) : b < c :=
@ordered_mul_cancel_comm_monoid.lt_of_mul_lt_mul_left α s a b c h

end
