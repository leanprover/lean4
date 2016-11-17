/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.binary init.combinator init.meta.interactive init.meta.decl_cmds

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

@[class] def add_semigroup      := semigroup
@[class] def add_monoid         := monoid
@[class] def add_group          := group
@[class] def add_comm_semigroup := comm_semigroup
@[class] def add_comm_monoid    := comm_monoid
@[class] def add_comm_group     := comm_group

instance add_semigroup.to_has_add {α : Type u} [s : add_semigroup α] : has_add α :=
⟨@semigroup.mul α s⟩
instance add_monoid.to_has_zero {α : Type u} [s : add_monoid α] : has_zero α :=
⟨@monoid.one α s⟩
instance add_group.to_has_neg {α : Type u} [s : add_group α] : has_neg α :=
⟨@group.inv α s⟩

meta def multiplicative_to_additive : name_map name :=
rb_map.of_list $
  [/- map operations -/
   (`mul, `add), (`one, `zero), (`inv, `neg),
   /- map structures -/
   (`semigroup, `add_semigroup),
   (`monoid, `add_monoid),
   (`group, `add_group),
   (`comm_semigroup, `add_comm_semigroup),
   (`comm_monoid, `add_comm_monoid),
   (`comm_group, `add_comm_group),
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
   (`comm_group.to_comm_monoid, `add_comm_group.to_add_comm_monoid)
 ]

open tactic

meta def transport_to_additive (src : name) (tgt : name) : command :=
copy_decl_updating_type multiplicative_to_additive src tgt
>> copy_attribute `reducible src tt tgt
>> copy_attribute `simp src tt tgt
>> copy_attribute `instance src tt tgt

/- Make sure all constants at multiplicative_to_additive are declared -/
meta def init_multiplicative_to_additive : command :=
multiplicative_to_additive^.fold skip (λ s t tac, do
  env ← get_env,
  if (env^.get t)^.to_bool = ff
  then tac >> transport_to_additive s t
  else tac)

run_command init_multiplicative_to_additive
run_command transport_to_additive `mul_assoc `add_assoc
run_command transport_to_additive `mul_comm  `add_comm
run_command transport_to_additive `mul_left_comm `add_left_comm
run_command transport_to_additive `one_mul `zero_add
run_command transport_to_additive `mul_one `add_zero
run_command transport_to_additive `mul_left_inv `add_left_neg
