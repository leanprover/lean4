/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.binary init.combinator init.meta.interactive init.meta.decl_cmds

universe variable u

class semigroup (A : Type u) extends has_mul A :=
(mul_assoc : ∀ a b c : A, a * b * c = a * (b * c))

variables {A : Type u}

@[simp] lemma mul_assoc [semigroup A] : ∀ a b c : A, a * b * c = a * (b * c) :=
semigroup.mul_assoc

class comm_semigroup (A : Type u) extends semigroup A :=
(mul_comm : ∀ a b : A, a * b = b * a)

@[simp] lemma mul_comm [comm_semigroup A] : ∀ a b : A, a * b = b * a :=
comm_semigroup.mul_comm

@[simp] lemma mul_left_comm [comm_semigroup A] : ∀ a b c : A, a * (b * c) = b * (a * c) :=
left_comm mul mul_comm mul_assoc

class left_cancel_semigroup (A : Type u) extends semigroup A :=
(mul_left_cancel : ∀ a b c : A, a * b = a * c → b = c)

lemma mul_left_cancel [left_cancel_semigroup A] {a b c : A} : a * b = a * c → b = c :=
left_cancel_semigroup.mul_left_cancel a b c

class right_cancel_semigroup (A : Type u) extends semigroup A :=
(mul_right_cancel : ∀ a b c : A, a * b = c * b → a = c)

lemma mul_right_cancel [right_cancel_semigroup A] {a b c : A} : a * b = c * b → a = c :=
right_cancel_semigroup.mul_right_cancel a b c

class monoid (A : Type u) extends semigroup A, has_one A :=
(one_mul : ∀ a : A, 1 * a = a) (mul_one : ∀ a : A, a * 1 = a)

@[simp] lemma one_mul [monoid A] : ∀ a : A, 1 * a = a :=
monoid.one_mul

@[simp] lemma mul_one [monoid A] : ∀ a : A, a * 1 = a :=
monoid.mul_one

class comm_monoid (A : Type u) extends monoid A, comm_semigroup A

class group (A : Type u) extends monoid A, has_inv A :=
(mul_left_inv : ∀ a : A, a⁻¹ * a = 1)

@[simp] lemma mul_left_inv [group A] : ∀ a : A, a⁻¹ * a = 1 :=
group.mul_left_inv

class comm_group (A : Type u) extends group A, comm_monoid A

/- Additive "sister" structures.
   Example, add_semigroup mirrors semigroup.
   These structures exist just to help automation.
   In an alternative design, we could have the binary operation as an
   extra argument for semigroup, monoid, group, etc. However, the lemmas
   would be hard to index since they would not contain any constant.
   For example, mul_assoc would be

   lemma mul_assoc {A : Type u} {op : A → A → A} [semigroup A op] :
                   ∀ a b c : A, op (op a b) c = op a (op b c) :=
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

instance add_semigroup.to_has_add {A : Type u} [s : add_semigroup A] : has_add A :=
⟨@mul A (@semigroup.to_has_mul A s)⟩
instance add_monoid.to_has_zero {A : Type u} [s : add_monoid A] : has_zero A :=
⟨@one A (@monoid.to_has_one A s)⟩
instance add_group.to_has_neg {A : Type u} [s : add_group A] : has_neg A :=
⟨@inv A (@group.to_has_inv A s)⟩

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

meta def transport_to_additive : name → name → command :=
copy_decl_updating_type multiplicative_to_additive

open tactic

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
