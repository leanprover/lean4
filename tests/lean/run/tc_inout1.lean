universe variables u v

/-
Type class parameter can be annotated with out_param.

Given (C a_1 ... a_n), we replace a_i with a temporary metavariable ?m_i IF
1- a_i is an out_param and it contains metavariables.
3- a_i depends on a_j for j < i, and a_j was replaced with a temporary metavariable ?m_j.
   This case is needed to make sure the new C-application is type correct.

Then, we execute type class resolution as usual.
If it succeeds, and metavariables ?m_i have been assigned, we solve the unification
constraints ?m_i =?= a_i. If we succeed, we return the result. Otherwise, we fail.

We also fail if ?m_i is not assigned.

Remark: we do not cache results when temporary metavariables ?m_i are used.
-/

class is_monoid (α : Type) (op : inout α → α → α) (e : inout α) :=
(op_assoc      : associative op)
(left_neutral  : ∀ a : α, op e a = a)
(right_neutral : ∀ a : α, op a e = a)

lemma assoc {α : Type} {op : α → α → α} {e : α} [is_monoid α op e] : ∀ a b c : α, op (op a b) c = op a (op b c) :=
@is_monoid.op_assoc α op e _

instance nat_add_monoid : is_monoid nat nat.add 0 := sorry
instance nat_mul_monoid : is_monoid nat nat.mul 1 := sorry
instance int_mul_monoid : is_monoid int int.mul 1 := sorry

open tactic

run_cmd do
  M ← to_expr ``(is_monoid nat),
  m₁ ← mk_mvar,
  m₂ ← mk_mvar,
  i ← mk_instance (M m₁ m₂),
  /- found nat_mul_monoid -/
  trace i,
  instantiate_mvars (M m₁ m₂) >>= trace


run_cmd do
  M ← to_expr ``(is_monoid nat nat.add),
  m₁ ← mk_mvar,
  i ← mk_instance (M m₁),
  /- found nat_add_monoid -/
  trace i,
  instantiate_mvars (M m₁) >>= trace


section
local infix + := nat.add

example (a b c : nat) : (a + b) + c = a + (b + c) :=
assoc a b c
end

section
class has_mem2 (α : inout Type u) (γ : Type v) :=
(mem : α → γ → Prop)

def mem2 {α : Type u} {γ : Type v} [has_mem2 α γ] : α → γ → Prop :=
has_mem2.mem

local infix ∈ := mem2

instance (α : Type u) : has_mem2 α (list α) :=
⟨list.mem⟩

#check λ a (s : list nat), a ∈ s

set_option pp.notation false
#check ∀ a ∈ [1, 2, 3], a > 0
end
