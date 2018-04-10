universe variables u v

/-
Type class parameter can be annotated with out_param.
Given (C a_1 ... a_n), we replace a_i with a temporary metavariable ?x_i IF
- Case 1
   a_i is an out_param
OR
- Case 2
   a_i depends on a_j for j < i, and a_j was replaced with a temporary metavariable ?x_j.
   This case is needed to make sure the new C-application is type correct.
   It may be counterintuitive to some users.
   @kha and @leodemoura have discussed a different approach
   where a type class declaration is rejected IF
   it contains a regular parameter X that depends on an `out` parameter Y.
   If we reject this kind of declaration, then we don't need
   this extra case which may artificially treat regular parameters
   as `out` (**).
-/

class is_monoid (α : Type) (op : α → α → α) (e : out_param α) :=
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
  M ← to_expr ``(is_monoid nat nat.add),
  m₁ ← mk_mvar,
  i ← mk_instance (M m₁),
  /- found nat_add_monoid -/
  trace i,
  instantiate_mvars (M m₁) >>= trace

run_cmd do
  M ← to_expr ``(is_monoid nat nat.mul),
  m₁ ← mk_mvar,
  i ← mk_instance (M m₁),
  /- found nat_mul_monoid -/
  trace i,
  instantiate_mvars (M m₁) >>= trace


section
local infix + := nat.add

example (a b c : nat) : (a + b) + c = a + (b + c) :=
assoc a b c
end

section
class has_mem2 (α : out_param $ Type u) (γ : Type v) :=
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
