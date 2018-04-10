universe u

inductive list_mem {α : Type u} : α → list α → Prop
| head (a : α) (l : list α)   : list_mem a (a::l)
| tail (a b : α) (l : list α) : list_mem a l → list_mem a (b::l)

lemma mem_self {α} (a : α) (l : list α) : list_mem a (a::l) :=
list_mem.head a l

open tactic

lemma mem_cons_iff {α} (a y : α) (l : list α) : list_mem a (y :: l) ↔ (a = y ∨ list_mem a l) :=
begin
  apply iff.intro,
  {intro h, cases h, {apply or.inl, refl}, {apply or.inr, assumption}},
  {intro h, cases h, {subst_vars, apply list_mem.head}, {apply list_mem.tail, assumption}}
end

lemma list_mem_1 {α} (a : α) : ¬ list_mem a [] :=
by intro h; cases h

def test_list_mem_dcases_on
  {α  : Type u}
  {C  : Π (a : α) (a_1 : list α), list_mem a a_1 → Prop}
  {a  : α} {l : list α}
  (n  : list_mem a l)
  (h₁ : ∀ (a : α) (l : list α), C a (a :: l) (list_mem.head a l))
  (h₂ : ∀ (a b : α) (l : list α) (a_1 : list_mem a l), C a (b :: l) (list_mem.tail a b l a_1)) : C a l n :=
@list_mem.dcases_on α C a l n h₁ h₂
