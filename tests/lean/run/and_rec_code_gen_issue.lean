import data.buffer

structure hoare_state (σ : Type) (α : Type) :=
(pre    : σ → Prop)
(post   : σ → α → σ → Prop)
(action : ∀ s : {s // pre s}, {as' : α × σ // post s.val as'.1 as'.2})

namespace hoare_state

protected def return (σ : Type) {α : Type} (a : α) : hoare_state σ α :=
{pre    := λ s, true,
 post   := λ s a' s', s' = s ∧ a' = a,
 action := λ ⟨s, h⟩, ⟨(a, s), by simp⟩}

protected def bind {σ α β : Type} (m₁ : hoare_state σ α) (m₂ : α → hoare_state σ β) : hoare_state σ β :=
{pre    := λ s₁, m₁.pre s₁ ∧ ∀ a s₂, m₁.post s₁ a s₂ → (m₂ a).pre s₂,
 post   := λ s₁ b s₃, ∃ a s₂, m₁.post s₁ a s₂ ∧ (m₂ a).post s₂ b s₃,
 action := λ ⟨s₁, h₁, h₂⟩,
           match m₁.action ⟨s₁, h₁⟩ with
           | ⟨(a, s₂), h₃⟩ :=
              match (m₂ a).action ⟨s₂, h₂ a s₂ h₃⟩ with
              | ⟨(b, s₃), s₄⟩ := ⟨(b, s₃), ⟨a, s₂, h₃, s₄⟩⟩
              end
           end
}

protected def assert {σ : Type} (p : σ → Prop) : hoare_state σ unit :=
{pre    := λ s, p s,
 post   := λ s _ s', s' = s ∧ p s',
 action := λ ⟨s, h⟩, ⟨((), s), ⟨rfl, h⟩⟩}

protected def write {σ : Type} (new_s : σ) : hoare_state σ unit :=
{pre    := λ s, true,
 post   := λ s _ s', s' = new_s,
 action := λ ⟨s, h⟩, ⟨((), new_s), rfl⟩}

protected def read {σ : Type} : hoare_state σ σ :=
{pre    := λ s, true,
 post   := λ s a s', s' = s ∧ a = s,
 action := λ ⟨s, h⟩, ⟨(s, s), by simp⟩}

protected def assign {α : Type} (p : nat) (v : α) : hoare_state (buffer α) unit :=
{pre    := λ s, p < s.size,
 post   := λ s _ s', ∀ h : p < s.size, s' = s.write ⟨p, h⟩ v,
 action := λ ⟨s, h⟩, ⟨((), s.write ⟨p, h⟩ v), by intros; simp⟩}

local infix ` ::= `:60 := hoare_state.assign

instance (σ : Type) : has_bind (hoare_state σ) :=
⟨@hoare_state.bind σ⟩

protected def run {σ α : Type} (a : hoare_state σ α) (s : σ) (h : a.pre s) : {as' : α × σ // a.post s as'.1 as'.2} :=
a.action ⟨s, h⟩

def test : hoare_state (buffer nat) unit :=
do 0  ::= 1,
   10 ::= 2,
   2  ::= 4

lemma size_write (b : buffer nat) (i : nat) (h : i < b.size) (v : nat) : (b.write ⟨i, h⟩ v).size = b.size :=
begin
  cases b,
  unfold buffer.write buffer.size,
  simp
end

open nat

def init_mem : nat → hoare_state (buffer nat) unit
| 0        := 0 ::= 0
| (succ p) := succ p ::= 0 >> init_mem p

lemma init_mem_inv : ∀ n (b : buffer nat), n < b.size → (init_mem n).pre b
| 0 b h            := h
| (nat.succ n) b h :=
  have n < b.size, from nat.lt_of_succ_lt h,
  begin
    unfold init_mem has_bind.and_then bind has_bind.bind hoare_state.bind, simp,
    split,
    {unfold hoare_state.assign, simp, exact h},
    {intros _ _,
     unfold hoare_state.assign, simp,
     intro h₁, rewrite h₁ h,
     apply init_mem_inv n,
     rewrite size_write,
     assumption}
  end

def run_init_mem (n : nat) (b : buffer nat) (h : n < b.size) : buffer nat :=
(hoare_state.run (init_mem n) b (init_mem_inv n b h)).1.2

#eval run_init_mem 10 [0,1,2,3,4,5,6,7,8,9,10,11,12,13].to_buffer dec_trivial

end hoare_state
