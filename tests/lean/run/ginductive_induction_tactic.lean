mutual inductive {u} foo, bla (α : Type u)
with foo : Type u
| mk₁ : α → bla → foo
with bla : Type u
| mk₂ : α → bla → bla
| mk₃ : list foo → bla

def cidx {α} : bla α → nat
| (bla.mk₂ _ _) := 1
| (bla.mk₃ _) := 2

def to_list {α} : bla α → list (foo α)
| (bla.mk₂ _ _)  := []
| (bla.mk₃ ls) := ls

lemma ex {α} (b : bla α) (h : cidx b = 2) : b = bla.mk₃ (to_list b) :=
begin
  induction b,
  {simp [cidx] at h, exact absurd h (dec_trivial)},
  {simp [to_list]}
end
