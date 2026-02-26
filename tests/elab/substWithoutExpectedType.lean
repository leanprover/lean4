inductive Foo: List α → Type _
  | mk (l): Foo l

def Foo.length: Foo l → Nat
  | mk l => l.length

variable {α : Type u} {Γ Γ': List α} {p: Foo Γ} {h: Γ = Γ'}

theorem eq_rec_length : (h ▸ p).length = p.length := by
  cases h; rfl

example : (h ▸ p).length = p.length :=
  eq_rec_length

example : (h ▸ p).length = p.length := by
  simp only [eq_rec_length]

example : (h ▸ p).length = p.length := by
  rw [eq_rec_length]

example : (h ▸ p).length = p.length := by
  subst h; rfl

example : (h ▸ p).length = p.length :=
  match h with
  | rfl => rfl

example : (h ▸ p).length = p.length :=
  let (rfl) := h; rfl
