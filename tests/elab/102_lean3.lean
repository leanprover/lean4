inductive time (D : Type) : Type
| start : time D
| after : (D → time D) → time D

def foo (C D : Type) : time D → (γ : Type) × (γ → C)
| time.start    => ⟨C, id⟩
| time.after ts => ⟨(∀ (i : D), (foo C D $ ts i).1) × D, λ p => (foo C D $ ts p.2).2 $ p.1 p.2⟩

theorem fooEq1 (C D) : foo C D time.start = ⟨C, id⟩ :=
  rfl
theorem fooEq2 (C D) (ts : D → time D): foo C D (time.after ts) = ⟨(∀ (i : D), (foo C D $ ts i).1) × D, λ p => (foo C D $ ts p.2).2 $ p.1 p.2⟩ :=
  rfl
