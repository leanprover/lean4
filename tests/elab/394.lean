def casesTFOn {motive : Prop → Sort _} (P) [inst : Decidable P] : (T : motive True) → (F : motive False) → motive P :=
  λ ht hf => match inst with
  | isTrue H => eq_true H ▸ ht
  | isFalse H => eq_false H ▸ hf

example (P) [Decidable P] : ¬¬P → P := by
  induction P using casesTFOn
  admit
  admit
