def casesTFOn {motive : Prop → Sort _} (P) [inst : Decidable P] : (T : motive True) → (F : motive False) → motive P :=
  λ ht hf => if H : P then eq_true H ▸ ht else eq_false H ▸ hf

example (P) [Decidable P] : ¬¬P → P := by
  induction P using casesTFOn
  admit
  admit
