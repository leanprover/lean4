inductive Lex (ra : α → α → Prop) (rb : β → β → Prop) : α × β → α × β → Prop where
  | left  {a₁} (b₁) {a₂} (b₂) (h : ra a₁ a₂) : Lex ra rb (a₁, b₁) (a₂, b₂)
  | right (a) {b₁ b₂} (h : rb b₁ b₂)         : Lex ra rb (a, b₁)  (a, b₂)


def lexAccessible1 {ra : α → α → Prop} {rb : β → β → Prop} (aca : (a : α) → Acc ra a) (acb : (b : β) → Acc rb b) (a : α) (b : β) : Acc (Lex ra rb) (a, b) := by
  induction (aca a) generalizing b with
  | intro xa aca iha =>
    induction (acb b) with
    | intro xb acb ihb =>
      apply Acc.intro (xa, xb)
      intro p lt
      cases lt with
      | left  b1 b2 h    => apply iha _ h -- only explicit fields are provided by default
      | @right a b1 b2 h => apply ihb b1 h -- `@` allows us to provide names to implicit fields too

def lexAccessible2 {ra : α → α → Prop} {rb : β → β → Prop} (aca : (a : α) → Acc ra a) (acb : (b : β) → Acc rb b) (a : α) (b : β) : Acc (Lex ra rb) (a, b) := by
  induction (aca a) generalizing b with
  | intro xa aca iha =>
    induction (acb b) with
    | intro xb acb ihb =>
      apply Acc.intro (xa, xb)
      intro p lt
      cases lt with
      | @left a1 b1 a2 b2 h => apply iha a1 h
      | right _ h   => apply ihb _ h
