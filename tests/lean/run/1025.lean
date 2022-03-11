inductive Vector (α : Type u): Nat → Type u where
| nil : Vector α 0
| cons (head : α) (tail : Vector α n) : Vector α (n+1)

namespace Vector
  def mem (a : α) : Vector α n → Prop
  | nil => False
  | cons b l => a = b ∨ mem a l

  def foldr (f : α → β → β) (init : β) : Vector α n → β
  | nil     => init
  | cons a l => f a (foldr f init l)

  theorem foldr_max [LE β] [LT β] [DecidableRel (· < · : β → β → Prop)] {v: Vector α n} (f : α → β) (init : β)
    (h: v.mem y):
    f y ≤ v.foldr (λ x acc => max (f x) acc) init := by
    induction v <;> simp only[foldr,max]
    . admit
    . split <;> admit
end Vector
