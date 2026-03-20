inductive Vector' (α : Type u): Nat → Type u where
| nil : Vector' α 0
| cons (head : α) (tail : Vector' α n) : Vector' α (n+1)

class Order (α : Type u) extends LE α, LT α, Max α where
  ltDecidable : DecidableRel (@LT.lt α _)
  max_def x y : max x y = if x < y then x else y

namespace Vector'
  def mem (a : α) : Vector' α n → Prop
  | nil => False
  | cons b l => a = b ∨ mem a l

  def foldr (f : α → β → β) (init : β) : Vector' α n → β
  | nil     => init
  | cons a l => f a (foldr f init l)

  theorem foldr_max [Order β] {v: Vector' α n} (f : α → β) (init : β)
    (h: v.mem y):
    f y ≤ v.foldr (λ x acc => max (f x) acc) init := by
    induction v <;> simp only[foldr,Order.max_def]
    · admit
    · split <;> admit
end Vector'
