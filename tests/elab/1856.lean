structure Equiv (α : Sort _) (β : Sort _) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x

infixl:25 " ≃ " => Equiv

/-- A product of types can be split as the binary product of one of the types and the product
  of all the remaining types. -/
def piSplitAt {α : Type _} [DecidableEq α] (i : α) (β : α → Type _) :
    (∀ j, β j) ≃ β i × ∀ j : { j // j ≠ i }, β j where
  toFun f := ⟨f i, fun j => f j⟩
  invFun f j := if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩
  left_inv f := by
    apply funext
    intro x
    /- Goal is now:
    ```
    (fun f j => if h : j = i then (_ : i = j) ▸ f.fst else Prod.snd f { val := j, property := h })
      ((fun f => (f i, fun j => f j.val)) f) x =
      f x
    ```
    -/
    dsimp
    trace_state
    sorry
