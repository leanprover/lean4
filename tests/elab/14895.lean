module

/-!
Regression test for https://github.com/leanprover/lean4/pull/14895.

`Sum`'s derived `BEq` is exposed, so `==` on sums still reduces from another module, and the
derived `ReflBEq`/`LawfulBEq` instances transfer from the components.
-/

example : (Sum.inl 0 == (Sum.inr 0 : Nat ⊕ Nat)) = false := rfl
example : (Sum.inl 0 == (Sum.inr 0 : Nat ⊕ Nat)) = false := by decide
example : (Sum.inl 0 == (Sum.inr 0 : Nat ⊕ Nat)) = false := by simp

example : (Sum.inl 0 == (Sum.inl 0 : Nat ⊕ Nat)) = true := rfl

example [BEq α] [BEq β] [ReflBEq α] [ReflBEq β] (x : α ⊕ β) : x == x := BEq.rfl

example [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] (x y : α ⊕ β) (h : x == y) : x = y :=
  eq_of_beq h
