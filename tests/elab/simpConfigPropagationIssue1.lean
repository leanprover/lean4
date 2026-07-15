namespace Option

variable {α : Type _}

instance merge_isCommutative (f : α → α → α) [Std.Commutative f] :
    Std.Commutative (merge f) :=
  ⟨fun a b ↦ by cases a <;> cases b <;> simp [merge, Std.Commutative.comm]⟩

instance merge_isAssociative (f : α → α → α) [Std.Associative f] :
    Std.Associative (merge f) :=
  ⟨fun a b c ↦ by cases a <;> cases b <;> cases c <;> simp [merge, Std.Associative.assoc]⟩

end Option
