namespace Option

variable {α : Type _}

instance liftOrGet_isCommutative (f : α → α → α) [Std.Commutative f] :
    Std.Commutative (liftOrGet f) :=
  ⟨fun a b ↦ by cases a <;> cases b <;> simp [liftOrGet, Std.Commutative.comm]⟩

instance liftOrGet_isAssociative (f : α → α → α) [Std.Associative f] :
    Std.Associative (liftOrGet f) :=
  ⟨fun a b c ↦ by cases a <;> cases b <;> cases c <;> simp [liftOrGet, Std.Associative.assoc]⟩

end Option
