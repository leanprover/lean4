class FooClass (α : Type _) : Prop where

theorem bar (α ι : Type _) [FooClass α] (f : ι → FooClass α) : FooClass α := by
  infer_instance
