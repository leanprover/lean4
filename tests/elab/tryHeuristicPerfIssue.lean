class L1 (α : Type u) where
  add    : α → α → α
  addc1  : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x

instance L1.toAdd [inst : L1 α] : Add α := { inst with }

class L2 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x

instance L2.toL1 [inst : L2 α] : L1 α := { inst with }

class L3 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x

instance L3.toL2 [inst : L3 α] : L2 α := { inst with }

class L4 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x
  addc4 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) y x

instance L4.toL3 [inst : L4 α] : L3 α := { inst with }

class L5 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x
  addc4 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) y x
  addc5 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) y x

instance L5.toL4 [inst : L5 α] : L4 α := { inst with }

class L6 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x
  addc4 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) y x
  addc5 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) y x
  addc6 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) y x

instance L6.toL5 [inst : L6 α] : L5 α := { inst with }

class L7 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x
  addc4 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) y x
  addc5 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) y x
  addc6 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) y x
  addc7 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) y x

instance L7.toL6 [inst : L7 α] : L6 α := { inst with }

class L8 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x
  addc4 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) y x
  addc5 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) y x
  addc6 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) y x
  addc7 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) y x
  addc8 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7⟩))))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7⟩))))))) y x

instance L8.toL7 [inst : L8 α] : L7 α := { inst with }

class L9 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x
  addc4 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) y x
  addc5 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) y x
  addc6 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) y x
  addc7 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) y x
  addc8 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7⟩))))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7⟩))))))) y x
  addc9 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ (@L8.toL7 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7, addc8⟩)))))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ (@L8.toL7 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7, addc8⟩)))))))) y x

instance L9.toL8 [inst : L9 α] : L8 α := { inst with }

class T1 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x
  addc4 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) y x
  addc5 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) y x
  addc6 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) y x
  addc7 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) y x
  addc8 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7⟩))))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7⟩))))))) y x
  addc9 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ (@L8.toL7 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7, addc8⟩)))))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ (@L8.toL7 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7, addc8⟩)))))))) y x

-- slow
instance T1.toL9 [inst : T1 α] : L9 α := { inst with }

class T2 (α : Type u) where
  add   : α → α → α
  addc1 : ∀ (x y : α), @Add.add α ⟨add⟩ x y = @Add.add α ⟨add⟩ y x
  addc2 : ∀ (x y : α), @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) x y = @Add.add α (@L1.toAdd _ ⟨add, addc1⟩) y x
  addc3 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ ⟨add, addc1, addc2⟩)) y x
  addc4 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ ⟨add, addc1, addc2, addc3⟩))) y x
  addc5 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ ⟨add, addc1, addc2, addc3, addc4⟩)))) y x
  addc6 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ ⟨add, addc1, addc2, addc3, addc4, addc5⟩))))) y x
  addc7 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6⟩)))))) y x
  addc8 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7⟩))))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7⟩))))))) y x
  addc9 : ∀ (x y : α), @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ (@L8.toL7 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7, addc8⟩)))))))) x y = @Add.add α (@L1.toAdd _ (@L2.toL1 _ (@L3.toL2 _ (@L4.toL3 _ (@L5.toL4 _ (@L6.toL5 _ (@L7.toL6 _ (@L8.toL7 _ ⟨add, addc1, addc2, addc3, addc4, addc5, addc6, addc7, addc8⟩)))))))) y x

-- slow
instance T2.toL9 [inst : T2 α] : L9 α := { inst with }


set_option pp.all true in
-- #print T2.toL9

axiom C : Type
axiom C.add   : C → C → C

noncomputable instance C.T1 : T1 C := ⟨add, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry⟩
noncomputable instance C.T2 : T2 C := ⟨add, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry, sorry⟩

-- slow
example : @T1.toL9 _ C.T1 = @T2.toL9 _ C.T2 := rfl
