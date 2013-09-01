Variable f : Type -> Bool
Show forall a b : Type, (f a) = (f b)
Variable g : Bool -> Bool -> Bool
Show forall (a b : Type) (c : Bool), g c ((f a) = (f b))
Show exists (a b : Type) (c : Bool), g c ((f a) = (f b))
Show forall (a b : Type) (c : Bool), (g c (f a) = (f b)) ⇒ (f a)
Check forall (a b : Type) (c : Bool), g c ((f a) = (f b))
Show ∀ (a b : Type) (c : Bool), g c ((f a) = (f b))
Show ∀ a b : Type, (f a) = (f b)
Show ∃ a b : Type, (f a) = (f b) ∧ (f a)
Show ∃ a b : Type, (f a) = (f b) ∨ (f b)
Variable a : Bool
Show (f a) ∨ (f a)
Show (f a) = a ∨ (f a)
Show (f a) = a ∧ (f a)
