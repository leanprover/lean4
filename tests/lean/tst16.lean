Variable f : Type -> Bool
print forall a b : Type, (f a) = (f b)
Variable g : Bool -> Bool -> Bool
print forall (a b : Type) (c : Bool), g c ((f a) = (f b))
print exists (a b : Type) (c : Bool), g c ((f a) = (f b))
print forall (a b : Type) (c : Bool), (g c (f a) = (f b)) ⇒ (f a)
Check forall (a b : Type) (c : Bool), g c ((f a) = (f b))
print ∀ (a b : Type) (c : Bool), g c ((f a) = (f b))
print ∀ a b : Type, (f a) = (f b)
print ∃ a b : Type, (f a) = (f b) ∧ (f a)
print ∃ a b : Type, (f a) = (f b) ∨ (f b)
Variable a : Bool
print (f a) ∨ (f a)
print (f a) = a ∨ (f a)
print (f a) = a ∧ (f a)
