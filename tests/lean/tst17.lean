Variable f : Type -> Bool
Variable g : Type -> Type -> Bool
print forall (a b : Type), exists (c : Type), (g a b) = (f c)
Check forall (a b : Type), exists (c : Type), (g a b) = (f c)
Eval forall (a b : Type), exists (c : Type), (g a b) = (f c)
