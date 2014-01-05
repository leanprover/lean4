variable f : Type -> Bool
variable g : Type -> Type -> Bool
print forall (a b : Type), exists (c : Type), (g a b) = (f c)
check forall (a b : Type), exists (c : Type), (g a b) = (f c)
eval forall (a b : Type), exists (c : Type), (g a b) = (f c)
