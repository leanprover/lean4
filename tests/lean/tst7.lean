variable f : forall (A : Type), A -> Bool
print fun (A B : Type) (a : _), f B a
-- The following one should produce an error
print fun (A : Type) (a : _) (B : Type), f B a

variable myeq : forall A : (Type U), A -> A -> Bool
print  myeq _ (fun (A : Type) (a : _), a) (fun (B : Type) (b : B), b)
check myeq _ (fun (A : Type) (a : _), a) (fun (B : Type) (b : B), b)


variable R : Type -> Bool
variable h : (forall (A : Type), R A) -> Bool
check (fun (H  : Bool)
           (f1 : forall (A : Type), R _)
           (g1 : forall (A : Type), R A)
           (G  : forall (A : Type), myeq _ (f1 _) (g1 A)),
           h f1)
