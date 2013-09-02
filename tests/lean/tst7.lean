Set pp::colors false
Variable f : Pi (A : Type), A -> Bool
Show fun (A B : Type) (a : _), f B a
(* The following one should produce an error *)
Show fun (A : Type) (a : _) (B : Type), f B a

Variable myeq : Pi (A : Type U), A -> A -> Bool
Show  myeq _ (fun (A : Type) (a : _), a) (fun (B : Type) (b : B), b)
Check myeq _ (fun (A : Type) (a : _), a) (fun (B : Type) (b : B), b)


Variable R : Type -> Bool
Variable h : (Pi (A : Type), R A) -> Bool
Check (fun (H  : Bool)
           (f1 : Pi (A : Type), R _)
           (g1 : Pi (A : Type), R A)
           (G  : Pi (A : Type), myeq _ (f1 _) (g1 A)),
           h f1)
