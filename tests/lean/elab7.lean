Variables A B C : (Type U)
Variable P : A -> Bool
Variable F1 : A -> B -> C
Variable F2 : A -> B -> C
Variable H : Pi (a : A) (b : B), (F1 a b) == (F2 a b)
Variable a : A
Check Eta (F2 a)
Check Abst (fun a : A,
              (Trans (Symm (Eta (F1 a)))
                     (Trans (Abst (fun (b : B), H a b))
                            (Eta (F2 a)))))

Check Abst (fun a, (Abst (fun b, H a b)))

Theorem T1 : F1 = F2 := Abst (fun a, (Abst (fun b, H a b)))
Theorem T2 : (fun (x1 : A) (x2 : B), F1 x1 x2) = F2 := Abst (fun a, (Abst (fun b, H a b)))
Theorem T3 : F1 = (fun (x1 : A) (x2 : B), F2 x1 x2) := Abst (fun a, (Abst (fun b, H a b)))
Theorem T4 : (fun (x1 : A) (x2 : B), F1 x1 x2) = (fun (x1 : A) (x2 : B), F2 x1 x2) := Abst (fun a, (Abst (fun b, H a b)))
Show Environment 4
SetOption pp::implicit true
Show Environment 4