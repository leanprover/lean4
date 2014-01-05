variables A B C : (Type U)
variable P : A -> Bool
variable F1 : A -> B -> C
variable F2 : A -> B -> C
variable H : Pi (a : A) (b : B), (F1 a b) == (F2 a b)
variable a : A
check Eta (F2 a)
check Abst (fun a : A,
              (Trans (Symm (Eta (F1 a)))
                     (Trans (Abst (fun (b : B), H a b))
                            (Eta (F2 a)))))

check Abst (fun a, (Abst (fun b, H a b)))

theorem T1 : F1 = F2 := Abst (fun a, (Abst (fun b, H a b)))
theorem T2 : (fun (x1 : A) (x2 : B), F1 x1 x2) = F2 := Abst (fun a, (Abst (fun b, H a b)))
theorem T3 : F1 = (fun (x1 : A) (x2 : B), F2 x1 x2) := Abst (fun a, (Abst (fun b, H a b)))
theorem T4 : (fun (x1 : A) (x2 : B), F1 x1 x2) = (fun (x1 : A) (x2 : B), F2 x1 x2) := Abst (fun a, (Abst (fun b, H a b)))
print environment 4
setoption pp::implicit true
print environment 4