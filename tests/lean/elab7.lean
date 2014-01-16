variables A B C : (Type U)
variable P : A -> Bool
variable F1 : A -> B -> C
variable F2 : A -> B -> C
variable H : forall (a : A) (b : B), (F1 a b) = (F2 a b)
variable a : A
check eta (F2 a)
check funext (fun a : A,
              (trans (symm (eta (F1 a)))
                     (trans (funext (fun (b : B), H a b))
                            (eta (F2 a)))))

check funext (fun a, (funext (fun b, H a b)))

theorem T1 : F1 = F2 := funext (fun a, (funext (fun b, H a b)))
theorem T2 : (fun (x1 : A) (x2 : B), F1 x1 x2) = F2 := funext (fun a, (funext (fun b, H a b)))
theorem T3 : F1 = (fun (x1 : A) (x2 : B), F2 x1 x2) := funext (fun a, (funext (fun b, H a b)))
theorem T4 : (fun (x1 : A) (x2 : B), F1 x1 x2) = (fun (x1 : A) (x2 : B), F2 x1 x2) := funext (fun a, (funext (fun b, H a b)))
print environment 4
set_option pp::implicit true
print environment 4