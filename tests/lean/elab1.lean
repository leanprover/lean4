

variable f {A : Type} (a b : A) : A.
check f 10 true

variable g {A B : Type} (a : A) : A.
check g 10

variable h : Pi (A : Type), A -> A.

check fun x, fun A : Type, h A x

variable my_eq : Pi A : Type, A -> A -> Bool.

check fun (A B : Type) (a : _) (b : _) (C : Type), my_eq C a b.

variable a : Bool
variable b : Bool
variable H : a /\ b
theorem t1 : b := Discharge (fun H1, Conj H1 (Conjunct1 H)).

theorem t2 : a = b := Trans (Refl a) (Refl b).

check f Bool Bool.

theorem pierce (a b : Bool) : ((a ⇒ b) ⇒ a) ⇒ a :=
    Discharge (λ H, DisjCases (EM a)
                              (λ H_a, H)
                              (λ H_na, NotImp1 (MT H H_na)))
