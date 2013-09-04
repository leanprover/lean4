

Variable f {A : Type} (a b : A) : A.
Check f 10 true

Variable g {A B : Type} (a : A) : A.
Check g 10

Variable h : Pi (A : Type), A -> A.

Check fun x, fun A : Type, h A x

Variable eq : Pi A : Type, A -> A -> Bool.

Check fun (A B : Type) (a : _) (b : _) (C : Type), eq C a b.

Variable a : Bool
Variable b : Bool
Variable H : a /\ b
Theorem t1 : b := Discharge (fun H1, Conj H1 (Conjunct1 H)).

Theorem t2 : a = b := Trans (Refl a) (Refl b).

Check f Bool Bool.

Theorem pierce (a b : Bool) : ((a ⇒ b) ⇒ a) ⇒ a :=
    Discharge (λ H, DisjCases (EM a)
                              (λ H_a, H)
                              (λ H_na, NotImp1 (MT H H_na)))
