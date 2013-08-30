
Variable N : Type
Variable h : N -> N -> N

Theorem CongrH {a1 a2 b1 b2 : N} (H1 : a1 = b1) (H2 : a2 = b2) : (h a1 a2) = (h b1 b2) :=
   Congr (Congr (Refl h) H1) H2

(* Display the theorem showing implicit arguments *)
Set lean::pp::implicit true
Show Environment 2

(* Display the theorem hiding implicit arguments *)
Set lean::pp::implicit false
Show Environment 2

Theorem Example1 (a b c d : N) (H: (a = b ∧ b = c) ∨ (a = d ∧ d = c)) : (h a b) = (h c b) :=
    DisjCases H
              (fun H1 : a = b ∧ b = c,
                   CongrH (Trans (Conjunct1 H1) (Conjunct2 H1)) (Refl b))
              (fun H1 : a = d ∧ d = c,
                   CongrH (Trans (Conjunct1 H1) (Conjunct2 H1)) (Refl b))

(* Show proof of the last theorem with all implicit arguments *)
Set lean::pp::implicit true
Show Environment 1

(* Using placeholders to hide the type of H1 *)
Theorem Example2 (a b c d : N) (H: (a = b ∧ b = c) ∨ (a = d ∧ d = c)) : (h a b) = (h c b) :=
    DisjCases H
              (fun H1 : _,
                   CongrH (Trans (Conjunct1 H1) (Conjunct2 H1)) (Refl b))
              (fun H1 : _,
                   CongrH (Trans (Conjunct1 H1) (Conjunct2 H1)) (Refl b))

Set lean::pp::implicit true
Show Environment 1

(* Same example but the first conjuct has unnecessary stuff *)
Theorem Example3 (a b c d e : N) (H: (a = b ∧ b = e ∧ b = c) ∨ (a = d ∧ d = c)) : (h a b) = (h c b) :=
    DisjCases H
              (fun H1 : _,
                   CongrH (Trans (Conjunct1 H1) (Conjunct2 (Conjunct2 H1))) (Refl b))
              (fun H1 : _,
                   CongrH (Trans (Conjunct1 H1) (Conjunct2 H1)) (Refl b))

Set lean::pp::implicit false
Show Environment 1
