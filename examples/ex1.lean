Variable N : Type
Variable h : N -> N -> N

(* Specialize congruence theorem for h-applications *)
Theorem CongrH {a1 a2 b1 b2 : N} (H1 : a1 = b1) (H2 : a2 = b2) : (h a1 a2) = (h b1 b2) :=
   Congr (Congr (Refl h) H1) H2

(* Declare some variables *)
Variable a : N
Variable b : N
Variable c : N
Variable d : N
Variable e : N

(* Add axioms stating facts about these variables *)
Axiom H1 : (a = b ∧ b = c) ∨ (a = d ∧ d = c)
Axiom H2 : b = e

(* Proof that (h a b) = (h c e) *)
Theorem T1 : (h a b) = (h c e) :=
    DisjCases H1
              (fun C1 : _,
                   CongrH (Trans (Conjunct1 C1) (Conjunct2 C1)) H2)
              (fun C2 : _,
                   CongrH (Trans (Conjunct1 C2) (Conjunct2 C2)) H2)

(* We can use theorem T1 to prove other theorems *)
Theorem T2 : (h a (h a b)) = (h a (h c e)) :=
    CongrH (Refl a) T1

(* Display the last two objects (i.e., theorems) added to the environment *)
Show Environment 2

(* Show implicit arguments *)
Set lean::pp::implicit true
Set pp::width 150
Show Environment 2
