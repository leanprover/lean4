variable N : Type
variable h : N -> N -> N

-- Specialize congruence theorem for h-applications
theorem congrh {a1 a2 b1 b2 : N} (H1 : a1 = b1) (H2 : a2 = b2) : (h a1 a2) = (h b1 b2) :=
   congr (congr (refl h) H1) H2

-- Declare some variables
variable a : N
variable b : N
variable c : N
variable d : N
variable e : N

-- Add axioms stating facts about these variables
axiom H1 : (a = b ∧ b = c) ∨ (d = c ∧ a = d)
axiom H2 : b = e

-- Proof that (h a b) = (h c e)
theorem T1 : (h a b) = (h c e) :=
    or::elim H1
        (λ C1, congrh ((and::eliml C1) ⋈ (and::elimr C1)) H2)
        (λ C2, congrh ((and::elimr C2) ⋈ (and::eliml C2)) H2)

-- We can use theorem T1 to prove other theorems
theorem T2 : (h a (h a b)) = (h a (h c e)) :=
    congrh (refl a) T1

-- Display the last two objects (i.e., theorems) added to the environment
print environment 2

-- print implicit arguments
set::option lean::pp::implicit true
set::option pp::width 150
print environment 2
