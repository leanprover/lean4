variable N : Type
variable h : N -> N -> N

theorem congrH {a1 a2 b1 b2 : N} (H1 : a1 = b1) (H2 : a2 = b2) : (h a1 a2) = (h b1 b2) :=
   congr (congr (refl h) H1) H2

-- Display the theorem showing implicit arguments
set::option lean::pp::implicit true
print environment 2

-- Display the theorem hiding implicit arguments
set::option lean::pp::implicit false
print environment 2

theorem Example1 (a b c d : N) (H: (a = b ∧ b = c) ∨ (a = d ∧ d = c)) : (h a b) = (h c b) :=
    or::elim H
              (fun H1 : a = b ∧ b = c,
                   congrH (trans (and::eliml H1) (and::elimr H1)) (refl b))
              (fun H1 : a = d ∧ d = c,
                   congrH (trans (and::eliml H1) (and::elimr H1)) (refl b))

-- print proof of the last theorem with all implicit arguments
set::option lean::pp::implicit true
print environment 1

-- Using placeholders to hide the type of H1
theorem Example2 (a b c d : N) (H: (a = b ∧ b = c) ∨ (a = d ∧ d = c)) : (h a b) = (h c b) :=
    or::elim H
              (fun H1 : _,
                   congrH (trans (and::eliml H1) (and::elimr H1)) (refl b))
              (fun H1 : _,
                   congrH (trans (and::eliml H1) (and::elimr H1)) (refl b))

set::option lean::pp::implicit true
print environment 1

-- Same example but the first conjuct has unnecessary stuff
theorem Example3 (a b c d e : N) (H: (a = b ∧ b = e ∧ b = c) ∨ (a = d ∧ d = c)) : (h a b) = (h c b) :=
    or::elim H
              (fun H1 : _,
                   congrH (trans (and::eliml H1) (and::elimr (and::elimr H1))) (refl b))
              (fun H1 : _,
                   congrH (trans (and::eliml H1) (and::elimr H1)) (refl b))

set::option lean::pp::implicit false
print environment 1

theorem Example4 (a b c d e : N) (H: (a = b ∧ b = e ∧ b = c) ∨ (a = d ∧ d = c)) : (h a c) = (h c a) :=
    or::elim H
              (fun H1 : _,
                   let AeqC := trans (and::eliml H1) (and::elimr (and::elimr H1))
                   in congrH AeqC (symm AeqC))
              (fun H1 : _,
                   let AeqC := trans (and::eliml H1) (and::elimr H1)
                   in congrH AeqC (symm AeqC))

set::option lean::pp::implicit false
print environment 1
