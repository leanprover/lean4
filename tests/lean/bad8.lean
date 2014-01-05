import Int.
variable list : Type → Type
variable nil {A : Type} : list A
variable cons {A : Type} (head : A) (tail : list A) : list A
variable a : ℤ
variable b : ℤ
variable n : ℕ
variable m : ℕ
definition l1 : list ℤ := cons a (cons b (cons n nil))
definition l2 : list ℤ := cons a (cons n (cons b nil))
