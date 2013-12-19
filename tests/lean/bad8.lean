Variable list : Type → Type
Variable nil {A : Type} : list A
Variable cons {A : Type} (head : A) (tail : list A) : list A
Variable a : ℤ
Variable b : ℤ
Variable n : ℕ
Variable m : ℕ
Definition l1 : list ℤ := cons a (cons b (cons n nil))
Definition l2 : list ℤ := cons a (cons n (cons b nil))
