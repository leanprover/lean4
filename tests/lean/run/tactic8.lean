import logic

exit -- TODO
theorem tst {A B : Bool} (H1 : A) (H2 : B) : A ∧ B ∧ A
:= by (apply and_intro,
       show A, from H1,
       show B ∧ A, from and_intro H2 H1)
check @tst