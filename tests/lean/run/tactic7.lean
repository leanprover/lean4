import logic

exit -- TODO
theorem tst {A B : Bool} (H1 : A) (H2 : B) : A ∧ B ∧ A
:= by (print, apply and_intro, print, exact, apply and_intro, print, !exact)
