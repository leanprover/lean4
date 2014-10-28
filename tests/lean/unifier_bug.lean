import logic

theorem test {A B : Type} {a : A} {b : B} (H : a == b) :
           eq.rec_on (heq.type_eq H) a = b
:=
-- Remark the error message should not occur in the token theorem
heq.rec_on H rfl
