notation "a" => fun x => a

syntax "b" term : term
notation "c" => b x

set_option quotPrecheck false in
notation "d" => b x
#check d

infix:10 " ∧ " => and
set_option pp.raw true
notation "foo" => fun x y => x ∧ y
notation "bar" => fun x => x ∧ y
