notation "a" => fun x => a

syntax "b" term : term
notation "c" => b x

set_option quotPrecheck false
notation "d" => b x
#check d
