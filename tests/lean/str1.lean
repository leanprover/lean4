import data.list

-- set_option pp.all true
open string char list

check "ABC"

check str (of_nat 68) (str (of_nat 65) (str (of_nat 66) "abc"))

check list.cons (of_nat 65) "abc"

check list.cons (of_nat 66) (list.cons (of_nat 65) list.nil)

check (of_nat 67)::(of_nat 66)::(of_nat 65)::nil

check (of_nat 68)::"abc"

check append "abc" "cde"

set_option pp.strings false

check "ABC"

check str (of_nat 68) (str (of_nat 65) (str (of_nat 66) "abc"))

check list.cons (of_nat 65) "abc"

check list.cons (of_nat 66) (list.cons (of_nat 65) list.nil)

check (of_nat 67)::(of_nat 66)::(of_nat 65)::nil

check (of_nat 68)::"abc"

check append "abc" "cde"
