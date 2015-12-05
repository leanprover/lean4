import algebra.ring algebra.numeral
open algebra

set_option simplify.max_steps 5000000
-- TODO(dhs): we need to create the simplifier.numeral namespace incrementally.
-- Once it exists, we can uncomment the following line to use it simplify.
set_option simplify.numerals true
universe l
constants (A : Type.{l}) (A_comm_ring : comm_ring A)
attribute A_comm_ring [instance]

#simplify eq env 0 (0:A) + 1
#simplify eq env 0 (1:A) + 0
#simplify eq env 0 (1:A) + 1
#simplify eq env 0 (0:A) + 2
#simplify eq env 0 (1:A) + 2
#simplify eq env 0 (2:A) + 1
#simplify eq env 0 (3:A) + 1
#simplify eq env 0 (2:A) + 2
#simplify eq env 0 (4:A) + 1
#simplify eq env 0 (3:A) + 2
#simplify eq env 0 (2:A) + 3
#simplify eq env 0 (0:A) + 6
#simplify eq env 0 (3:A) + 3
#simplify eq env 0 (4:A) + 2
#simplify eq env 0 (5:A) + 1
#simplify eq env 0 (4:A) + 3
#simplify eq env 0 (1:A) + 6
#simplify eq env 0 (6:A) + 1
#simplify eq env 0 (5:A) + 28
#simplify eq env 0 (0 : A) + (2 + 3) + 7
#simplify eq env 0 (70 : A) + (33 + 2)

#simplify eq env 0 (23000000000 : A) + 22000000000

#simplify eq env 0 (0 : A) * 0
#simplify eq env 0 (0 : A) * 1
#simplify eq env 0 (0 : A) * 2
#simplify eq env 0 (2 : A) * 0
#simplify eq env 0 (1 : A) * 0
#simplify eq env 0 (1 : A) * 1
#simplify eq env 0 (2 : A) * 1
#simplify eq env 0 (1 : A) * 2
#simplify eq env 0 (2 : A) * 2
#simplify eq env 0 (3 : A) * 2
#simplify eq env 0 (2 : A) * 3
#simplify eq env 0 (4 : A) * 1
#simplify eq env 0 (1 : A) * 4
#simplify eq env 0 (3 : A) * 3
#simplify eq env 0 (3 : A) * 4
#simplify eq env 0 (4 : A) * 4
#simplify eq env 0 (11 : A) * 2
#simplify eq env 0 (15 : A) * 6
#simplify eq env 0 (123456 : A) * 123456

#simplify eq env 0 (0 + 45343453:A) * (53653343 + 1) * (53453 + 2) + (0 + 1 + 2 + 2200000000034733)

#simplify eq env 0 (23000000000343434534345316:A) * (53653343563534534 + 5367536453653573573453) * 53453756475777536 + 2200000000034733531531531534536
