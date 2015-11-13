import algebra.simplifier
open algebra

open simplifier.numeral

set_option simplify.max_steps 5000000
universe l
constants (A : Type.{l}) (A_comm_ring : comm_ring A)
attribute A_comm_ring [instance]

#simplify eq 0 (0:A) + 1
#simplify eq 0 (1:A) + 0
#simplify eq 0 (1:A) + 1
#simplify eq 0 (0:A) + 2
#simplify eq 0 (1:A) + 2
#simplify eq 0 (2:A) + 1
#simplify eq 0 (3:A) + 1
#simplify eq 0 (2:A) + 2
#simplify eq 0 (4:A) + 1
#simplify eq 0 (3:A) + 2
#simplify eq 0 (2:A) + 3
#simplify eq 0 (0:A) + 6
#simplify eq 0 (3:A) + 3
#simplify eq 0 (4:A) + 2
#simplify eq 0 (5:A) + 1
#simplify eq 0 (4:A) + 3
#simplify eq 0 (1:A) + 6
#simplify eq 0 (6:A) + 1
#simplify eq 0 (5:A) + 28
#simplify eq 0 (0 : A) + (2 + 3) + 7
#simplify eq 0 (70 : A) + (33 + 2)

#simplify eq 0 (23000000000 : A) + 22000000000

#simplify eq 0 (0 : A) * 0
#simplify eq 0 (0 : A) * 1
#simplify eq 0 (0 : A) * 2
#simplify eq 0 (2 : A) * 0
#simplify eq 0 (1 : A) * 0
#simplify eq 0 (1 : A) * 1
#simplify eq 0 (2 : A) * 1
#simplify eq 0 (1 : A) * 2
#simplify eq 0 (2 : A) * 2
#simplify eq 0 (3 : A) * 2
#simplify eq 0 (2 : A) * 3
#simplify eq 0 (4 : A) * 1
#simplify eq 0 (1 : A) * 4
#simplify eq 0 (3 : A) * 3
#simplify eq 0 (3 : A) * 4
#simplify eq 0 (4 : A) * 4
#simplify eq 0 (11 : A) * 2
#simplify eq 0 (15 : A) * 6
#simplify eq 0 (123456 : A) * 123456

-- The following test is too slow
-- #simplify eq 0 (23000000000343434534345316:A) * (53653343563534534 + 5367536453653573573453) * 53453756475777536 + 2200000000034733531531531534536
