import data.nat data.int
open nat

find_decl _ < succ _, +imp, -le

find_decl _ < _ + _

find_decl _ = succ _

find_decl _ < succ _, +pos

find_decl zero < succ _, pos

set_option find_decl.expensive true
-- Now, nat.zero will match 0 (i.e., (of_num num.zero))
find_decl zero < succ _, pos
