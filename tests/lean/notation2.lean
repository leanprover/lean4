import data.list data.num
open list
infixr `::` := cons
check 1 :: 2 :: nil
check 1 :: 2 :: 3 :: 4 :: 5 :: nil
