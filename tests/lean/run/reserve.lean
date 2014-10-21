import logic

reserve infix `=?=`:50
reserve infixr `&&&`:25

notation a `=?=` b := eq a b
notation a `&&&` b := and a b

set_option pp.notation false
check λ a b : num, a =?= b &&& b =?= a
