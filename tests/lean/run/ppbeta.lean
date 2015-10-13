import data.int
open [coercions] [classes] int
open [coercions] nat

definition lt1 (a b : int) := int.le (int.add a 1) b
infix `<`     := lt1
infixl `+` := int.add

theorem lt_add_succ2 (a : int) (n : nat) : a < a + nat.succ n :=
int.le.intro (show a + 1 + n = a + nat.succ n, from sorry)
