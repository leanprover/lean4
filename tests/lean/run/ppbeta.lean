import data.int
open [coercions] int
open [coercions] nat

definition lt (a b : int) := int.le (int.add a 1) b
infix `<`     := lt
infixl `+`:65 := int.add

theorem lt_add_succ2 (a : int) (n : nat) : a < a + nat.succ n :=
int.le_intro (show a + 1 + n = a + nat.succ n, from sorry)
