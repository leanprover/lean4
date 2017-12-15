namespace foo
open nat

class lt (n : out_param ℕ) (m : ℕ)
instance succ_lt_succ_of_lt (n m) [lt n m] : lt (succ n) (succ m) := by constructor
instance zero_lt_succ (m) : lt 0 (succ m) := by constructor

class foo (n : out_param ℕ) (m : ℕ)
instance (n m) [lt n 10] [lt m n] : foo n m := by constructor

def bar {n} (m) [foo n m] := n
#eval bar 0
#eval bar 1
end foo
