notation a " +' " b => a + b

set_option trace.Elab.info true
-- should contain all macro expansions
#check 1 + 2 + 3
-- should propagate through multiple macro expansions
#check fun (n m l : Nat) => (n + (m +' l) : Int)
