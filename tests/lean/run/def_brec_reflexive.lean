
inductive inftree (A : Type*)
| leaf : A → inftree
| node : (nat → inftree) → inftree

open inftree

definition {u} szn {A : Type (u+1)} (n : nat) : inftree A → inftree A → nat
| (leaf a) t2       := 1
| (node c) (leaf b) := 0
| (node c) (node d) := szn (c n) (d n)
