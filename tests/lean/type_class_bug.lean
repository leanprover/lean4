set_option pp.all true
#check
(do {
 a : nat ← [1],
 return a } : list nat )

#check
(do {
 a : nat ← [1, 2, 3],
 b : nat ← [3, 4],
 return (a, b) } : list (nat × nat) )
