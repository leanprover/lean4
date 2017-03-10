#eval
(do {
 a : nat ← [1, 2, 3, 4],
 b : nat ← [4, 5, 6],
 (guard $ 2 * a ≥ b : list unit),
 (guard $ b < 6 : list unit),
 return (a, b) } : list (nat × nat) )
