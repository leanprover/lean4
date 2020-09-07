new_frontend

partial def reverse {α} (as : List α) : List α :=
let rec loop : List α → List α → List α
  | [],    r => r
  | a::as, r => loop as (a::r);
loop as []

#eval reverse [3, 2, 1]
#eval reverse [1, 2, 3, 4]
#print reverse
#print reverse.loop
#print reverse.loop._unsafe_rec
