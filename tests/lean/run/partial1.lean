

partial def reverse {α} (as : List α) : List α :=
let rec loop : List α → List α → List α
  | [],    r => r
  | a::as, r => loop as (a::r)
loop as []

#eval reverse [3, 2, 1]
#eval reverse [1, 2, 3, 4]
#print reverse
#print reverse.loop
#print reverse.loop._unsafe_rec

partial def appendRev {α} (extra : List α) (as : List α) : List α :=
let rec loop (as acc : List α) : List α :=
  match as, acc with
  | [],    r => extra ++ r
  | a::as, r => loop as (a::r)
loop as []

#eval appendRev [3, 4] [1, 2, 0]
