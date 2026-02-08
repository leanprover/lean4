

partial def reverse {α} (as : List α) : List α :=
let rec loop : List α → List α → List α
  | [],    r => r
  | a::as, r => loop as (a::r)
loop as []

#guard reverse [3, 2, 1] == [1, 2, 3]
#guard reverse [1, 2, 3, 4] == [4, 3, 2, 1]

#print reverse

#print reverse.loop
#print reverse.loop._unsafe_rec

partial def appendRev {α} (extra : List α) (as : List α) : List α :=
let rec loop (as acc : List α) : List α :=
  match as, acc with
  | [],    r => extra ++ r
  | a::as, r => loop as (a::r)
loop as []

#guard appendRev [3, 4] [1, 2, 0] == [3, 4, 0, 2, 1]
