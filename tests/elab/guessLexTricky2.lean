/-!
Another “tricky” example from “Finding Lexicographic Orders for Termination Proofs in
Isabelle/HOL” by Lukas Bulwahn, Alexander Krauss, and Tobias Nipkow,
10.1007/978-3-540-74591-4_5.

Works out of the box!
-/

set_option showInferredTerminationBy true

mutual
def pedal : Nat → Nat → Nat → Nat
  | 0, _m, c => c
  | _n, 0, c => c
  | n+1, m+1, c =>
    if n < m
    then coast n m (c + m + 1)
    else pedal n (m + 1) (c + m + 1)

def coast : Nat → Nat → Nat → Nat
  | n, m , c =>
  if n < m
  then coast n (m - 1) (c + n)
  else pedal n m (c + n)
end
