def get : (as : List α) → (i : Fin as.length) → α
  | a::as, .mk 0 _     => a
  | a::as, .mk (i+1) h => get as (.mk i (Nat.lt_of_succ_lt_succ h))

namespace Ex

inductive Fin : Nat → Type
  | zero : Fin (.succ n)
  | succ : Fin n → Fin (.succ n)
  deriving Repr

def get : (as : List α) → (i : Fin as.length) → α
  | a::as, .zero   => a
  | a::as, .succ i => get as i

end Ex
