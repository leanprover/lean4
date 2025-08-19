structure Fin' (n : Nat) where
  val  : Nat
  isLt : val < n
  deriving DecidableEq

#eval
  (Fin'.mk 0 (Nat.lt.step (Nat.lt.base 0)): Fin' 2)
  = (Fin'.mk 0 (Nat.lt.step (Nat.lt.base 0)) : Fin' 2)

#eval
  (Fin'.mk 0 (Nat.lt.step (Nat.lt.base 0)): Fin' 2)
  = (Fin'.mk 1 (Nat.lt.base 1) : Fin' 2)

inductive List' (α : Type u) where
  | nil : List' α
  | cons (head : α) (tail : List' α) (h : head = head) : List' α
deriving DecidableEq

#eval
  List'.nil.cons 0 rfl
  = List'.nil.cons 0 rfl

#eval
  List'.nil.cons 0 rfl
  = (List'.nil.cons 0 rfl).cons 1 rfl

structure A
deriving DecidableEq

#eval A.mk = A.mk
