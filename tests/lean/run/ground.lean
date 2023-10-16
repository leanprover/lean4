import Lean

-- TODO: move elaborator to core
open Lean Meta Elab Term
elab "ground " e:term : term <= expectedType =>
  return DiscrTree.mkGroundAnnotation (← elabTerm e expectedType)

def consn (n : Nat) (a : α) (as : List α) : List α :=
  match n with
  | 0 => as
  | n+1 => consn n a (a :: as)

@[simp] theorem consn_0 : consn 0 a as = as := rfl
@[simp] theorem consn_succ : consn (ground n+1) a as = consn n a (a::as) := rfl

example : consn (n+2) a as = consn n a (a::a::as) := by
  fail_if_success simp -- Should not fire consn_succ
  simp [consn]
  done

example : consn 2 a as = a::a::as := by
  simp -- should fire consn
