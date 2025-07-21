inductive Expr (Identifier : Type) : Type where
  | mk (c : String)

def fv {I:Type} (e : Expr I) : List I := sorry

def eql {I:Type} [DecidableEq I] (e : Expr I) (_h1 : fv e == []) : Nat := sorry

def eval {I:Type} [DecidableEq I] (n : Nat) (e : Expr I) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ n' =>
    let e2' := eval n' e
    eql e sorry
  termination_by n
