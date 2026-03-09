set_option linter.constructorNameAsVariable false

inductive  A (n : Nat) : Type
  | a : A n
  | b : A n → A n

def A.size (acc n : Nat) : A n → Nat
  | .a => acc
  | .b a' => 1 + A.size (acc + 1) n a'
termination_by structural a => a

-- Another instance reported on Zulip at
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.E2.9C.94.20Doubly-nested.20inductive/near/451204850

inductive Xn (e : Sigma.{0} (· → Type)) (α : Type) : Nat → Type where
| mk1_S {n} (x : Xn e α n) : Xn e α (n+1)
| mk2 {n} (s : e.1) (p : e.2 s → Xn e α n) : Xn e α n

def Xn.zip {e α m n} : Xn e (Xn e α n) m → Xn e α (n+m+1)
  | .mk1_S x => .mk1_S x.zip
  | .mk2 s p => .mk2 s fun a => (p a).zip
termination_by structural x => x

def Xn.zip' {e α n m} : Xn e (Xn e α n) m → Xn e α (n+m+1)
  | .mk1_S x => .mk1_S x.zip'
  | .mk2 s p => .mk2 s fun a => (p a).zip'
termination_by structural x => x
