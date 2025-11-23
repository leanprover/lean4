/--
The notation typeclass for heterogeneous addition.
This enables the notation `a + b : γ` where `a : α`, `b : β`.
-/
class HAdd' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a + b` computes the sum of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hAdd : α → β → γ

instance : HAdd' Int Int Int where
  hAdd a b := a + b

/--
The notation typeclass for heterogeneous exponentiation.
This enables the notation `a ^ b : γ` where `a : α`, `b : β`.
-/
class HPow' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ^ b` computes `a` to the power of `b`.
  The meaning of this notation is type-dependent. -/
  hPow : α → β → γ

instance : HPow' Int Nat Int where
  hPow a b := a ^ b

--
macro_rules | `($x ⊕ $y)   => `(binop% HAdd'.hAdd $x $y)
macro_rules | `($x 𝒫 $y)   => `(binop% HPow'.hPow $x $y)
--^ waitForILeans
mutual

def h (x : Nat) : Int:=
  match x with
  | 0 => 1
             --v textDocument/definition
  | x+1 => r x ⊕ r x + (h x) 𝒫 2
                            --^ textDocument/definition
         --^ textDocument/definition

def r (x : Nat) := x + 1
end
