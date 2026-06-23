module

/-! Regression test for issue 13407 -/

inductive Result (α : Type) where | ok (x : α) | err
instance : Monad Result where
  pure x := .ok x
  bind s f := match s with | .ok x => f x | .err => .err
instance : Coe α (Result α) where coe x := .ok x

structure Int' (bits : Nat) where val : Nat

def Int'.wrap (n : Int) (bits : Nat) : Int' bits := ⟨(n % (2^bits : Int)).toNat⟩

def Int'.toInt (x : Int' bits) : Int :=
  if x.val < 2^(bits - 1) then ↑x.val else ↑x.val - ↑(2^bits)

instance (n : Nat) : OfNat (Int' bits) n where ofNat := ⟨n % (2^bits)⟩
instance : Neg (Int' bits) where neg x := Int'.wrap (-Int'.toInt x) bits
instance : Repr (Int' bits) := ⟨fun x _ => repr (Int'.toInt x)⟩

class BinOp1 (α β : Type) (γ : outParam Type) where binOp1 : α → β → γ
class BinOp2 (α β : Type) (γ : outParam Type) where binOp2 : α → β → γ
class UnaryOp (α : Type) (β : outParam Type) where unaryOp : α → β
class Cast (α β : Type) where cast : α → Result β

instance : BinOp1 (Int' b) (Int' b) (Result (Int' b)) where
  binOp1 a c := .ok (Int'.wrap (a.toInt + c.toInt) b)

instance : BinOp1 (Int' l) (Int' r) (Result (Int' l)) where
  binOp1 a c := .ok (Int'.wrap (a.toInt + c.toInt) l)

instance : BinOp2 (Int' b) (Int' b) (Result (Int' b)) where
  binOp2 a c := .ok (Int'.wrap (a.toInt + c.toInt) b)

instance : UnaryOp (Int' b) (Result (Int' b)) where
  unaryOp a := .ok (Int'.wrap (-(a.toInt + 1)) b)

instance : Cast (Int' n) (Int' m) where
  cast x := .ok (Int'.wrap x.toInt m)

set_option linter.unusedVariables false

def helper (_ : Nat) : Result (Int' 64) := UnaryOp.unaryOp (1 : Int' 64)

def test (a : Nat) : Result (Int' 16) := do
  let x ← UnaryOp.unaryOp (1 : Int' 16)
  let y ← BinOp2.binOp2
        (← (Cast.cast (← helper a) : Result (Int' 128)))
        (← BinOp1.binOp1
              (← (Cast.cast (← helper a) : Result (Int' 128)))
              (← BinOp2.binOp2
                    (← BinOp1.binOp1 (10 : Int' 128) (1 : Int' 128))
                    (← BinOp2.binOp2 (7 : Int' 128) (3 : Int' 128))))
  BinOp1.binOp1
    (← (Cast.cast (← (Cast.cast y : Result (Int' 128))) : Result (Int' 16)))
    (← BinOp2.binOp2 x (← BinOp2.binOp2 x x))

/-- info: 11 -/
#guard_msgs in
#eval do
  match test 0 with
  | .ok v => IO.println (repr v)
  | .err => IO.println "ERR"
