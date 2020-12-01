class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hmul : α → β → γ

class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hadd : α → β → γ

@[defaultInstance 1]
instance [Mul α] : HMul α α α where
  hmul a b := a * b

@[defaultInstance 1]
instance [Add α] : HAdd α α α where
  hadd a b := a + b

instance [Mul α] : HMul α (Array α) (Array α) where
  hmul a as := as.map (a * .)

infix:70 [1] "*" => HMul.hmul

infix:65 [1] "+" => HAdd.hadd

#check fun x => x * 2
#check fun y : Int => let  x := 1; x * y
#check fun y : Int => let* x := 1; x * y

instance : HMul Nat Int Int where
  hmul a b := Int.mul a b

instance : HMul Int Nat Int where
  hmul a b := Int.mul a b

instance : HAdd Nat Int Int where
  hadd a b := Int.add a b

instance : HAdd Int Nat Int where
  hadd a b := Int.add a b

def f1 (n : Nat) (i : Int) :=
  i * n

def f2 (n : Nat) (i : Int) :=
  n * i

def f3 (n : Nat) (i : Int) :=
  n * (n * (n * (n * i)))

def f4 (n : Nat) (i : Int) :=
  n + (n + (n * (n * i)))

def f5 (n : Nat) (i : Int) :=
  n + (n + (n * (i, i).1))

#eval (2:Nat) * #[3, 4, 5]

def f6 (n : Nat) (i : Int) :=
  n + n * (2:Nat) * i
