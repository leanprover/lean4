instance [Mul α] : HMul α (Array α) (Array α) where
  hMul a as := as.map (a * .)

#check fun x => x * 2
#check fun y : Int => let  x := 1; x * y
#check fun y : Int => let_delayed x := 1; x * y

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
  let y := 2 * i
  let x := y * n
  n + x

def f7 (n : Nat) (i : Int) :=
  n + (n * 2 * i)

def f8 (n : Nat) (i : Int) :=
  n * 2 + (i * 1 * n * 2 * i)
