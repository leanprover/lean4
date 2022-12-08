@[default_instance]
instance [Mul α] : HMul α (Array α) (Array α) where
  hMul a as := as.map (a * ·)

instance [Mul α] : Mul (Array α) where
  mul as bs := (as.zip bs).map fun (a, b) => a * b

#eval 2 * #[3, 4, 5]

#eval (2:Nat) * #[3, 4, 5]

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

def f6 (n : Nat) (i : Int) :=
  let y := 2 * i
  let x := y * n
  n + x

def f7 (n : Nat) (i : Int) :=
  n + (n * 2 * i)

def f8 (n : Nat) (i : Int) :=
  n * 2 + (i * 1 * n * 2 * i)

def f9 [Mul α] (a : α) (as bs : Array α) : Array α :=
  a * as * bs

def f10 (a : Int) (as bs : Array Int) : Array Int :=
  2 * a * as * bs

def f11 (a : Int) (as bs : Array Int) : Array Int :=
  3 * a * as * (2 * bs)

def f12 [Mul α] (as bs : Array α) : Array α :=
  as.foldl (init := bs) fun bs a => a * bs
