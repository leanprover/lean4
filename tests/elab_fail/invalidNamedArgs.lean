
def ex1 (xs : List Nat) : Nat :=
xs.foldl (b := 0) fun sum x => sum + x

def f (a : Nat) (flag := true) : Nat :=
a + if flag then 1 else 0

def g (a : Nat) : Nat :=
f a (flg := false)


def T : Nat → Type
  | 0 => (x : Nat) → Bool
  | _  + 1 => (y : Nat) → Bool

def h : (n : Nat) → T n
  | 0 => fun x => x == 0
  | n + 1 => fun y => y == n

example := h (n := 0) (k := 7)
example := h (n := 31) (k := 7)
example := h (k := 7)
