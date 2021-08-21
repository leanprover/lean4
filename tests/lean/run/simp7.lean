def f (x : α) := x

theorem ex1 (a : α) (b : List α) : f (a::b = []) = False :=
  by simp [f]

def length : List α → Nat
  | []    => 0
  | a::as => length as + 1

theorem ex2 (a b c : α) (as : List α) : length (a :: b :: as) > length as := by
  simp [length]
  apply Nat.lt.step
  apply Nat.lt_succ_self

def fact : Nat → Nat
  | 0 => 1
  | x+1 => (x+1) * fact x

theorem ex3 : fact x > 0 := by
  induction x with
  | zero => decide
  | succ x ih =>
    simp [fact]
    apply Nat.mul_pos
    apply Nat.zero_lt_succ
    apply ih

def head [Inhabited α] : List α → α
  | []   => arbitrary
  | a::_ => a

theorem ex4 [Inhabited α] (a : α) (as : List α) : head (a::as) = a :=
  by simp [head]

def foo := 10

theorem ex5 (x : Nat) : foo + x = 10 + x := by
  simp [foo]
  done

def g (x : Nat) : Nat := do
  let x := x
  return x

theorem ex6 : g x = x := by
  simp [g, bind, pure]

def f1 : StateM Nat Unit := do
  modify fun x => g x

def f2 : StateM Nat Unit := do
  let s ← get
  set <| g s

theorem ex7 : f1 = f2 := by
  simp [f1, f2, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

def h (x : Nat) : Sum (Nat × Nat) Nat := Sum.inl (x, x)

def bla (x : Nat) :=
  match h x with
  | Sum.inl (y, z) => y + z
  | Sum.inr _ => 0

theorem ex8 (x : Nat) : bla x = x + x := by
  simp [bla, h]
