universe u v

structure InjectiveFunction (α : Type u) (β : Type v) where
  fn  : α → β
  inj : ∀ a b, fn a = fn b → a = b

def add1 : InjectiveFunction Nat Nat where
  fn a      := a + 1
  inj a b h := by injection h; assumption

instance : CoeFun (InjectiveFunction α β) (fun _ => α → β) where
  coe s := s.fn

#eval add1 10

def mapAdd1 (xs : List Nat) : List Nat :=
  xs.map add1

#eval mapAdd1 [1, 2]

def foo : InjectiveFunction Bool (Nat → Nat) where
  fn
   | true,  a => a + 1
   | false, a => a
  inj a b h := by
    cases a
    cases b; rfl; injection (congrFun h 0)
    cases b; injection (congrFun h 0); rfl

theorem ex1 (x : Nat) : foo true x = x + 1 :=
  rfl

theorem ex2 (x : Nat) : foo false x = x :=
  rfl

#eval foo true 10
#eval foo false 20

#eval [1, 2, 3].map (foo true)
