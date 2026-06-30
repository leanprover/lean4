universe u v

structure InjectiveFunction (α : Type u) (β : Type v) where
  fn  : α → β
  inj : ∀ a b, fn a = fn b → a = b

def add1 : InjectiveFunction Nat Nat where
  fn a      := a + 1
  inj a b h := by injection h

instance : CoeFun (InjectiveFunction α β) (fun _ => α → β) where
  coe s := s.fn

#guard add1 10 == 11

def mapAdd1 (xs : List Nat) : List Nat :=
  xs.map add1

#guard mapAdd1 [1, 2] = [2, 3]

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

#guard foo true 10 == 11
#guard foo false 20 == 20

#guard [1, 2, 3].map (foo true) = [2, 3, 4]
