@[specialize f g h]
def f1 (f : Nat → Nat) (g : Nat → Nat) (x : Nat) :=
  f (f (g x))

@[specialize f 1 g]
def f2 (f : Nat → Nat) (g : Nat → Nat) (x : Nat) :=
  f (f (g x))

@[specialize 1 f g]
def f3 (f : Nat → Nat) (g : Nat → Nat) (x : Nat) :=
  f (f (g x))

@[specialize 0 g]
def f4 (f : Nat → Nat) (g : Nat → Nat) (x : Nat) :=
  f (f (g x))

@[specialize 10]
def f5 (f : Nat → Nat) (g : Nat → Nat) (x : Nat) :=
  f (f (g x))

@[specialize ff]
def f6 (f : Nat → Nat) (g : Nat → Nat) (x : Nat) :=
  f (f (g x))
