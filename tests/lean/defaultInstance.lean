class Foo (α β : Type) :=
  (f : α → β)

export Foo (f)

@[default_instance]
instance : Foo Nat Nat := {
  f := id
}

@[default_instance]
instance : Foo String String := {
  f := id
}

def g (x : Nat) := f x -- works

def h (x : String) := f x -- works

def r (x : Bool) := f x -- error

def r [Foo Bool Nat] (x : Bool) := f x -- error

def r [Foo Bool Nat] (x : Bool) := (f x : Nat) -- works
