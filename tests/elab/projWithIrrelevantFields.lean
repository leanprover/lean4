structure S (α : Type) where
  a : Nat
  b : Nat
  nothing : Nonempty α

def f {α : Type} (s : S α) : Nat := s.a

def g {α : Type} (s : S α) : Nat :=
  match s with
  | .mk _ b _ => b

structure T (α : Type) where
  b : Nat
  nothing : Nonempty α

def h {α : Type} (s : S α) : T α :=
  match s with
  | .mk _ b nothing => { b, nothing }

