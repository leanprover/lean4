--

variable (y : Nat)

def f.{u} (x : Nat) : Nat := -- error unused universe parameter 'u'
x

universe u

def f.{v, w} (α : Type v) (a : α) : α := -- error unused universe parameter 'w'
a

axiom f.{w} (α : Type u) (a : α) : α  -- error unused universe parameter 'w'
