inductive A where
  | a

inductive B : A → Type where
  | b : B A.a

inductive C : B a → Type where
  | c : C B.b

inductive D : C b → Type where
  | d : D C.c

def f (d : D c) : Bool :=
  true

set_option pp.explicit true
#print f
