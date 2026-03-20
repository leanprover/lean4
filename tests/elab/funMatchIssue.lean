inductive T : Type 1 :=
| mkT : (forall {a : Type}, a -> a) -> T

open T

-- Works
def makeT (f : forall {a : Type}, a -> a) : T :=
  mkT f

def makeT' : (forall {a : Type}, a -> a) -> T :=
fun x =>
  let f := @x
  mkT f

def makeT'' : (forall {a : Type}, a -> a) -> T
| f => mkT f
