--

def A.x : Nat := 10
def B.x : String := "hello"
def f (a : Nat) := a + 1
def g (s : String) := s ++ " world"
open A
open B
#check f x
#check g x

macro "foo!" x:term : term => `($x + (1:Nat))
macro "foo!" x:term : term => `(Append.append $x " world")

#check f (foo! 1)
#check g (foo! "hello")

macro "bla!" : term => `((1 : Nat))
macro "bla!" : term => `("hello world")

#check f bla!
#check g bla!
