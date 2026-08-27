--

def f1 :=
if h:x then 1 else 0

set_option pp.macroStack true
def f2 :=
if h:(x > 0) then 1 else 0


def x := <- get

macro "foo!" x:term:max : term => `(let x := "hello"; $x + x)
macro "bla!" x:term:max : term => `(fun (x : Nat) => if foo! ($x + x) < 1 then true else false)

def f (x : Nat) :=
bla! x
