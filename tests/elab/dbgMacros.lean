def f (x : Nat) :=
if x = 0 then panic! "unexpected zero"
else x - 1

#eval f 0

#eval f 10

def g (x : Nat) :=
if x = 0 then unreachable!
else x - 1

#eval g 0

def h (x : Nat) :=
assert! x != 0;
x - 1

#eval h 1
#eval h 0

def f2 (x : Nat) :=
dbg_trace "f2, x: {x}";
x + 1

#eval f2 10

def g2 (x : Nat) : IO Nat := do
IO.println "g2 started";
pure (x + 1)

#eval g2 10
