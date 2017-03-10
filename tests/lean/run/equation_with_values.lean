def f : char → nat
| #"a" := 0
| #"b" := 1
| #"c" := 2
| #"d" := 3
| #"e" := 4
| _    := 5

#check f.equations._eqn_1
#check f.equations._eqn_2
#check f.equations._eqn_3
#check f.equations._eqn_4
#check f.equations._eqn_5
#check f.equations._eqn_6

def g : nat → nat
| 100000 := 0
| 200000 := 1
| 300000 := 2
| 400000 := 3
| _      := 5

#check g.equations._eqn_1
#check g.equations._eqn_2
#check g.equations._eqn_3
#check g.equations._eqn_4
#check g.equations._eqn_5

def h : string → nat
| "hello" := 0
| "world" := 1
| "bla"   := 2
| "boo"   := 3
| _       := 5

#check h.equations._eqn_1
#check h.equations._eqn_2
#check h.equations._eqn_3
#check h.equations._eqn_4
#check h.equations._eqn_5

def r : string × string → nat
| ("hello", "world") := 0
| ("world", "hello") := 1
| _                  := 2

#check r.equations._eqn_1
#check r.equations._eqn_2
#check r.equations._eqn_3
#check r.equations._eqn_4
#check r.equations._eqn_5
