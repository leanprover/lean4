macro x:ident noWs "(" ys:term,* ")" : term => `($x $ys*)

#check id(1)

macro "foo" &"only" : tactic => `(trivial)

example : True := by foo only
