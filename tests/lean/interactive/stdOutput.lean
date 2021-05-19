import Lean

elab "foo" : command => IO.println "hi"
#eval "ho"
foo
