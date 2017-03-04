inductive term : Type
| var  : nat → term
| app  : list term → term
| cnst : string → term

meta def term.to_string : term → string
| (term.var x)  := "v#" ++ to_string x
| (term.app ts) := "(app " ++ to_string (list.map term.to_string ts) ++ ")"
| (term.cnst c) := c

meta instance : has_to_string term :=
⟨term.to_string⟩

set_option trace.compiler.preprocess true

def var_of : term → list term
| (term.app (t::ts)) := ts
| _                  := [term.app []]

def tst : list term :=
var_of (term.app [term.var 0, term.var 1, term.var 2, term.app [term.cnst "x"]])

vm_eval tst
