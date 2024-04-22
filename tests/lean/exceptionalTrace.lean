import Lean.Elab.Term

elab "rt" : term => Lean.throwMaxRecDepthAt .missing

set_option trace.Elab.step true

#check rt + 1
