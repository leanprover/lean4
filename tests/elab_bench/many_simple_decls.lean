import Lean
open Lean Elab Command

/-!
This is a regression test for universe linter performance and in general a benchmark for through
putting a lot of small and simple definitions quickly.
-/

elab "defs " n:num : command => do
  for i in [0:n.getNat] do
    elabCommand (← `(def $(mkIdent (.mkSimple s!"d{i}")) : Nat := $(quote i)))

set_option linter.checkUnivs true
defs 3000
