import Lean.Meta.Sym

open Lean Meta Sym

def logCongrInfo (f : Expr) : SymM Unit := do
  logInfo m!"{f} ↦ {← getCongrInfo f}"

/--
info: @HAdd.hAdd ↦ fixedPrefix 4 2
---
info: And ↦ fixedPrefix 0 2
---
info: @Eq ↦ fixedPrefix 1 2
---
info: @HEq ↦ interlaced [false, true, false, true]
---
info: @Neg.neg ↦ fixedPrefix 2 1
---
info: @Array.eraseIdx ↦ congrTheorem @Array.eraseIdx.congr_simp
---
info: @cond ↦ fixedPrefix 1 3
---
info: @ite ↦ congrTheorem @ite.congr_simp
---
info: @Eq.refl ↦ none
---
info: @congrArg ↦ none
-/
#guard_msgs in
run_meta SymM.run do
  logCongrInfo <| mkConst ``HAdd.hAdd [0, 0, 0]
  logCongrInfo <| mkConst ``And
  logCongrInfo <| mkConst ``Eq [1]
  logCongrInfo <| mkConst ``HEq [1]
  logCongrInfo <| mkConst ``Neg.neg [0]
  logCongrInfo <| mkConst ``Array.eraseIdx [0]
  logCongrInfo <| mkConst ``cond [1]
  logCongrInfo <| mkConst ``ite [1]
  logCongrInfo <| mkConst ``Eq.refl [1]
  logCongrInfo <| mkConst ``congrArg [1, 1]
