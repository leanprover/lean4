module

/-!
Tests reduction of `Fin.addNat?`, and of the polymorphic ranges built from it, across a module
boundary.
-/

example : ((2 : Fin 4).addNat? 1) = some 3 := by cbv

example : ((2 : Fin 3).addNat? 1) = none := by cbv

example : (1...4).toList.map (@Fin.succ 7) = (2...5).toList := by cbv

example : ((2 : Fin 4).addNat? 1) = some 3 := by decide +kernel
