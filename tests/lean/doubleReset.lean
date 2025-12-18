set_option trace.compiler.ir.reset_reuse true in
def applyProjectionRules (projs : Array ((α × β) × γ)) (newName : γ) :
    Array ((α × β) × γ) :=
  projs.map fun proj => { proj with 2 := newName, 1.2 := proj.1.2 }
