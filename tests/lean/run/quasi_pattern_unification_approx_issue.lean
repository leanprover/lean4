

variable {δ σ : Type}

def foo0 : StateT δ (StateT σ Id) σ :=
getThe σ

def foo1 : StateT δ (StateT σ Id) σ :=
monadLift (get : StateT σ Id σ)

def foo2 : StateT δ (StateT σ Id) σ := do
let s : σ  ← monadLift (get : StateT σ Id σ)
pure s
