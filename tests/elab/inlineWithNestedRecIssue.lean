import Lean

@[inline] private unsafe def mapMonoMImp [Monad m] (as : Array α) (f : α → m α) : m (Array α) :=
  go 0 as
where
  @[specialize] go (i : Nat) (as : Array α) : m (Array α) := do
    if h : i < as.size then
      let a := as[i]
      let b ← f a
      if ptrEq a b then
        go (i+1) as
      else
        go (i+1) (as.set i b)
    else
      return as

set_option trace.Compiler.result true
run_meta Lean.Compiler.compile #[``mapMonoMImp, ``mapMonoMImp.go]
