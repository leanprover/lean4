partial def recurseM [Monad μ] (curr: α) (action: α -> μ (List α)) : μ PUnit := do
  let children ← action curr
  children.forM (recurseM · action)

def specificTraverseList : OptionM Unit := recurseM () (fun _ => some [])

partial def recurseM2 [Monad μ] (curr: α) (action: α -> μ (Array α)) : μ PUnit := do
  let children ← action curr
  children.forM (recurseM2 · action)

def specificTraverseArray : OptionM Unit :=
  recurseM2 () (fun _ => some #[])
