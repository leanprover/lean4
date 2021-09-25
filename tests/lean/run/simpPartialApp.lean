variable {U V}

def f : (U → V) → (U → U) := sorry
def add  {U} : U → U → U := sorry

@[simp] theorem foo  (u : U) : f (add u) = id := sorry

def bar (u v : U) : f (add u) v =  id v := by
  simp
