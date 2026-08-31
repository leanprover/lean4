/-!
Tests a bug in the generated below/brecOn implementations for nested inductive types
Reported at https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Universes/near/525030149
-/

inductive TCTree : Type (u + 1)
  | node : (Σ (I : Type u), I → TCTree) → TCTree
