module

variable (α  : Type)

-- set_option debug.skipKernelTC true
-- set_option pp.proofs true
-- set_option trace.Elab.definition.body true

@[expose] public def foo : (l : List α) → Fin (l.length.succ)
| [] => ⟨0, Nat.zero_lt_succ _⟩
| _ :: xs =>
  let r := foo xs
  ⟨r.succ, by exact r.succ.isLt⟩
termination_by structural l => l
