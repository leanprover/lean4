module

/-- A definition whose body lives in `Basic.private.lean`. -/
public def f (n : Nat) : Nat

public theorem f_pos (n : Nat) : 0 < f n

public theorem f_succ (n : Nat) : f (n + 1) = f n + 1

@[expose] public def g (n : Nat) : Nat := f n + 1

public theorem g_pos (n : Nat) : 1 < g n := by
  have := f_pos n
  unfold g
  omega

/-- Universe-polymorphic and with instance arguments. -/
public def h {α : Type u} [Inhabited α] (xs : List α) : α

section
variable (k : Nat)
/-- Declared in a section with variables; `k` is included because the signature mentions it. -/
public def addK (n : Fin k) : Nat
end

def privHelper : Nat := 3
