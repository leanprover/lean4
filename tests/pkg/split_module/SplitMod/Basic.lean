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

section
variable {β : Type _} (q : β → Prop) (hq : ∀ b, q b)
include hq

/-- Auto-bound universe and `include`d section variable. -/
public theorem allQ (b : β) : q b
end

/-- Proved by well-founded recursion in the private file. -/
public theorem addZero (n : Nat) : n + 0 = n

section
variable {γ : Type _} [Inhabited γ] (pick : γ → γ)

/-- Section variables, including an anonymous instance, are matched by typeless implementations. -/
public theorem pickTwice (x : γ) (h : pick x = x) : pick (pick x) = x
end

/-- Implicit parameters are inserted before explicit binders of typeless implementations. -/
public theorem eqSymm {a b : Nat} (h : a = b) : b = a
