/-! Tests that conv and simp apply pi_congr rather than the less general forall_congr.
    The following examples used to work only at v = 0.
-/

axiom f : Sort u → Sort v
axiom g : Sort u → Sort v
axiom fg.eq (α : Sort u) : f α = g α

example : ((x:Sort u) → f.{u,v} x) = ((x : Sort u) → g.{u,v} x) :=
  pi_congr fg.eq

example : ((x:Sort u) → f.{u,v} x) = ((x : Sort u) → g.{u,v} x) := by
  conv => lhs; ext; apply fg.eq

example : ((x:Sort u) → f.{u,v} x) = ((x : Sort u) → g.{u,v} x) := by
  simp only [fg.eq]
