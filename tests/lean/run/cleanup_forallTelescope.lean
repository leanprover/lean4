import Lean

open Lean Meta

def gen (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  IO.println (← ppExpr info.type)
  IO.println "---"
  forallTelescope info.type (cleanupAnnotations := true) fun xs type => do
    let r ← mkForallFVars xs type
    IO.println (← ppExpr r)

/--
info: {coll : Type u} →
  {idx : Type v} →
    {elem : outParam (Type w)} →
      {valid : outParam (coll → idx → Prop)} →
        [self : GetElem coll idx elem valid] → (xs : coll) → (i : idx) → valid xs i → elem
---
{coll : Type u} →
  {idx : Type v} →
    {elem : Type w} →
      {valid : coll → idx → Prop} → [self : GetElem coll idx elem valid] → (xs : coll) → (i : idx) → valid xs i → elem
-/
#guard_msgs in
#eval gen ``GetElem.getElem

def f (x := 0) (_ : x = x := by rfl) : Nat := x+1


/--
info: (x : optParam Nat 0) → autoParam (x = x) _auto✝ → Nat
---
(x : Nat) → x = x → Nat
-/
#guard_msgs in
#eval gen ``f
