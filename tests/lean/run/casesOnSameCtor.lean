import Lean
open Lean Meta


inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

namespace Vec
-- set_option debug.skipKernelTC true
run_meta mkCasesOnSameCtor `Vec.casesOn2 ``Vec

/--
info: Vec.casesOn2.het.{u_1, u} {α : Type u} {motive : {a : Nat} → Vec α a → {a : Nat} → Vec α a → Sort u_1} {a✝ : Nat}
  (t : Vec α a✝) {a✝¹ : Nat} (t✝ : Vec α a✝¹) (h : t.ctorIdx = t✝.ctorIdx) (nil : motive nil nil)
  (cons :
    (a : α) →
      {n : Nat} → (a_1 : Vec α n) → (a_2 : α) → {n_1 : Nat} → (a_3 : Vec α n_1) → motive (cons a a_1) (cons a_2 a_3)) :
  motive t t✝
-/
#guard_msgs in
#check Vec.casesOn2.het

/--
info: Vec.casesOn2.{u_1, u} {α : Type u} {motive : {a : Nat} → Vec α a → Vec α a → Sort u_1} {a✝ : Nat} (t t✝ : Vec α a✝)
  (h : t.ctorIdx = t✝.ctorIdx) (nil : motive nil nil)
  (cons : (a : α) → {n : Nat} → (a_1 : Vec α n) → (a_2 : α) → (a_3 : Vec α n) → motive (cons a a_1) (cons a_2 a_3)) :
  motive t t✝
-/
#guard_msgs in
#check Vec.casesOn2

end Vec

namespace List
-- set_option debug.skipKernelTC true
-- set_option trace.compiler.ir.result true

run_meta mkCasesOnSameCtor `List.casesOn2 ``List

/--
info: List.casesOn2.{u_1, u} {α : Type u} {motive : List α → List α → Sort u_1} (t t✝ : List α) (h : t.ctorIdx = t✝.ctorIdx)
  (nil : motive [] [])
  (cons : (head : α) → (tail : List α) → (head_1 : α) → (tail_1 : List α) → motive (head :: tail) (head_1 :: tail_1)) :
  motive t t✝
-/
#guard_msgs in
#check List.casesOn2

end List

namespace BadIdx
opaque f : Nat → Nat
inductive T : (n : Nat) → Type where
  | mk1 : Fin n → T (f n)
  | mk2 : Fin (2*n) → T (f n)

run_meta mkCasesOnSameCtorHet `BadIdx.casesOn2Het ``T
/--
error: Dependent elimination failed: Failed to solve equation
  f n✝ = f n
-/
#guard_msgs in
run_meta mkCasesOnSameCtor `BadIdx.casesOn2 ``T

end BadIdx
