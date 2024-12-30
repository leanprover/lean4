import Lean

/--
info: Vector.extract.hcongr_5.{u_1} (α α' : Type u_1) (e_1 : α = α') (n n' : Nat) (e_2 : n = n') (v : Vector α n)
  (v' : Vector α' n') (e_3 : HEq v v') (start start' : Nat) (e_4 : start = start') (stop stop' : Nat)
  (e_5 : stop = stop') : HEq (v.extract start stop) (v'.extract start' stop')
-/
#guard_msgs in
#check Vector.extract.hcongr_5

/--
info: Vector.extract.congr_simp.{u_1} {α : Type u_1} {n : Nat} (v v✝ : Vector α n) (e_v : v = v✝) (start stop : Nat) :
  v.extract start stop = v✝.extract start stop
-/
#guard_msgs in
#check Vector.extract.congr_simp

open Lean Meta

/--
info: @Vector.extract.congr_simp
-/
#guard_msgs in
run_meta do
  let some thm1 ← mkCongrSimpForConst? ``Vector.extract [0] | unreachable!
  IO.println (← ppExpr thm1.proof)
  let some thm2 ← mkCongrSimp? (mkConst ``Vector.extract [0]) | unreachable!
  assert! thm1.type == thm2.type
  assert! thm1.argKinds == thm2.argKinds

/--
info: Vector.extract.hcongr_5
-/
#guard_msgs in
run_meta do
  let some thm1 ← mkHCongrWithArityForConst? ``Vector.extract [0] 5 | unreachable!
  IO.println (← ppExpr thm1.proof)
  let thm2 ← mkHCongrWithArity (mkConst ``Vector.extract [0]) 5
  assert! thm1.type == thm2.type
  assert! thm1.argKinds == thm2.argKinds
