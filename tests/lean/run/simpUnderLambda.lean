import Lean
/-!
Tests for `simp -underlambda`

(Not using #check_simp because it does not support simp arguments)
-/

opaque P : {α : Type} → α → Prop

-- Like sorry, but no warning
axiom abort {α : Prop} : α
macro "abort" : tactic => `(tactic |exact abort)

/-- info: ⊢ P fun x => x -/
#guard_msgs in
example : P (fun (x : Nat) => id x) := by
  simp; trace_state; abort

/-- info: ⊢ P fun x => id x -/
#guard_msgs in
example : P (id (fun (x : Nat) => id x)) :=
  by simp -underLambda; trace_state; abort

/--
info: o : Option Nat
⊢ P
    (match o with
    | some val => id true
    | none => id false)
-/
#guard_msgs in
example (o : Option Nat) : P (id (match id o with | some _ => id true | none => id false)) := by
  simp -underLambda; trace_state; abort

/--
info: b : Bool
⊢ P (if b = true then id 5 else id 6)
-/
#guard_msgs in
example (b : Bool) : P (id (if id b then id 5 else id 6)) := by
  simp -underLambda; trace_state; abort

/--
info: b : Bool
⊢ P (if b = true then id 5 else id 6)
-/
#guard_msgs in
example (b : Bool) : P (id (if id b then id 5 else id 6)) := by
  dsimp -underLambda; trace_state; abort

/--
info: b : Bool
g : {b : Bool} → b = true → Nat
⊢ P (if h : b = true then id (g h) else id 7)
-/
#guard_msgs in
set_option pp.proofs true in
example (b : Bool) (g : {b : Bool} → b = true → Nat) :
    P (id (if h : b then id (g h) else id 7)) := by
  simp -underLambda; trace_state; abort


/--
info: xs : List Nat
⊢ P (List.map (fun x => 0 + x) xs)
-/
#guard_msgs in
example (xs : List Nat) :
    P (id (xs.map (fun x => 0 + x))) := by
  simp -underLambda; trace_state; abort

-- The following rewrite works because
-- List.map_id_fun
-- applies definitionally

/--
info: xs : List Nat
⊢ P (id xs)
-/
#guard_msgs in
example (xs : List Nat) :
    P (xs.map (fun x => id x)) := by
  simp -underLambda only [List.map_id_fun]; trace_state; abort


attribute [congr] List.map_congr_left

/--
info: xs : List Nat
⊢ P (List.map (fun x => 0 + x) xs)
-/
#guard_msgs in
example (xs : List Nat) :
    P (id (xs.map (fun x => 0 + x))) := by
  simp -underLambda; trace_state; abort
