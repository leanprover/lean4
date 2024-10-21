import Lean.Meta.Basic

inductive StructLike α where
  | mk : α → StructLike α

inductive Nested where
  | nest : StructLike Nested → Nested
  | other

/--
info: theorem Nested.nest.sizeOf_spec : ∀ (a : StructLike Nested), sizeOf (Nested.nest a) = 1 + sizeOf a :=
fun a => Eq.refl (1 + sizeOf a)
-/
#guard_msgs in
#print Nested.nest.sizeOf_spec

/-- info: StructLike -/
#guard_msgs in
open Lean Meta in
run_meta do
  let i ← getConstInfoRec ``Nested.rec_1
  logInfo m!"{i.getMajorInduct}"

theorem works (x : StructLike Nested) : StructLike.rec
  (motive := fun _ => Bool)
  (mk := fun _ => true)
  x = true
  := rfl

theorem failed_before (x : StructLike Nested) : Nested.rec_1
  (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool)
  (nest := fun _ _ => true)
  (other := true)
  (mk := fun _ _ => true)
  x = true
  := rfl


-- The original surface bug

inductive Set (α : Type u) where
  | mk (l : List α)

inductive Value where
  | prim
  | set (s : Set Value)

instance : DecidableEq Value := sorry

mutual

def Value.lt : Value → Value → Bool
  | .prim, .prim => false
  | .set (.mk vs₁), .set (.mk vs₂) => Values.lt vs₁ vs₂
  | .prim, .set _ => true
  | .set _, .prim => false

def Values.lt : List Value → List Value → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | v₁ :: vs₁, v₂ :: vs₂ => Value.lt v₁ v₂ || (v₁ = v₂ && Values.lt vs₁ vs₂)

end

theorem Value.lt_irrefl (v : Value) :
  ¬ Value.lt v v
:= by
  cases v
  case set a =>
    show ¬Values.lt a.1 a.1 = true
    sorry
  all_goals sorry
