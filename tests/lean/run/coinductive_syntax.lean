set_option trace.Elab.inductive true
--variable (α : Type)

open Lean.Order

coinductive infSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq r b → infSeq r a

def infSeq' (r : α → α → Prop) : α → Prop := infSeq r (infSeq')
  partial_fixpoint monotonicity by sorry

#check infSeq'.fixpoint_induct

/--
info: infSeq.{u_1} {α : Sort u_1} (r : α → α → Prop) (infSeq.call : {α : Sort u_1} → (α → α → Prop) → α → Prop) : α → Prop-/
--/
#guard_msgs in
#check infSeq
/--
info: infSeq.step.{u_1} {α : Sort u_1} {r : α → α → Prop} (infSeq.call : {α : Sort u_1} → (α → α → Prop) → α → Prop)   {a b : α} : r a b → infSeq.call r b → infSeq r infSeq.call a
-/
#guard_msgs in
#check infSeq.step


mutual
  coinductive Tick : Prop where
  | mk : Tock → Tick

  coinductive Tock : Prop where
  | mk : Tick → Tock
end

inductive myNat where
  | myZero : myNat
  | mySucc : myNat → myNat

#check myNat.recOn
