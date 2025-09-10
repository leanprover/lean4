-- set_option trace.Elab.inductive true
-- set_option trace.Elab.definition false
-- set_option trace.Elab.definition.partialFixpoint false
set_option trace.Meta.SumOfProducts true
open Lean.Order
section
variable (α : Type)

coinductive infSeq (r : α → α → Prop): α → Prop where
  | step : r a b → infSeq r b → infSeq r a

#check infSeq

#check infSeq_functor.sop


#check infSeq.coinduct


#check infSeq.step
end

mutual
  coinductive tick : Prop where
  | mk : tock → tick

  coinductive tock : Prop where
  | mk : tick → tock
end

/-- info: tick.mk : tock → tick -/
#guard_msgs in
#check tick.mk

/-- info: tock_functor (tick_functor.call tock_functor.call : Prop) : Prop -/
#guard_msgs in
#check tock_functor
