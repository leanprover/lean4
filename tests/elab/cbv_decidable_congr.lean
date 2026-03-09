set_option cbv.warning false
set_option trace.Meta.Tactic true
axiom P : Prop
axiom instDecidableP : Decidable P
axiom Q : Prop

axiom P_eval : P = Q
attribute [cbv_eval] P_eval
example : P = Q := by cbv

axiom hQ : Q

axiom instDecidableQ : Decidable Q
noncomputable instance : Decidable P := instDecidableP
noncomputable instance : Decidable Q := instDecidableQ
axiom dQ_eval : instDecidableQ = Decidable.isTrue hQ
attribute [cbv_eval] dQ_eval

example : (if P then true else false) = true := by cbv

example : (if P then true else false) = true := by conv => lhs; cbv

example : (if _ : P then true else false) = true := by cbv

example : P := by decide_cbv

example : decide P = true := by conv => lhs; cbv

example : Q := by decide_cbv

example : decide Q = true := by conv => lhs; cbv

example : (if Q then true else false) = true := by cbv

example : (if _ : Q then true else false) = true := by cbv
