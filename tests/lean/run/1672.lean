set_option trace.Meta.IndPredBelow true in
inductive TransClosure (r : α → α → Prop) : α → α → Prop
  | extends : r a b → TransClosure r a b
  | trans_left : r a b → TransClosure r b c → TransClosure r a c

def trans' {a b c} : TransClosure r a b → TransClosure r b c → TransClosure r a c
| .extends h₁       => .trans_left h₁
| .trans_left h₁ h₂ => .trans_left h₁ ∘ trans' h₂
