import Lean

inductive NEList (α : Type)
  | uno  : α → NEList α
  | cons : α → NEList α → NEList α

def NEList.notUno : NEList α → Bool
  | uno  a    => true
  | cons a as => false

inductive Lambda
  | mk : (l : NEList String) → l.notUno = true → Lambda

inductive Value
  | lam  : Lambda → Value
  | nil  : Value

def State.aux (v : Value) : Bool :=
  match v with
  | .lam (.mk ns h) => true
  | v               => false

def gen : Lean.MetaM Unit := do
  discard <| Lean.Meta.Match.getEquationsForImpl ``State.aux.match_1

#eval gen
