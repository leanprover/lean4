structure Op (α : Type _) where op : α → α → α
variable {α}
variable (s : Op α)
local infixr:60 " ∙ " => s.op
local infixr:60 " ∙1 " => s.op1 -- TODO: generate error

def x := 0

notation "x++" => x.succ
notation "x++" => x.foo  -- TODO: generate error
