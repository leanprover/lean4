variable {α} (op : α → α → α)
local infixr:60 " ∙ " => op
example (x y : α) : x ∙ y = y ∙ x := sorry

infixr:60 " *** " => op -- Error, only local notation can reference section variables
