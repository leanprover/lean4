/- Type classes -/
namespace Example

class ToString (α : Type u) where
  toString : α → String

#check @ToString.toString
-- {α : Type u_1} → [self : ToString α] → α → String

instance : ToString String where
  toString s := s

instance : ToString Bool where
  toString b := if b then "true" else "false"

#eval ToString.toString "hello"
export ToString (toString)
#eval toString true
-- "true"
-- #eval toString (true, "hello") -- Error

instance [ToString α] [ToString β] : ToString (α × β) where
  toString p := "(" ++ toString p.1 ++ ", " ++ toString p.2 ++ ")"

#eval toString (true, "hello")
-- "(true, hello)"

end Example
