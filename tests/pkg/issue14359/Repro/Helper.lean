module

public section

class Description (α : Type) where
  pieces : List String

def describe (α : Type) [Description α] : Option String :=
  some <| (Description.pieces α).foldl (init := "") (· ++ ·)

instance : Description Unit where
  pieces := ["un", "it"]
