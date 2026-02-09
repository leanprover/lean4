-- Even if there are errors in the attributes,
-- the definition should still be declared.

-- Attributes without implementation
syntax "unimplementedattr" : attr
@[unimplementedattr] def foo := 42
#check foo

-- Attributes that fail during application
def bar :=
  let rec @[class] bar : Nat := 42
  bar
#check bar
