-- Tests that `inferInstanceAs` auxiliary definitions are properly marked `meta`
-- when used inside a `meta` section.

module

meta section

def Foo := List Nat

instance : EmptyCollection Foo := inferInstanceAs (EmptyCollection (List Nat))

end
