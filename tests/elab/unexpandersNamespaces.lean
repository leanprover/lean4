namespace Foo

abbrev List (α : Type u) : Type := Unit

def List.nil {α : Type u} : List α := ()
def List.cons {α : Type u} (x : α) (xs : List α) : List α := ()

#check @List.nil Unit
#check @_root_.List.nil Unit

end Foo
