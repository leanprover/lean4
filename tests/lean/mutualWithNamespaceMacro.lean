new_frontend

mutual

inductive Foo.Lst (α : Type)
| nil   : Lst
| cons  : Tree → Lst → Lst

inductive Boo.Tree (α : Type) -- conflicting namespace
| leaf : Tree
| node : Lst → Tree

end

mutual

inductive Foo.Lst (α : Type)
| nil   : Lst
| cons  : Tree → Lst → Lst

inductive Foo.Tree (α : Type)
| leaf : Tree
| node : Lst → Tree

end
