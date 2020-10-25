

mutual

inductive Foo.Lst (α : Type)
| nil   : Lst
| cons  : Tree α → Lst α → Lst α

inductive Boo.Tree (α : Type) -- conflicting namespace
| leaf : Tree α
| node : Lst α → Tree α

end

mutual

inductive Foo.Lst (α : Type)
| nil   : Lst α
| cons  : Tree α → Lst α → Lst α

inductive Foo.Tree (α : Type)
| leaf : Tree α
| node : Lst α → Tree α

end
