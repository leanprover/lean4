mutual

inductive Foo.Lst (α : Type)
| nil   : Foo.Lst α
| cons  : Boo.Tree α → Foo.Lst α → Foo.Lst α

inductive Boo.Tree (α : Type)
| leaf : Boo.Tree α
| node : Foo.Lst α → Boo.Tree α

end
