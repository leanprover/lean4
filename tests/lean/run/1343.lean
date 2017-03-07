universe variable u

namespace ex1
inductive foo (α : Type (u+1)) : Type (u+1)
| mk : α → foo

inductive bug
| leaf : bug
| mk   : foo bug → bug
end ex1

namespace ex2
inductive foo (α : Type u) : Type u
| mk : α → foo

inductive bug
| leaf : bug
| mk   : foo bug → bug
end ex2
