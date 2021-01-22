

variable {α : Type} in
def f : α → α :=
fun x => x

#check @f

variable {α : Type} {β : Type} in
variable (h : α → α) in
set_option pp.raw.maxDepth 1000 in
def g : α → β → α :=
fun x _ => h x

#check @g
