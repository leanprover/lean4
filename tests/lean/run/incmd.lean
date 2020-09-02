new_frontend

variable {α : Type} in
def f : α → α :=
fun x => x

#check @f

variables {α : Type} {β : Type} in
variable (h : α → α) in
set_option syntaxMaxDepth 1000 in
def g : α → β → α :=
fun x _ => h x

#check @g
