theorem f1 (a : α) (f : α → β) : f a = f a := by
  rfl

/--
info: theorem f1.{u_1, u_2} : ∀ {α : Sort u_1} {β : Sort u_2} (a : α) (f : α → β), f a = f a :=
fun {α} {β} a f => Eq.refl (f a)
-/
#guard_msgs in
#print f1

theorem f2 {α : Sort u} {β : Sort v} (a : α) (f : α → β) : f a = f a := by
  rfl

/--
info: theorem f2.{u, v} : ∀ {α : Sort u} {β : Sort v} (a : α) (f : α → β), f a = f a :=
fun {α} {β} a f => Eq.refl (f a)
-/
#guard_msgs in
#print f2

theorem f3.{u,v} {α : Sort u} {β : Sort v} (a : α) (f : α → β) : f a = f a := by
  rfl

/--
info: theorem f3.{u, v} : ∀ {α : Sort u} {β : Sort v} (a : α) (f : α → β), f a = f a :=
fun {α} {β} a f => Eq.refl (f a)
-/
#guard_msgs in
#print f3

def g (a : α) (f : α → β) : f a = f a := by
  rfl

/--
info: def g.{u_1, u_2} : ∀ {α : Sort u_1} {β : Sort u_2} (a : α) (f : α → β), f a = f a :=
fun {α} {β} a f => Eq.refl (f a)
-/
#guard_msgs in
#print g
