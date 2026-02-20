class F (α : Sort _) extends Inhabited α

instance : F True where
  default := trivial

def X (α β) [F α] : (α → β) → β :=
  fun f => f default

def Y (α : Sort _) : (True → α) → α :=
  X _ _
