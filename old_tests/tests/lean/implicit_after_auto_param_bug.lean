meta def default_f_lt := `[apply has_lt.lt]

def f (α : Type) (lt : α → α → Prop . default_f_lt) [decidable_rel lt] : Type :=
α

example : id (f nat) = nat :=
rfl

example : f nat = nat :=
rfl

def mk {α : Type} (a : α) (lt : α → α → Prop . default_f_lt) [decidable_rel lt] : f α lt :=
a

def f.to_val {α : Type} {lt : α → α → Prop} {h : decidable_rel lt} (v : @f α lt h) : α :=
v

instance repr_f (α : Type) (lt : α → α → Prop) (d : decidable_rel lt) [has_repr α] : has_repr (@f α lt d) :=
⟨λ a : α, repr a⟩

#check f nat

#check id (f nat)

#check mk 1

#check (mk 1).to_val

#eval f.to_val (mk 1)

#eval mk 1

#eval id (mk 1)
