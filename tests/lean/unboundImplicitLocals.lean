def myid (a : α) := a -- works

#check myid 10
#check myid true

theorem ex1 (a : α) : myid a = a := rfl

def cnst (b : β) : α → β := fun _ => b -- works

theorem ex2 (b : β) (a : α) : cnst b a = b := rfl

def Vec (α : Type) (n : Nat) := { a : Array α // a.size = n }

def mkVec : Vec α 0 := ⟨ #[], rfl ⟩

def Vec.map (xs : Vec α n) (f : α → β) : Vec α β :=
  ⟨ xs.val.map f, sorry ⟩

/- unbound implicit locals must be greek or lower case letters -/
def Vec.map2 (xs : Vec α size /- error: unknown identifier size -/) (f : α → β) : Vec α β :=
  ⟨ xs.val.map f, sorry ⟩

set_option unboundImplicitLocal false in
def Vec.map3 (xs : Vec α n) (f : α → β) : Vec α β := -- Errors, unknown identifiers 'α', 'n', 'β'
  ⟨ xs.val.map f, sorry ⟩

def double [Add α] (a : α) := a + a
