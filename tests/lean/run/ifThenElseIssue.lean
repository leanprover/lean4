-- set_option trace.Meta.isDefEq true
-- set_option trace.Elab true

def f1 (s : Nat × Bool) : Bool :=
  if s.2 then false else true

def f2 (s : Nat × Bool) : Bool :=
  if @Prod.snd _ _ s then false else true

def f3 (s : Nat × Bool) : Bool :=
  if Prod.snd s then false else true

def f4 (s : Nat × String × Bool) : Bool :=
  if s.2.2 then false else true

def sec (s : α × β) : β :=
  s.2

def f5 (s : Nat × Bool) : Bool :=
  if sec s then false else true

def f6 (s : Nat × (Bool → Bool)) : Bool :=
  if sec s true then false else true

def f7 (s : List Bool) : Bool :=
  if s.head! then false else true

def f8 (s : List Bool) : Bool :=
  if (s.map not).head! then false else true

def f9 (s : List Bool) : Bool :=
  if List.head! (s.map not) then false else true
