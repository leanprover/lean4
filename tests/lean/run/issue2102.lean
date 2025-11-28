set_option linter.unusedVariables false

-- works

def g' (T : Type) (ls : List T) : (Option (List T)) :=
  match ls with
  | _::tl =>
      let res := Option.attach (g' T tl)
      res.bind fun x => x.val
  | [] => .none

-- didn't work

def g'' (T : Type) (ls : List T) : (Option (List T)) :=
  match ls with
  | _::tl =>
      let res := Option.attach (g'' T tl)
      res.bind fun ⟨x,h⟩ => x
  | [] => .none

def g''' (T : Type) (ls : List T) : (Option (List T)) :=
  match ls with
  | _::tl =>
      let res := Option.attach (g''' T tl)
      res.bind fun ⟨x,h⟩ => x
  | [] => .none
termination_by sizeOf ls
