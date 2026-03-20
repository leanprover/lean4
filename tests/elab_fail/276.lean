universe u v

-- `#check` works
set_option pp.all true in
#check fun {α : Sort v} => PEmpty.rec (fun _ => α)

-- but `def` doesn't work
-- error: code generator does not support recursor 'PEmpty.rec' yet
def PEmpty.elim' {α : Sort v} := PEmpty.rec (fun _ => α)
