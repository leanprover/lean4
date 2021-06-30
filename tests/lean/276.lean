universe u v

-- `Type u` version can be defined without this option, but I get the same error
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PEmpty : Sort u

-- `#check` works
set_option pp.all true in
#check fun {α : Sort v} => PEmpty.rec (fun _ => α)

-- but `def` doesn't work
-- error: (kernel) compiler failed to infer low level type, unknown declaration 'PEmpty.rec'
def PEmpty.elim {α : Sort v} := PEmpty.rec (fun _ => α)
