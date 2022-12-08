universe u v

-- `#check` works
set_option pp.all true in
#check fun {α : Sort v} => PEmpty.rec (fun _ => α)

-- but `def` doesn't work
-- error: (kernel) compiler failed to infer low level type, unknown declaration 'PEmpty.rec'
def PEmpty.elim {α : Sort v} := PEmpty.rec (fun _ => α)
