namespace foo
namespace bla
open lean.parser interactive interactive.types

meta def my_exact (q : parse texpr) :=
tactic.interactive.exact q

/- Copy tactic my_exact to tactic.interactive. -/
run_cmd add_interactive [`my_exact]
end bla

example : true :=
begin
  my_exact trivial
end
end foo
