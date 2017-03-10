meta def basic_monitor : vm_monitor nat :=
{ init := 0, step := λ s, return (trace ("step " ++ s^.to_string)  (s+1)) }

run_cmd vm_monitor.register `basic_monitor

set_option debugger true

example (a b : Prop) : a → b → a ∧ b :=
begin
  intros,
  constructor,
  assumption,
  assumption
end
