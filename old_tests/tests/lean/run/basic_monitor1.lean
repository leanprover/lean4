@[vm_monitor]
meta def basic_monitor : vm_monitor nat :=
{ init := 0, step := λ s, return (trace ("step " ++ to_string s)  (s+1)) >> failure }

set_option debugger true

def f : nat → nat
| 0     := 0
| (a+1) := f a

#eval trace "a" (f 4)
