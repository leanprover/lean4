set_option new_elaborator true

definition f : string → nat → nat
| "hello world" 1 := 0
| "hello world" _ := 1
| "bye"         1 := 2
| _             _ := 3

vm_eval f "hello world" 1
vm_eval f "hello world" 2
vm_eval f "bye" 1
vm_eval f "bye" 2
vm_eval f "hello" 1
