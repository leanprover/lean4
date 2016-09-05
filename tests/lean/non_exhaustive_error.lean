set_option new_elaborator true

definition f : string → nat → bool
| "hello world" 1 := tt
| "bye"         _ := tt
