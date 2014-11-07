import logic data.num
open num

constant f : num → num
constant g : num → num → num

notation A `:+1`:100000 := f A

check g 0:+1:+1 (1:+1 + 2:+1):+1

set_option pp.notation false

check g 0:+1:+1 (1:+1 + 2:+1):+1
