#check
 let t := to_fmt "foo" in
 format.to_string t options.mk

#check
 let t := to_fmt "foo" in
 t.to_string

#check
 let t := to_fmt "foo" in
 t.to_string options.mk

variable t : format

set_option pp.all true
#check t.to_string options.mk
