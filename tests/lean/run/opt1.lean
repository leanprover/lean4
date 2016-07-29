vm_eval options.get_string options.mk `opt1 "<empty>"
vm_eval options.get_string (options.set_string options.mk `opt1 "val1") `opt1 "<empty>"
vm_eval if (options.mk = options.mk) then bool.tt else bool.ff
vm_eval if (options.mk = (options.set_string options.mk `opt1 "val1")) then bool.tt else bool.ff
vm_eval options.get_nat (options.set_nat options.mk `opt1 10) `opt1 0
vm_eval options.get_nat (options.set_nat options.mk `opt1 10) `opt2 0
