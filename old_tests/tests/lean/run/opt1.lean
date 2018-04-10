#eval options.get_string options.mk `opt1 "<empty>"
#eval options.get_string (options.set_string options.mk `opt1 "val1") `opt1 "<empty>"
#eval if (options.mk = options.mk) then bool.tt else bool.ff
#eval if (options.mk = (options.set_string options.mk `opt1 "val1")) then bool.tt else bool.ff
#eval options.get_nat (options.set_nat options.mk `opt1 10) `opt1 0
#eval options.get_nat (options.set_nat options.mk `opt1 10) `opt2 0
