--
open num

#reduce 3+(2:num)
#reduce 3+2*(5:num)
#reduce 5*(5:num)
#reduce (eq.rec (eq.refl (2:num)) (eq.refl (2:num)) : 2 = (2:num))
