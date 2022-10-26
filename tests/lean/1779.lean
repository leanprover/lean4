section
variable [Coe Int R] [Neg R] (a : R) (n : Int)
#check a = -n
#check a = (-n : R)
#check -n = a
#check (-n : R) = a
end

section
variable [Coe Int R] [Add R] (a : R) (n : Int)
#check a = n + n
#check a = (n + n : R)
end

section
variable [Coe Int R] [OfNat R 0] [Sub R] (a : R) (n : Int)
#check a = 0 - n
#check a = (0 - n : R)
end

section
variable [Coe Int R] [Add R] [Neg R] (a : R) (n : Int)
#check a + -n
#check a + (-n : R)
#check -n + a
#check (-n : R) + a
end
