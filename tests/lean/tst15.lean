universe M >= 1
universe U >= M + 1
variable x : (Type max U+1+2 M+1 M+2 3)
check x
variable f : (Type U+10) -> Type
check f
check f x
check (Type 4)
check x
check (Type max U M)
print (Type U+3)
check (Type U+3)
check (Type U ⊔ M)
check (Type U ⊔ M ⊔ 3)
print (Type U+1 ⊔ M ⊔ 3)
check (Type U+1 ⊔ M ⊔ 3)
print (Type U) -> (Type 5)
check (Type U) -> (Type 5)
check (Type M ⊔ 3) -> (Type U+5)
print (Type M ⊔ 3) -> (Type U) -> (Type 5)
check (Type M ⊔ 3) -> (Type U) -> (Type 5)
print (Type U)
