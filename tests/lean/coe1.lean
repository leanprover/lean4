namespace hidden
#check if tt then "a" else "b"
/- Remark: in the standard library nat_to_int and int_to_real are has_lift instances
   instead of has_coe. -/
constant int  : Type
constant real : Type
constant nat_to_int  : has_coe nat int
constant int_to_real : has_coe int real
attribute [instance] nat_to_int int_to_real

constant sine : real → real
constants n m : nat
constants i j : int
constants x y : real

#check sine x
#check sine n
#check sine i

constant int_has_add  : has_add int
constant real_has_add : has_add real
attribute [instance] int_has_add real_has_add

#check x + i

/- The following one does not work because the implicit argument ?A of add is bound to int
   when x is processed. -/
#check i + x  -- FAIL

/- The workaround is to use the explicit lift -/
#check ↑i + x

#check x + n

#check n + x -- FAIL

#check ↑n + x

#check (i:real) + x
#check (n:real) + x
end hidden
