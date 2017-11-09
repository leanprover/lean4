variable R : Type
variable [ring R]

example : -(-(1:R)) = 1 :=
begin
  trace_state,
  exact neg_neg 1,
end

#check - -(1:R)
