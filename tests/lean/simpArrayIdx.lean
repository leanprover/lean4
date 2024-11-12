section
variable {α : Type _}
variable [Inhabited α]
variable (a : Array α)
variable (i j : Nat)
variable (v d : α)
variable (g : i < (a.set! i v).size)
variable (j_lt : j < (a.set! i v).size)

#check_simp (i + 0) ~> i

#check_simp (a.set! i v).get i g ~> v
#check_simp (a.set! i v).get! i ~> (a.setD i v)[i]!
#check_simp (a.set! i v).getD i d ~> if i < a.size then v else d
#check_simp (a.set! i v)[i] ~> v

-- Checks with different index values.
#check_simp (a.set! i v)[j]'j_lt  ~> (a.setD i v)[j]'_
#check_simp (a.setD i v)[j]'j_lt !~>

section
variable (p : i < a.size)
#check_tactic (a.set! i v)[i]? ~> .some v by simp[p]
end

end
