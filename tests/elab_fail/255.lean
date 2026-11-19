def x := 1

section
  variable (α : Type)
  variable (x : α)
  notation "A" => id x
  #check A
  theorem test : A = A := rfl

  section
    variable (x : Nat)
    #check A  -- should use shadowed `x`
  end
end

#check A  -- escaping section variable, should fail

section
  variable (x : Nat)
  #check A  -- should fail
end
