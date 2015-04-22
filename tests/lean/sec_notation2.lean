open nat

namespace foo

section
  section
    parameter (A : Type)
    definition f (a b : A) : A := a

    definition add2 (a : nat) : nat := a + 2

    postfix `+.2`:100 := add2

    local postfix `++2`:100 := add2

    eval 3 +.2

    example : 3 +.2 = 3 ++2 := rfl
 end

 eval 3 +.2

 example : 3 +.2 = 3 ++2 := rfl -- error

end

 eval 3 +.2
end foo

example : 3 +.2 = 5 := -- error
rfl

open foo

example : 3 +.2 = 5 := -- error
rfl
