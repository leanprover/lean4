protected def Nat.double (x : Nat) := 2*x

namespace Ex
export Nat (double) -- Add alias Ex.double for Nat.double
end Ex

open Ex
#check Ex.double -- Ok
#check double -- Error, `Ex.double` is alias for `Nat.double` which is protected
