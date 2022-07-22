import Std
open Std

deriving instance TypeName for Nat
deriving instance TypeName for String

example : (Dynamic.mk 42).get? String = none := by native_decide
example : (Dynamic.mk 42).get? Nat = some 42 := by native_decide
example : (Dynamic.mk 42).typeName = ``Nat := by native_decide
