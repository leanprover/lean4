/-!
# Auxiliary definitions and let-variables

`Closure.mkValueTypeClosure` must not lambda abstract a let-variable whose value is needed for the
value of the auxiliary declaration to have the given type.
See https://github.com/leanprover/lean4/issues/13408
-/

example : True := by
  let E : Type := id Nat
  let hE : Inhabited E := inferInstanceAs (Inhabited Nat)
  trivial

def MyNat := Nat

example : True := by
  let n : Nat := 3
  let s : Type := Fin n
  let : Inhabited s := inferInstanceAs (Inhabited (Fin 3))
  trivial

example : True := by
  let E : Type := id MyNat
  let : Inhabited E := inferInstanceAs (Inhabited Nat)
  trivial

instance : Add MyNat := inferInstanceAs (Add Nat)

example : True := by
  let E : Type := MyNat
  let : Add E := inferInstanceAs (Add Nat)
  trivial
