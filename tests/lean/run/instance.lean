/-! `instance` cannot be used recursively. -/

/--
@ +2:2...3
error: Invalid recursive use of `instance`

Hint: Consider using a separate `def` to define the implementation of this instance.
-/
#guard_msgs (positions := true) in
instance i : Repr Nat :=
  i

/--
error: cannot use `instance` in `mutual` block

Hint: You can use `mutual` `defs` to define the code of this instance, followed by non-mutual `instance … := ` commands to register it as an instance.
-/
#guard_msgs in
mutual
instance i1 : Repr Nat := i2
instance i2 : Repr Nat := i1
end
