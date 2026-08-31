inductive MyBool where
| i0
| other

theorem ex (b: MyBool)
       (h: b = .i0)
: match b with | .i0 => True | _ => False
:= by
  grind
