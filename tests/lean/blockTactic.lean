example (p : Prop) (h : True → True → p) : p := by
  apply h
  - trivial
  - trivial

example (p : Prop) (h : True → True → p) : p := by
  - apply h
    - trivial
    - trivial

example (p : Prop) (h : True → True → p) : p := by
  - apply h  -- should fail
  - trivial
  - trivial

example (p : Prop) (h : True → True → p) : p := by
  apply h
  - apply id
    trivial
  - apply id
    trivial

example (p : Prop) (h : False → False → p) : p := by
  apply h
  - trivial  -- should
  - trivial  -- both fail
