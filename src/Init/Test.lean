module

public section

instance bla : LE α where
  le _ _ := True

@[instance_reducible, expose]
def blobExposed : LE α :=
  bla

@[instance_reducible]
def blobNotExposed : LE α :=
  bla

#guard_msgs in
example {a b : α} :
    (letI : LE α := blobExposed; LE.le (α := α) a b) = True := by
  simp only [LE.le]

/-- error: `simp` made no progress -/
#guard_msgs in
example {a b : α} :
    (letI : LE α := blobNotExposed; LE.le (α := α) a b) = True := by
  simp only [LE.le]
