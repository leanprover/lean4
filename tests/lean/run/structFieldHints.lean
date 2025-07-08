-- TODO: delete import
import Lean

set_option pp.rawOnError true

structure SBase where
  field1 : Nat
structure S extends SBase where
  -- `field2` depends on `field1` so must be inserted after
  field2 : Vector Nat field1
  sh : String
  longerFieldName : Bool
  field3 : Bool

-- no fields
example : S :=
  {}
example : S := {}
example : S := {

}
example : S :=
  {

  }
example : S :=
  -- VS Code's auto-formatting makes this scenario unlikely, but we test it for completeness
  {
  }
example : S := {
}
example : S := {
  -- comment in the way
}

-- one field per line, braces not separated
example : S :=
  { field1 := 0
    field2 := #v[] }

-- one field per line, braces separated
example : S :=
  {
    field1 := 31
    field3 := true
  }

-- one field per line, braces separated without initial line break
example : S := {
  field1 := 31
  field3 := true
}

-- many fields per line, braces not separated
example : S :=
  { field1 := 0, field2 := #v[] }

-- many fields per line, braces not separated, next field must go on a new line
example : S :=
  { field1 := 0, sh := "a long string value that forces this line to the maximum column length" }

-- many fields per line, braces not separated, with an existing line break
example : S :=
  { field1 := 0, sh := "a long string value that forces this line to the maximum column length",
    field2 := #v[] }

-- ambiguous styling intent
example : S :=
  { sh := "hi" }

def base : SBase :=
  ⟨0⟩

-- using `with`, many field per line
example : S :=
  { base with field3 := true, sh := "bar" }

-- using `with`, many fields per line, next field requires a break
example : S :=
  { base with sh := "a long string value that forces this line near max length", field3 := false }

-- using `with`, one field per line, no initial line break
example : S := { base with
  field1 := 0
  field3 := true
}

-- using `with`, one field per line, indented post-`with`
example : S :=
  { base with field1 := 0
              field3 := true }

-- using `with`, no fields
example : S :=
  { base with }
example : S :=
  { base with
  }
example : S := { base with
}
example : S := { base with

}

example : S := {
  base with
  field1 := 0, field2 := #v[],
  field3 := true
}

-- with type annotation
example := {
  : S
}
example := { : S }
-- FIXME: failing:
example := { : S
}
example := {
  field1 := 1
  : S
}
example :=
  { field1 := 1
    field3 := true : S }
example := { field1 := 1 : S }

-- with `with` and type annotation
example :=
  { base with : S}
example := { base with
  : S
}

-- `where` structure instance
example : S where

example : S where
  field2 := #v[42]

-- missing constrained field
example : S :=
  { field2 := #v[] }

inductive BadDepType : Nat → Type where
  | mk : BadDepType (n + 4)
structure BadDepStruct where
  n : Nat
  bdt : BadDepType n
example : BadDepStruct where
  bdt := .mk
