import Lean.Parser.Term
/-!
# Hints for missing structure instance fields

This file tests the code action-containing hints for missing fields in structure instances. It tests
a variety of formatting styles to ensure that the generated code action adheres to the conventions
of the in-progress structure instance.
-/

structure SBase where
  field1 : Nat
structure S extends SBase where
  -- `field2` depends on `field1` so must be inserted after
  field2 : Vector Nat field1
  sh : String
  longerFieldName : Bool
  field3 : Bool

/-! ## No existing fields -/
example : S :=
  {}
--^ codeAction
example : S := {}
             --^ codeAction

example : S := {

}
--^ codeAction
example : S :=
  {

  }
--^ codeAction
example : S :=
  -- VS Code's auto-formatting makes this scenario unlikely, but we test it for completeness
  {
  }
--^ codeAction
example : S := {
}
--^ codeAction
example : S := {
  -- comment in the way
}
--^ codeAction

/-! ## One field per line, braces not separated -/
example : S :=
  { field1 := 0
    field2 := #v[] }
               --^ codeAction

/-! ## One field per line, braces separated -/
example : S :=
  {
    field1 := 31
    field3 := true
  }
--^ codeAction

/-! ## One field per line, braces separated without initial line break -/
example : S := {
  field1 := 31
  field3 := true
}
--^ codeAction

/-! ## Many fields per line, braces not separated -/
example : S :=
  { field1 := 0, field2 := #v[] }
                            --^ codeAction

/-! ## Many fields per line, braces not separated, next field must go on a new line -/
example : S :=
  { field1 := 0, sh := "a long string value that forces this line to the maximum column length" }
                                                                                            --^ codeAction

/-! ## Many fields per line, braces not separated, with an existing line break -/
example : S :=
  { field1 := 0, sh := "a long string value that forces this line to the maximum column length",
    field2 := #v[] }
               --^ codeAction

/-! ## Ambiguous styling intent -/
example : S :=
  { sh := "hi" }
           --^ codeAction

def base : SBase :=
  ⟨0⟩

/-! ## Using `with`, many fields per line -/
example : S :=
  { base with field3 := true, sh := "bar" }
                                      --^ codeAction

/-! ## Using `with`, many fields per line, next field requires a break -/
example : S :=
  { base with sh := "a long string value that forces this line near max length", field3 := false }
                                                                                             --^ codeAction

/-! ## Using `with`, one field per line, no initial line break -/
example : S := { base with
  field1 := 0
  field3 := true
}
--^ codeAction

/-! ## Using `with`, one field per line, indented post-`with` -/
example : S :=
  { base with field1 := 0
              field3 := true }
                         --^ codeAction

/-! ## Using `with`, no fields -/
example : S :=
  { base with }
          --^ codeAction
example : S :=
  { base with
  }
--^ codeAction
example : S := { base with
}
--^ codeAction
example : S := { base with

}
--^ codeAction

/-! ## `with` at same indentation as fields -/
example : S := {
  base with
  field1 := 0, field2 := #v[],
  field3 := true
}
--^ codeAction

/-! ## With type annotation -/
example := {
  : S
}
--^ codeAction
example := { : S }
          --^ codeAction
example := { : S
}
--^ codeAction
example := {
  field1 := 1
  : S
}
--^ codeAction
example :=
  { field1 := 1
    field3 := true : S }
               --^ codeAction
example := { field1 := 1 : S }
                     --^ codeAction

/-! ## `with` and type annotation -/
example :=
  { base with : S}
          --^ codeAction
example := { base with
  : S
}
--^ codeAction
example := { base with : S

}
--^ codeAction

/-! ## Missing constrained field -/
example : S :=
  { field2 := #v[] }
               --^ codeAction

/-! ## Missing constrained but not fully determined field -/
inductive BadDepType : Nat → Type where
  | mk : BadDepType (n + 4)
structure BadDepStruct where
  n : Nat
  bdt : BadDepType n
example : BadDepStruct :=
  { bdt := .mk }
           --^ codeAction

/-! ## Multi-byte characters in indentation offset -/
def números : Nat × Nat := {}
                         --^ codeAction
def números' : Nat × Nat := { fst := 23 }
                                    --^ codeAction


/-! ## Inapplicable syntax -/

-- TODO: eventually, we'd like to support `where`
example : S where
              --^ codeAction

example : S where
  field2 := #v[42]
               --^ codeAction

section
local macro "a_structure_with" args:(ident "equal_to" term "in_addition_to"?)* : term => do
  let fields ← args.raw.mapM fun a =>
    `(Lean.Parser.Term.structInstField | $(Lean.mkIdent a[0].getId):ident := $(.mk a[2]))
  `({ $[$fields]* })

example : S :=
  a_structure_with field1 equal_to 3 in_addition_to sh equal_to "Hello"
                                                                    --^ codeAction
end
