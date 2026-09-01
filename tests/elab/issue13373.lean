module

-- Issue #13373: SizeOf derivation fails for public inductive with private constructor
public inductive Tag where
  | provided
  | private external

/-- info: Tag.provided.sizeOf_spec : sizeOf Tag.provided = 1 -/
#guard_msgs in
#check @Tag.provided.sizeOf_spec
