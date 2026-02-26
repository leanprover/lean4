module

/-! Used to crash in codegen -/

mutual
public inductive B where
  | bar
end

/-! Used to declare a private ctor. -/
mutual
public inductive Term where
  | A (args : List Term)
end

/-- info: constructor Term.A : List Term → Term -/
#guard_msgs in
#print Term.A
