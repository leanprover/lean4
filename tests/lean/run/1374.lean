import Lean

/-- My new test option -/
register_option test : Nat := {
  defValue := 10
  descr    := "testing"
}

/-- My new builtin test option -/
register_builtin_option testb : Nat := {
  defValue := 10
  descr    := "testing"
}

/-- My new simp attribute -/
register_simp_attr mysimp "my simp attr"

/-- config elab -/
declare_config_elab elabSimpConfig' Lean.Meta.Simp.Config
