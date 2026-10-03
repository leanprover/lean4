module

/-! Regression test for #14708: autoParam helper names must be unique across modules. -/

namespace AutoParamVariableB

variable (h : True := by trivial)

public theorem explicitPublic : h = h := rfl

public section

theorem sectionPublic : h = h := rfl
