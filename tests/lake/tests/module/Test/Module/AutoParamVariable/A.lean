module

/-! Regression test for #14708: export section-variable autoParam helpers to importing modules. -/

namespace AutoParamVariableA

variable (h : True := by trivial)

public theorem explicitPublic : h = h := rfl

public section

theorem sectionPublic : h = h := rfl

private theorem privateTheorem : h = h := rfl
