module

public import SimpModuleIndex.M

-- `M` is imported at the exported level, whose index contains only `m_zero`
example : SMI.m 0 = 2 := by simp
example : SMI.m 1 = 3 := by
  fail_if_success simp
  rfl
