theorem foo : True := by
  exact True.intro
--^ collectDiagnostics

theorem foobar : True := True.intro
--^ collectDiagnostics

example : True := True.intro
--^ collectDiagnostics
