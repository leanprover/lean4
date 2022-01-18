macro "foo" : term => Lean.Macro.throwError "Test Error"

#check foo
