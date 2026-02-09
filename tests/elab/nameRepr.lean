#eval Lean.Name.mkStr (Lean.Name.mkNum `foo 2) "bla"
#eval `foo.bla
#eval Lean.Name.anonymous
#eval Lean.Name.mkNum Lean.Name.anonymous 11
#eval Lean.Name.mkNum `foo.bla 5
#eval Lean.Name.mkStr Lean.Name.anonymous "abc"
#eval Lean.Name.mkStr Lean.Name.anonymous "--->"
#eval Lean.Name.mkStr Lean.Name.anonymous "2"
