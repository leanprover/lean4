# Test that Lean will use the specified olean from `setup.json`
lean Dep.lean -o Dep.olean
lean Test.lean --setup setup.json
