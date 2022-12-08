example : Nat := Id.run do
  for _ in [1:10] do
    assert! true
    if false then return 0
  return 0
