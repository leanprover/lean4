import Frontend.Main

#eval show IO _ from do
  let r ← main ["Frontend.Import1"]
  if r ≠ 0 then throw <| IO.userError "Messages were generated!"
