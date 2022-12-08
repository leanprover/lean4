def f : IO Unit :=
  (do IO.println "case 1"; throw (IO.userError "failed"))
  <|>
  (do IO.println "case 2"; throw (IO.userError "failed"))
  <|>
  (do IO.println "case 3")
  <|>
  (let x := dbg_trace "hello"; 1
   IO.println x)

#eval f -- should not print hello
