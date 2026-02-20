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

instance : Coe (Id Unit) (Id (Array Unit)) where
  coe x := Array.singleton <$> x

instance : HAndThen (Id Unit) (Id Unit) (Id Unit) where
  hAndThen p1 p2 := p1 *> (p2 ())

def nop : Id Unit :=
  pure ()

def group (_ : Id (Array Unit)) : Id Unit :=
  pure ()

def bug :=
  group (nop >> nop)
