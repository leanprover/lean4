set_option linter.unusedVariables true

structure Ctx where
  s : String

def f (s : String) : ReaderT Ctx Id Unit :=
  withReader (fun ctx => { ctx with s := s }) (pure ())
