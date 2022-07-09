set_option linter.all true

structure Ctx where
  s : String

def f (s : String) : ReaderT Ctx Id Unit :=
  withReader (fun ctx => { ctx with s := s }) (pure ())
