def Foo := List Nat

def test (x : Nat) : Foo :=
  [x, x+1, x+2]

#eval test 4 -- Error

#check fun (x y : Foo) => x == y -- Error

deriving instance BEq, Repr for Foo

#eval test 4

#check fun (x y : Foo) => x == y

def Boo := List (String × String)
  deriving BEq, Repr, DecidableEq

def mkBoo (s : String) : Boo :=
  [(s, s)]

#eval mkBoo "hello"

#eval mkBoo "hell" == mkBoo "hello"
#eval mkBoo "hello" == mkBoo "hello"
#eval mkBoo "hello" = mkBoo "hello"

def M := ReaderT String (StateT Nat IO)
  deriving Monad, MonadState, MonadReader

#print instMMonad

def action : M Unit := do
  modify (. + 1)
  dbg_trace "{← read}"
