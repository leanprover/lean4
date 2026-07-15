prelude
import Init.System.IO

#eval (throw $ IO.userError "this is my error" : IO Unit)
#eval (throw $ IO.Error.noFileOrDirectory "file.ext" 31 "and details" : IO Unit)
