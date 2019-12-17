prelude
import Init.System.IO

#eval (throw $ IO.userError "this is my error" : IO Unit)
#eval (throw $ IO.Error.noFileOrDirectory "file.ext" "and details" : IO Unit)
