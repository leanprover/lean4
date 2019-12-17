prelude
import Init.System.IO

def main : IO Unit :=
throw $ IO.Error.noFileOrDirectory "file.ext" "this is some context"
