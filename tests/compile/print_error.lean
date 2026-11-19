prelude
import Init.System.IO

def main : IO Unit :=
throw $ IO.Error.noFileOrDirectory "file.ext" 13 "this is some context"
