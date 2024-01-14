open System
open System.Platform

def norm (f : FilePath) : String :=
  f.toString.map fun c => if c == '\\' then '/' else c

#eval FilePath.isAbsolute (if isWindows then "C:\\foo" else "/foo")
#eval FilePath.isAbsolute "a/b"

#eval norm <| ("a" : FilePath) / "b"
#eval norm <| ("a" : FilePath) / "b" / "c"
#eval norm <| ("a" : FilePath) / "/b/c"

#eval norm <$> FilePath.parent "a/b"
#eval norm <$> FilePath.parent "a/b/c"
#eval norm <$> FilePath.parent "a"

#eval FilePath.fileName "a/b"

#eval FilePath.fileStem "a/b"
#eval FilePath.fileStem "a/b.tar.gz"
#eval FilePath.fileStem "a/.gitignore"

#eval norm <| FilePath.withFileName "a/b" "c"

#eval FilePath.extension "a/b"
#eval FilePath.extension "a/b.txt"
#eval FilePath.extension "a/.gitignore"

#eval norm <| FilePath.withExtension "a/b.tar.gz" "xz"
#eval norm <| FilePath.withExtension "a/b.tar.gz" ""
#eval norm <| FilePath.withExtension "a/b" "tar.gz"

#eval norm <| FilePath.addExtension "a/b.tar.gz" "bak"
