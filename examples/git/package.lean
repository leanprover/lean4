import Lake.Package

open Lake System

def package : PackageConfig := {
  name := "gitHello"
  version := "1.0"
  dependencies := [
    {
      name := "hello",
      src := Source.git
        "https://github.com/tydeu/lean4-lake.git"
        "71defa066dd845a31d19547f1a3e01f79c5fc8d9"
        (branch := none)
      dir := FilePath.mk "examples" / "hello"
    }
  ]
}
