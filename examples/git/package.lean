import Lake
open Lake System

def package : PackageConfig := {
  name := "gitHello"
  dependencies := [
    {
      name := "hello",
      src := Source.git
        "https://github.com/tydeu/lean4-lake.git"
        "7a230da4073dd979ca521e81dcacdacd930c36d4"
        (branch := none)
      dir := FilePath.mk "examples" / "hello"
    }
  ]
}
