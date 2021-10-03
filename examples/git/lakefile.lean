import Lake
open System Lake DSL

package where
  name := "gitHello"
  dependencies := #[
    {
      name := "hello",
      src := Source.git
        "https://github.com/tydeu/lean4-lake.git" "master"
      dir := FilePath.mk "examples" / "hello"
    }
  ]
