import Lake
open System Lake DSL

package where
  name := "gitHello"
  dependencies := #[
    {
      name := "hello"
      src := Source.git "https://github.com/leanprover/lake.git" "master"
      dir := FilePath.mk "examples" / "hello"
    }
  ]
