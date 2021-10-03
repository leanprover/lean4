import Lake
open System Lake DSL

package git_hello where
  dependencies := #[
    {
      name := `hello
      src := Source.git "https://github.com/leanprover/lake.git" "master"
      dir := FilePath.mk "examples" / "hello"
    }
  ]
