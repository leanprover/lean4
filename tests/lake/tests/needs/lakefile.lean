import Lake

open System Lake DSL

package test

require dep from "dep"

lean_exe modA where
  needs := #[`+Dep.A:olean]
