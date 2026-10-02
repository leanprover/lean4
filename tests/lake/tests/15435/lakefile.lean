import Lake
open Lake DSL

package test

lean_lib Lib

lean_exe a where
  root := `A

lean_lib NeedsElided where
  needs := #[`@/a:exe]

lean_lib NeedsNamed where
  needs := #[`@test/a:exe]

lean_lib NeedsModule where
  needs := #[`+Lib:c.o.noexport]
