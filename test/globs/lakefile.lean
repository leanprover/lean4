import Lake

open Lake DSL

package test

@[default_target]
lean_lib Test {
  globs := #[.submodules "Test"]
}
