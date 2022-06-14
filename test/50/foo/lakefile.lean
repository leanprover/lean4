import Lake
open Lake DSL

package foo where
  moreLeanArgs := #[(__args__).get! 0]
  moreLeancArgs := #[(__args__).get! 1]

@[defaultTarget]
lean_exe foo
