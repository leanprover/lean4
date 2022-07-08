import Lake
open Lake DSL

package foo where
  moreLeanArgs := get_config? leanArgs |>.getD "" |>.splitOn " " |>.toArray
  moreLeancArgs := get_config? leancArgs |>.getD "" |>.splitOn " " |>.toArray

@[defaultTarget]
lean_exe foo
