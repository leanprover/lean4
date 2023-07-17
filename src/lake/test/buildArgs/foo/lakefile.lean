import Lake
open Lake DSL

def configToArray (cfg? : Option String) : Array String :=
  if let some cfg := cfg? then cfg.splitOn " " |>.toArray else #[]

package foo where
  moreLeanArgs  := configToArray <| get_config? leanArgs
  weakLeanArgs  := configToArray <| get_config? weakLeanArgs
  moreLeancArgs := configToArray <| get_config? leancArgs
  moreLinkArgs  := configToArray <| get_config? linkArgs

@[default_target]
lean_exe foo
