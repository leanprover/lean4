import Lake.Config.Cache

/-! Test on-demand cache download publication for #16301. -/

open System Lake

def main (args : List String) : IO UInt32 := do
  let [url, path, contents] := args
    | throw <| IO.userError "expected URL PATH CONTENTS"
  let result ← (downloadArtifactCore (Hash.ofByteArray contents.toUTF8) url path).toBaseIO
  return if result.isSome then 0 else 1
