module

meta import Lake.Config.Artifact

/-! Test artifact path parsing, including traversal paths reported in the review of #15870. -/

open Lake Lean

#eval show IO Unit from do
  let hash := Hash.ofNat 42
  for ext in #["", "art", "ltar", "olean.server", "olean.private", "ir.sig"] do
    let path := artifactPath hash ext
    match ArtifactDescr.ofFilePath? path with
    | .ok descr =>
      unless descr.hash == hash && descr.ext == ext do
        throw <| IO.userError s!"artifact path did not round trip: {path}"
    | .error e => throw <| IO.userError s!"valid artifact path rejected: {path}: {e}"
  for path in #[
    s!"{hash}.ltar/../../../pwn/escaped.ltar",
    s!"{hash}.ltar\\..\\..\\..\\pwn\\escaped.ltar",
    s!"{hash}.dir/file", s!"{hash}.dir\\file",
    s!"{hash}...", s!"{hash}.a..b",
    s!"../{hash}.ltar", s!"/{hash}.ltar"
  ] do
    if (ArtifactDescr.ofFilePath? path).isOk then
      throw <| IO.userError s!"unsafe artifact path accepted: {path}"
    if (fromJson? (Json.str path) : Except String ArtifactDescr).isOk then
      throw <| IO.userError s!"unsafe artifact JSON accepted: {path}"
