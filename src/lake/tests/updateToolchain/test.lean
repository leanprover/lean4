import Lake.Util.Version

open Lake

def checkParse (tc : String) :=
  IO.println <| repr <| ToolchainVer.ofString tc

def checkLt (tc1 tc2 : String) :=
  IO.println <| decide <| ToolchainVer.ofString tc1 < ToolchainVer.ofString tc2

def test := do
  IO.println ""
  checkParse "leanprover/lean4:v4.13.0-rc1"
  checkParse "leanprover/lean4:nightly-2024-09-15"
  checkParse "leanprover/lean4-pr-releases:pr-release-101"
  checkParse "leanprover/lean:v4.1.0"
  checkParse "4.12.0"
  checkLt "4.6.0-rc1" "v4.6.0"
  checkLt "4.12.0" "leanprover/lean4:v4.13.0-rc1"
  checkLt "nightly-2024-09-08" "nightly-2024-10-09"
  checkLt "nightly-2024-09-08" "4.0.0"

/--
info:
Lake.ToolchainVer.release { toSemVerCore := { major := 4, minor := 13, patch := 0 }, specialDescr := "rc1" }
Lake.ToolchainVer.nightly { year := 2024, month := 9, day := 15 }
Lake.ToolchainVer.pr 101
Lake.ToolchainVer.other "leanprover/lean:v4.1.0"
Lake.ToolchainVer.release { toSemVerCore := { major := 4, minor := 12, patch := 0 }, specialDescr := "" }
true
true
true
false
-/
#guard_msgs in #eval test
