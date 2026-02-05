import Lean.Server.Utils

open Lean
open Lean.Server

def buildPkgContext
    (sourceRoots : Array (VersionedPkgId × Array (Name × String)))
    (dependencies : Array (VersionedPkgId × Array VersionedPkgId))
    (ileanRoots : Array (VersionedPkgId × String)) :
    PkgContext :=
  let sourceRoots : Array (VersionedPkgId × PkgContext.PkgSourceRoots) := sourceRoots.map fun (pkg, pkgRoots) =>
    let pkgRoots := pkgRoots.map fun (name, path) => (name, System.FilePath.mk path)
    (pkg, Std.TreeMap.ofArray (cmp := Name.quickCmp) pkgRoots)
  let sourceRoots := Std.TreeMap.ofArray sourceRoots
  let dependencies := Std.TreeMap.ofArray dependencies
  let ileanRoots := Std.TreeMap.ofArray <| ileanRoots.map fun (pkg, root) => (pkg, System.FilePath.mk root)
  let env := PkgContext.Env.format sourceRoots dependencies ileanRoots
  PkgContext.Env.parse env

def c : PkgContext := buildPkgContext
  #[
    ("A_v1", #[(`A, "/A_v1/A"), (`AFoo, "/A_v1/AFoo")]),
    ("B_v1", #[(`B, "/B_v1/B")]),
    ("C_v1", #[(`C, "/C_v1/C")]),
    ("D_v1", #[(`D, "/D_v1/D")]),
    ("D_v2", #[(`D, "/D_v2/D")]),
    (.core, #[(`Init, "/core/Init"), (`Std, "/core/Std"), (`Lean, "/core/Lean"), (`Lake, "/core/Lake")])
  ]
  #[
    ("A_v1", #["B_v1", "C_v1", "D_v1", .core]),
    ("B_v1", #["D_v1", .core]),
    ("C_v1", #["D_v2", .core]),
    ("D_v1", #[.core]),
    ("D_v2", #[.core]),
    (.core, #[])
  ]
  #[
    ("A_v1", "/A_v1/ileans"),
    ("B_v1", "/B_v1/ileans"),
    ("C_v1", "/C_v1/ileans"),
    ("D_v1", "/D_v1/ileans"),
    ("D_v2", "/D_v2/ileans"),
    (.core, "/core/ileans"),
  ]

/--
info: { sourceRoots := Std.TreeMap.ofList [("A_v1",
                   Std.TreeMap.ofList [(`AFoo, FilePath.mk "/A_v1/AFoo"), (`A, FilePath.mk "/A_v1/A")]),
                  ("B_v1", Std.TreeMap.ofList [(`B, FilePath.mk "/B_v1/B")]),
                  ("C_v1", Std.TreeMap.ofList [(`C, FilePath.mk "/C_v1/C")]),
                  ("D_v1", Std.TreeMap.ofList [(`D, FilePath.mk "/D_v1/D")]),
                  ("D_v2", Std.TreeMap.ofList [(`D, FilePath.mk "/D_v2/D")]),
                  ("core",
                   Std.TreeMap.ofList [(`Init, FilePath.mk "/core/Init"),
                    (`Lean, FilePath.mk "/core/Lean"),
                    (`Lake, FilePath.mk "/core/Lake"),
                    (`Std, FilePath.mk "/core/Std")])],
  dependencies := { dependsOn := Std.TreeMap.ofList [("A_v1",
                                   Std.TreeSet.ofList ["A_v1", "B_v1", "C_v1", "D_v1", "core"]),
                                  ("B_v1", Std.TreeSet.ofList ["B_v1", "D_v1", "core"]),
                                  ("C_v1", Std.TreeSet.ofList ["C_v1", "D_v2", "core"]),
                                  ("D_v1", Std.TreeSet.ofList ["D_v1", "core"]),
                                  ("D_v2", Std.TreeSet.ofList ["D_v2", "core"]),
                                  ("core", Std.TreeSet.ofList ["core"])],
                    dependedOnBy := Std.TreeMap.ofList [("A_v1", Std.TreeSet.ofList ["A_v1"]),
                                     ("B_v1", Std.TreeSet.ofList ["A_v1", "B_v1"]),
                                     ("C_v1", Std.TreeSet.ofList ["A_v1", "C_v1"]),
                                     ("D_v1", Std.TreeSet.ofList ["A_v1", "B_v1", "D_v1"]),
                                     ("D_v2", Std.TreeSet.ofList ["C_v1", "D_v2"]),
                                     ("core", Std.TreeSet.ofList ["A_v1", "B_v1", "C_v1", "D_v1", "D_v2", "core"])] },
  ileanRoots := { roots := Std.TreeMap.ofList [("A_v1", FilePath.mk "/A_v1/ileans"),
                            ("B_v1", FilePath.mk "/B_v1/ileans"),
                            ("C_v1", FilePath.mk "/C_v1/ileans"),
                            ("D_v1", FilePath.mk "/D_v1/ileans"),
                            ("D_v2", FilePath.mk "/D_v2/ileans"),
                            ("core", FilePath.mk "/core/ileans")],
                  pkgs := Std.TreeMap.ofList [(FilePath.mk "/A_v1/ileans", "A_v1"),
                           (FilePath.mk "/B_v1/ileans", "B_v1"),
                           (FilePath.mk "/C_v1/ileans", "C_v1"),
                           (FilePath.mk "/D_v1/ileans", "D_v1"),
                           (FilePath.mk "/D_v2/ileans", "D_v2"),
                           (FilePath.mk "/core/ileans", "core")] } }
-/
#guard_msgs in
#eval c

def cases : List GlobalModId := [
  { pkg? := none, mod := `«external:file:///scratch.lean» },
  { pkg? := none, mod := `«external:untitled» },
  { pkg? := none, mod := `Foo },
  { pkg? := some .core, mod := `Lean },
  { pkg? := some .core, mod := `Init },
  { pkg? := some .core, mod := `Init.Foo },
  { pkg? := some .core, mod := `NonLean },
  { pkg? := some "A_v1", mod := `Lean },
  { pkg? := some "A_v1", mod := `A },
  { pkg? := some "A_v1", mod := `A.Foo },
  { pkg? := some "A_v1", mod := `AFoo },
  { pkg? := some "A_v1", mod := `D },
  { pkg? := some "B_v1", mod := `D },
  { pkg? := some "C_v1", mod := `D },
]

instance : ToString GlobalModId where
  toString id := s!"{id.pkg?.map toString |>.getD "none"} > {id.mod}"

def result := cases.map fun case =>
  let uri? := modToUri'? c case
  let modId? := uri?.map (uriToMod' c)
  (case, uri?, modId?)

/--
info: none > «external:file:///scratch.lean» => file:///scratch.lean => none > «external:file:///scratch.lean»
none > «external:untitled» => untitled => none > «external:untitled»
none > Foo => none => none
core > Lean => file:///core/Lean.lean => core > Lean
core > Init => file:///core/Init.lean => core > Init
core > Init.Foo => file:///core/Init/Foo.lean => core > Init.Foo
core > NonLean => none => none
A_v1 > Lean => file:///core/Lean.lean => core > Lean
A_v1 > A => file:///A_v1/A.lean => A_v1 > A
A_v1 > A.Foo => file:///A_v1/A/Foo.lean => A_v1 > A.Foo
A_v1 > AFoo => file:///A_v1/AFoo.lean => A_v1 > AFoo
A_v1 > D => file:///D_v1/D.lean => D_v1 > D
B_v1 > D => file:///D_v1/D.lean => D_v1 > D
C_v1 > D => file:///D_v2/D.lean => D_v2 > D
-/
#guard_msgs in
#eval result.map (fun (case, uri?, modId?) =>
    s!"{case} => {uri?.map toString |>.getD "none"} => {modId?.map toString |>.getD "none"}")
  |> "\n".intercalate
  |> IO.println
