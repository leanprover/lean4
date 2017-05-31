/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.toml system.io

namespace leanpkg

inductive source
| path (dir_name : string) : source
| git (url rev : string) : source

namespace source

def from_toml (v : toml.value) : option source :=
(do toml.value.str dir_name ← v.lookup "path" | none,
    return $ path dir_name) <|>
(do toml.value.str url ← v.lookup "git" | none,
    toml.value.str rev ← (v.lookup "rev") | none,
    return $ git url rev) <|>
(do toml.value.str url ← v.lookup "git" | none,
    return $ git url "master")

def to_toml : ∀ (s : source), toml.value
| (path dir_name) := toml.value.table [("path", toml.value.str dir_name)]
| (git url "master") :=
  toml.value.table [("git", toml.value.str url)]
| (git url rev) :=
  toml.value.table [("git", toml.value.str url), ("rev", toml.value.str rev)]

instance : has_to_string source :=
⟨λ s, s.to_toml.to_string⟩

end source

structure dependency :=
(name : string) (src : source)

namespace dependency
instance : has_to_string dependency :=
⟨λ d, d.name ++ " = " ++ to_string d.src⟩
end dependency

structure manifest :=
(name : string) (version : string)
(timeout : option nat := none)
(path : option string := none)
(dependencies : list dependency := [])

namespace manifest

def effective_path (m : manifest) : list string :=
[match m.path with some p := p | none := "." end]

def from_toml (t : toml.value) : option manifest := do
pkg ← t.lookup "package",
toml.value.str n ← pkg.lookup "name" | none,
toml.value.str ver ← pkg.lookup "version" | none,
tm ← match pkg.lookup "timeout" with
     | some (toml.value.nat timeout) := some (some timeout)
     | none := some none
     | _ := none
     end,
path ← match pkg.lookup "path" with
       | some (toml.value.str path) := some (some path)
       | none := some none
       | _ := none
       end,
toml.value.table deps ← t.lookup "dependencies" <|> some (toml.value.table []) | none,
deps ← monad.for deps (λ ⟨n, src⟩, do src ← source.from_toml src,
                                      return $ dependency.mk n src),
return { name := n, version := ver, path := path, dependencies := deps, timeout := tm }

def to_toml (d : manifest) : toml.value :=
let pkg := [("name", toml.value.str d.name), ("version", toml.value.str d.version)],
    pkg := match d.path with some p := pkg ++ [("path", toml.value.str p)] | none := pkg end,
    pkg := match d.timeout with some t := pkg ++ [("timeout", toml.value.nat t)] | none := pkg end,
    deps := toml.value.table $ d.dependencies.for $ λ dep, (dep.name, dep.src.to_toml) in
toml.value.table [("package", toml.value.table pkg), ("dependencies", deps)]

instance : has_to_string manifest :=
⟨λ d, d.to_toml.to_string⟩

def from_string (s : string) : option manifest :=
match parser.run_string toml.File s with
| sum.inr toml := from_toml toml
| sum.inl _ := none
end

def from_file [io.interface] (fn : string) : io manifest := do
cnts ← io.fs.read_file fn,
toml ←
  (match parser.run toml.File cnts with
  | sum.inl err :=
    io.fail $ "toml parse error in " ++ fn ++ "\n\n" ++ err
  | sum.inr res := return res
  end),
some manifest ← return (from_toml toml)
  | io.fail ("cannot read manifest from " ++ fn ++ "\n\n" ++ toml.to_string),
return manifest

end manifest

def leanpkg_toml_fn := "leanpkg.toml"

end leanpkg
