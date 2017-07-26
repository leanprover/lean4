/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.manifest system.io leanpkg.proc
variable [io.interface]

namespace leanpkg

def assignment := list (string × string)

namespace assignment
def empty : assignment := []

def find : assignment → string → option string
| []              s := none
| ((k, v) :: kvs) s :=
  if k = s then some v else find kvs s

def contains (a : assignment) (s : string) : bool :=
(a.find s).is_some

def insert (a : assignment) (k v : string) : assignment :=
if a.contains k then a else (k, v) :: a

def fold {α} (i : α) (f : α → string → string → α) : assignment → α :=
list.foldl (λ a ⟨k, v⟩, f a k v) i

end assignment

@[reducible] def solver := state_t assignment io
instance {α : Type} : has_coe (io α) (solver α) := ⟨state_t.lift⟩

def not_yet_assigned (d : string) : solver bool := do
assg ← state_t.read,
return $ ¬ assg.contains d

def resolved_path (d : string) : solver string := do
assg ← state_t.read,
some path ← return (assg.find d) | io.fail "",
return path

-- TODO(gabriel): directory existence testing
def dir_exists (d : string) : io bool := do
ch ← io.proc.spawn { cmd := "test", args := ["-d", d] },
ev ← io.proc.wait ch,
return $ ev = 0

-- TODO(gabriel): windows?
def resolve_dir (abs_or_rel : string) (base : string) : string :=
if abs_or_rel.front = '/' then
  abs_or_rel -- absolute
else
  base ++ "/" ++ abs_or_rel

def materialize (relpath : string) (dep : dependency) : solver unit :=
match dep.src with
| (source.path dir) := do
  let depdir := resolve_dir dir relpath,
  io.put_str_ln $ dep.name ++ ": using local path " ++ depdir,
  state_t.modify $ λ assg, assg.insert dep.name depdir
| (source.git url rev) := do
  let depdir := "_target/deps/" ++ dep.name,
  already_there ← dir_exists depdir,
  let checkout_action := exec_cmd {cmd := "git", args := ["checkout", "--detach", rev], cwd := depdir},
  (do guard already_there,
      io.put_str_ln $ dep.name ++ ": trying to update " ++ depdir ++ " to revision " ++ rev,
      checkout_action) <|>
  (do guard already_there,
      exec_cmd {cmd := "git", args := ["fetch"], cwd := depdir},
      checkout_action) <|>
  (do io.put_str_ln $ dep.name ++ ": cloning " ++ url ++ " to " ++ depdir,
      exec_cmd {cmd := "rm", args := ["-rf", depdir]},
      exec_cmd {cmd := "mkdir", args := ["-p", depdir]},
      exec_cmd {cmd := "git", args := ["clone", url, depdir]},
      exec_cmd {cmd := "git", args := ["checkout", "--detach", rev], cwd := depdir}),
  state_t.modify $ λ assg, assg.insert dep.name depdir
end

def solve_deps_core : ∀ (rel_path : string) (d : manifest) (max_depth : ℕ), solver unit
| _ _ 0 := io.fail "maximum dependency resolution depth reached"
| relpath d (max_depth + 1) := do
deps ← monad.filter (not_yet_assigned ∘ dependency.name) d.dependencies,
deps.mmap' (materialize relpath),
deps.mmap' $ λ dep, do
  p ← resolved_path dep.name,
  d ← manifest.from_file $ p ++ "/" ++ "leanpkg.toml",
  when (d.name ≠ dep.name) $
    io.fail $ d.name ++ " (in " ++ relpath ++ ") depends on " ++ d.name ++
      ", but resolved dependency has name " ++ dep.name ++ " (in " ++ p ++ ")",
  solve_deps_core p d max_depth

def solve_deps (d : manifest) : io assignment := do
(_, assg) ← solve_deps_core "." d 1024 $ assignment.empty.insert d.name ".",
return assg

def construct_path_core (depname : string) (dirname : string) : io (list string) :=
list.map (λ relpath, dirname ++ "/" ++ relpath) <$>
manifest.effective_path <$> (manifest.from_file $ dirname ++ "/" ++ leanpkg_toml_fn)

def construct_path (assg : assignment) : io (list string) := do
let assg := assg.fold [] (λ xs depname dirname, (depname, dirname) :: xs),
list.join <$> (assg.mmap $ λ ⟨depname, dirname⟩, construct_path_core depname dirname)

end leanpkg
