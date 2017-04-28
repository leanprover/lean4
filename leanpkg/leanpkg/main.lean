/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.resolve
variable [io.interface]

namespace leanpkg

def write_file (fn : string) (cnts : string) (mode := io.mode.write) : io unit := do
h ← io.mk_file_handle fn io.mode.write,
io.fs.write h cnts.to_char_buffer,
io.fs.close h

def read_manifest : io manifest :=
manifest.from_file leanpkg_toml_fn

def write_manifest (d : manifest) (fn := leanpkg_toml_fn) : io unit :=
write_file fn (to_string d)

-- TODO(gabriel): implement a cross-platform api
def get_dot_lean_dir : io string :=
io.cmd "bash" ["-c", "echo -n ~/.lean"]

-- TODO(gabriel): file existence testing
def exists_file (f : string) : io bool := do
ch ← io.proc.spawn { cmd := "test", args := ["-f", f] },
ev ← io.proc.wait ch,
return $ ev = 0

def mk_path_file : ∀ (paths : list string), string
| [] := "builtin_path\n"
| (x :: xs) := mk_path_file xs ++ "path " ++ x ++ "\n"

def configure : io unit := do
d ← read_manifest,
io.put_str_ln $ "configuring " ++ d.name ++ " " ++ d.version,
assg ← solve_deps d,
path_file_cnts ← mk_path_file <$> construct_path assg,
write_file "leanpkg.path" path_file_cnts

def make : io unit :=
exec_cmd "lean" ["--make"]

def build := configure >> make

def init_gitignore_contents :=
"*.olean
/_target
/leanpkg.path
"

def init_pkg (n : string) (dir : string) : io unit := do
write_manifest { name := n, version := "0.1", path := none, dependencies := [] }
  (dir ++ "/" ++ leanpkg_toml_fn),
write_file (dir ++ "/.gitignore") init_gitignore_contents io.mode.append,
exec_cmd "leanpkg" ["configure"] dir

def init (n : string) := init_pkg n "."

-- TODO(gabriel): windows
def basename : ∀ (fn : string), string
| []          := []
| (c :: rest) :=
  if c = #"/" then [] else c :: basename rest

def add_dep_to_manifest (dep : dependency) : io unit := do
d ← read_manifest,
let d' := { d with dependencies := d.dependencies.filter (λ old_dep, old_dep.name ≠ dep.name) ++ [dep] },
write_manifest d'

def strip_dot_git (url : string) : string :=
if url.taken 4 = ".git" then url.dropn 4 else url

def absolutize_add_dep (dep : string) : io string :=
if #":" ∈ @cast string (list char) rfl dep then return dep
else do cwd ← io.cmd "pwd" [], return $ resolve_dir dep (cwd.dropn 1) -- remove final newline

def parse_add_dep (dep : string) : dependency :=
if #":" ∈ @cast string (list char) rfl dep then -- looks like git :-)
  { name := basename (strip_dot_git dep), src := source.git dep "master" }
else
  { name := basename dep, src := source.path dep }

def fixup_git_version (dir : string) : ∀ (src : source), io source
| (source.git url _) := do
  rev ← io.cmd "git" ["rev-parse", "HEAD"] dir,
  return $ source.git url (rev.dropn 1) -- remove newline at end
| src := return src

def add (dep : string) : io unit := do
let dep := parse_add_dep dep,
(_, assg) ← materialize "." dep assignment.empty,
some downloaded_path ← return (assg.find dep.name),
manif ← manifest.from_file (downloaded_path ++ "/" ++ leanpkg_toml_fn),
src ← fixup_git_version downloaded_path dep.src,
let dep := { dep with name := manif.name, src := src },
add_dep_to_manifest dep,
configure

def new (dir : string) := do
ex ← dir_exists dir,
when ex $ io.fail $ "directory already exists: " ++ dir,
exec_cmd "mkdir" ["-p", dir],
init_pkg (basename dir) dir

def usage := "
Usage: leanpkg <command>

configure       download dependencies
build           download dependencies and build *.olean files

new <dir>       creates a lean package in the specified directory
init <name>     adds a leanpkg.toml file to the current directory, and sets up .gitignore

add <url>       adds a dependency from a git repository (uses current master revision)
add <dir>       adds a local dependency

install <url>   installs a user-wide package from git
install <dir>   installs a user-wide package from a local directory

dump            prints the parsed leanpkg.toml file (for debugging)
"

set_option eqn_compiler.lemmas false -- TODO(gabriel): just for performance
def main : ∀ (args : list string), io unit
| ["configure"] := configure
| ["build"] := build
| ["new", dir] := new dir
| ["init", name] := init name
| ["add", dep] := add dep
| ["install", dep] := do
  dep ← absolutize_add_dep dep,
  dot_lean_dir ← get_dot_lean_dir,
  exec_cmd "mkdir" ["-p", dot_lean_dir],
  let user_toml_fn := dot_lean_dir ++ "/" ++ leanpkg_toml_fn,
  ex ← exists_file user_toml_fn,
  when (¬ ex) $ write_manifest {
      name := "_user_local_packages",
      version := "1",
      path := none,
      dependencies := []
    } user_toml_fn,
  exec_cmd "leanpkg" ["add", dep] dot_lean_dir
| ["dump"] := read_manifest >>= io.print_ln
| _ := io.fail usage

end leanpkg

def main : io unit := io.cmdline_args >>= leanpkg.main
