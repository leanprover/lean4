/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.resolve
variable [io.interface]

namespace leanpkg

def leanpkg_toml_fn := "leanpkg.toml"

def read_desc : io desc :=
desc.from_file leanpkg_toml_fn

def write_desc (d : desc) (fn := leanpkg_toml_fn) : io unit := do
h ← io.mk_file_handle fn io.mode.write,
io.fs.write h (to_string d).to_char_buffer,
io.fs.close h

-- TODO(gabriel): implement a cross-platform api
def get_dot_lean_dir : io string :=
io.cmd "bash" ["-c", "echo -n ~/.lean"]

-- TODO(gabriel): file existence testing
def exists_file (f : string) : io bool := do
ch ← io.proc.spawn { cmd := "test", args := ["-f", f] },
ev ← io.proc.wait ch,
return $ ev = 0

def mk_path_file (assg : assignment) : string :=
let paths := assg.fold ["."] (λ xs _ x, x :: xs),
    lines := "builtin_path" :: paths.map (λ p, "path " ++ p) in
lines.foldr (λ x xs, x ++ "\n" ++ xs) ""

def configure : io unit := do
d ← read_desc,
io.put_str_ln $ "configuring " ++ d.name ++ " " ++ d.version,
assg ← solve_deps d,
let path_file_cnts := mk_path_file assg,
path_file_h ← io.mk_file_handle "leanpkg.path" io.mode.write,
io.fs.write path_file_h $ buffer.nil.append_list path_file_cnts.reverse,
io.fs.close path_file_h

def make : io unit :=
exec_cmd "lean" ["--make"]

def build := configure >> make

def add (dep : dependency) : io unit := do
d ← read_desc,
let d' := { d with dependencies := d.dependencies.filter (λ old_dep, old_dep.name ≠ dep.name) ++ [dep] },
write_desc d'

def init_pkg (n : string) (dir : string) : io unit := do
write_desc { name := n, version := "0.1", dependencies := [] }
  (dir ++ "/" ++ leanpkg_toml_fn),
h ← io.mk_file_handle (dir ++ "/.gitignore") io.mode.append,
io.fs.write h "*.olean\n/_target\n/leanpkg.path\n".to_char_buffer,
io.fs.close h

def init (n : string) := init_pkg n "."

-- TODO(gabriel): windows
def basename : ∀ (fn : string), string
| []          := []
| (c :: rest) :=
  if c = #"/" then [] else c :: basename rest

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

add --git <name> <url> <rev>
                adds a dependency from a git repository
add --local <name> <directory>
                adds a local dependency

install --git <name> <url> <rev>
                installs a user-wide package from git
install --local <name> <url>
                installs a user-wide package from a local directory

dump            prints the parsed leanpkg.toml file (for debugging)
"

set_option eqn_compiler.lemmas false -- TODO(gabriel): just for performance
def main : ∀ (args : list string), io unit
| ["configure"] := configure
| ["build"] := build
| ["new", dir] := new dir
| ["init", name] := init name
| ["add", "--git", n, url, rev] :=
  add { name := n, src := source.git url rev }
| ["add", "--local", n, dir] :=
  add { name := n, src := source.path dir }
| ("install" :: rest) := do
  dot_lean_dir ← get_dot_lean_dir,
  exec_cmd "mkdir" ["-p", dot_lean_dir],
  let user_toml_fn := dot_lean_dir ++ "/" ++ leanpkg_toml_fn,
  ex ← exists_file user_toml_fn,
  when (¬ ex) $ write_desc {
      name := "_user_local_packages",
      version := "1",
      dependencies := []
    } user_toml_fn,
  exec_cmd "leanpkg" ("add" :: rest) dot_lean_dir,
  exec_cmd "leanpkg" ["configure"] dot_lean_dir
| ["dump"] := read_desc >>= io.print_ln
| _ := io.fail usage

end leanpkg

def main : io unit := io.cmdline_args >>= leanpkg.main
