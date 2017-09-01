/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.resolve leanpkg.git
variable [io.interface]

namespace leanpkg

def write_file (fn : string) (cnts : string) (mode := io.mode.write) : io unit := do
h ← io.mk_file_handle fn io.mode.write,
io.fs.write h cnts.to_char_buffer,
io.fs.close h

def read_manifest : io manifest := do
m ← manifest.from_file leanpkg_toml_fn,
when (m.lean_version ≠ lean_version_string) $
  io.print_ln $ "\nWARNING: Lean version mismatch: installed version is " ++ lean_version_string
     ++ ", but package requires " ++ m.lean_version ++ "\n",
return m

def write_manifest (d : manifest) (fn := leanpkg_toml_fn) : io unit :=
write_file fn (repr d)

-- TODO(gabriel): implement a cross-platform api
def get_dot_lean_dir : io string := do
some home ← io.env.get "HOME" | io.fail "environment variable HOME is not set",
return $ home ++ "/.lean"

-- TODO(gabriel): file existence testing
def exists_file (f : string) : io bool := do
ch ← io.proc.spawn { cmd := "test", args := ["-f", f] },
ev ← io.proc.wait ch,
return $ ev = 0

-- TODO(gabriel): io.env.get_current_directory
def get_current_directory : io string :=
do cwd ← io.cmd { cmd := "pwd" }, return cwd.pop_back -- remove final newline

def mk_path_file : ∀ (paths : list string), string
| [] := "builtin_path\n"
| (x :: xs) := mk_path_file xs ++ "path " ++ x ++ "\n"

def configure : io unit := do
d ← read_manifest,
io.put_str_ln $ "configuring " ++ d.name ++ " " ++ d.version,
assg ← solve_deps d,
path_file_cnts ← mk_path_file <$> construct_path assg,
write_file "leanpkg.path" path_file_cnts

def make (lean_args : list string) : io unit := do
manifest ← read_manifest,
exec_cmd {
  cmd := "lean",
  args := (match manifest.timeout with some t := ["-T", repr t] | none := [] end) ++
    ["--make"] ++ manifest.effective_path ++ lean_args,
  env := [("LEAN_PATH", none)]
}

def build (lean_args : list string) := configure >> make lean_args

def make_test (lean_args : list string) : io unit :=
exec_cmd { cmd := "lean", args := ["--make", "test"] ++ lean_args, env := [("LEAN_PATH", none)] }

def test (lean_args : list string) := build lean_args >> make_test lean_args

def init_gitignore_contents :=
"*.olean
/_target
/leanpkg.path
"

def init_pkg (n : string) (dir : string) : io unit := do
write_manifest { name := n, version := "0.1" } (dir ++ "/" ++ leanpkg_toml_fn),
write_file (dir ++ "/.gitignore") init_gitignore_contents io.mode.append,
exec_cmd {cmd := "leanpkg", args := ["configure"], cwd := dir}

def init (n : string) := init_pkg n "."

-- TODO(gabriel): windows
def basename (s : string) : string :=
s.fold "" $ λ s c, if c = '/' then "" else s.str c

def add_dep_to_manifest (dep : dependency) : io unit := do
d ← read_manifest,
let d' := { d with dependencies := d.dependencies.filter (λ old_dep, old_dep.name ≠ dep.name) ++ [dep] },
write_manifest d'

def strip_dot_git (url : string) : string :=
if url.backn 4 = ".git" then url.popn_back 4 else url

def looks_like_git_url (dep : string) : bool :=
':' ∈ dep.to_list

def absolutize_add_dep (dep : string) : io string :=
if looks_like_git_url dep then return dep
else resolve_dir dep <$> get_current_directory

def parse_add_dep (dep : string) : dependency :=
if looks_like_git_url dep then
  { name := basename (strip_dot_git dep), src := source.git dep upstream_git_branch }
else
  { name := basename dep, src := source.path dep }

def fixup_git_version (dir : string) : ∀ (src : source), io source
| (source.git url _) := source.git url <$> git_head_revision dir
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
exec_cmd {cmd := "mkdir", args := ["-p", dir]},
init_pkg (basename dir) dir

def upgrade_dep (assg : assignment) (d : dependency) : io dependency :=
match d.src with
| (source.git url rev) := (do
    some path ← return (assg.find d.name) | io.fail "unresolved dependency",
    new_rev ← git_latest_origin_revision path,
    return {d with src := source.git url new_rev})
  <|> return d
| _ := return d
end

def upgrade := do
m ← read_manifest,
assg ← solve_deps m,
ds' ← m.dependencies.mmap (upgrade_dep assg),
write_manifest {m with dependencies := ds'},
configure

def usage :=
"Lean package manager, version " ++ ui_lean_version_string ++ "

Usage: leanpkg <command>

configure              download dependencies
build [-- <lean-args>] download dependencies and build *.olean files
test  [-- <lean-args>] download dependencies, build *.olean files, and run test files

new <dir>              creates a lean package in the specified directory
init <name>            adds a leanpkg.toml file to the current directory, and sets up .gitignore

add <url>              adds a dependency from a git repository (uses latest upstream revision)
add <dir>              adds a local dependency
upgrade                upgrades all git dependencies to the latest upstream version

install <url>          installs a user-wide package from git
install <dir>          installs a user-wide package from a local directory

dump                   prints the parsed leanpkg.toml file (for debugging)
"

def main : ∀ (cmd : string) (leanpkg_args lean_args : list string), io unit
| "configure" []     []        := configure
| "build"     _      lean_args := build lean_args
| "test"      _      lean_args := test lean_args
| "new"       [dir]  []        := new dir
| "init"      [name] []        := init name
| "add"       [dep]  []        := add dep
| "upgrade"   []     []        := upgrade
| "install"   [dep]  []        := do
  dep ← absolutize_add_dep dep,
  dot_lean_dir ← get_dot_lean_dir,
  exec_cmd {cmd := "mkdir", args := ["-p", dot_lean_dir]},
  let user_toml_fn := dot_lean_dir ++ "/" ++ leanpkg_toml_fn,
  ex ← exists_file user_toml_fn,
  when (¬ ex) $ write_manifest {
      name := "_user_local_packages",
      version := "1"
    } user_toml_fn,
  exec_cmd {cmd := "leanpkg", args := ["add", dep], cwd := dot_lean_dir},
  exec_cmd {cmd := "leanpkg", args := ["build"], cwd := dot_lean_dir}
| "dump"       []    []        := read_manifest >>= io.print_ln ∘ repr
| _            _     _         := io.fail usage

private def split_cmdline_args_core : list string → list string × list string
| []           := ([], [])
| (arg::args)  := if arg = "--"
                  then ([], args)
                  else match split_cmdline_args_core args with
                       | (outer_args, inner_args) := (arg::outer_args, inner_args)
                       end

def split_cmdline_args : list string → io (string × list string × list string)
| [] := io.fail usage
| [cmd] := return (cmd, [], [])
| (cmd::rest) := match split_cmdline_args_core rest with
                 | (outer_args, inner_args) := return (cmd, outer_args, inner_args)
                 end
end leanpkg


def main : io unit :=
do (cmd, outer_args, inner_args) ← io.cmdline_args >>= leanpkg.split_cmdline_args,
   leanpkg.main cmd outer_args inner_args
