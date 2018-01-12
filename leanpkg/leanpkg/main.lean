/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.resolve leanpkg.git

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

def mk_path_file : ∀ (paths : list string), string
| [] := "builtin_path\n"
| (x :: xs) := mk_path_file xs ++ "path " ++ x ++ "\n"

def configure : io unit := do
d ← read_manifest,
io.put_str_ln $ "configuring " ++ d.name ++ " " ++ d.version,
when (d.path ≠ some "src") $ io.put_str_ln "WARNING: leanpkg configurations not specifying `path = \"src\"` are deprecated.",
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

def init_pkg (n : string) (from_new : bool) : io unit := do
write_manifest { name := n, path := "src", version := "0.1" } leanpkg_toml_fn,
src_ex ← dir_exists "src",
when (¬src_ex) (do
  when ¬from_new $ io.put_str_ln "Move existing .lean files into the 'src' folder.",
  exec_cmd {cmd := "mkdir", args := ["src"]}),
write_file ".gitignore" init_gitignore_contents io.mode.append,
git_ex ← dir_exists ".git",
when (¬git_ex) (do {
  exec_cmd {cmd := "git", args := ["init", "-q"]},
  when (upstream_git_branch ≠ "master") $
    exec_cmd {cmd := "git", args := ["checkout", "-b", upstream_git_branch]}
} <|> io.print_ln "WARNING: failed to initialize git repository"),
configure

def init (n : string) := init_pkg n false

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

def parse_add_dep (dep : string) : io dependency :=
if looks_like_git_url dep then
  pure { name := basename (strip_dot_git dep), src := source.git dep upstream_git_branch }
else do
  ex ← dir_exists dep,
  if ex then
    pure { name := basename dep, src := source.path dep }
  else do
    [user, repo] ← pure $ dep.split (= '/')
      | io.fail sformat!"path '{dep}' does not exist",
    pure { name := repo, src := source.git sformat!"https://github.com/{user}/{repo}" upstream_git_branch }

def absolutize_dep (dep : dependency) : io dependency :=
match dep.src with
| source.path p := do
  cwd ← io.env.get_cwd,
  pure {src := source.path (resolve_dir p cwd), ..dep}
| _ := pure dep
end

def fixup_git_version (dir : string) : ∀ (src : source), io source
| (source.git url _) := source.git url <$> git_head_revision dir
| src := return src

def add (dep : dependency) : io unit := do
(_, assg) ← (materialize "." dep).run assignment.empty,
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
change_dir dir,
init_pkg (basename dir) true

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

new <dir>              create a Lean package in a new directory
init <name>            create a Lean package in the current directory

add <url>              add a dependency from a git repository (uses latest upstream revision)
add <dir>              add a local dependency
upgrade                upgrade all git dependencies to the latest upstream version

install <url>          install a user-wide package from git
install <dir>          install a user-wide package from a local directory

dump                   print the parsed leanpkg.toml file (for debugging)

See `leanpkg help <command>` for more information on a specific command."

def main : ∀ (cmd : string) (leanpkg_args lean_args : list string), io unit
| "configure" []     []        := configure
| "build"     _      lean_args := build lean_args
| "test"      _      lean_args := test lean_args
| "new"       [dir]  []        := new dir
| "init"      [name] []        := init name
| "add"       [dep]  []        := parse_add_dep dep >>= add
| "upgrade"   []     []        := upgrade
| "install"   [dep]  []        := do
  dep ← parse_add_dep dep,
  dep ← absolutize_dep dep,
  dot_lean_dir ← get_dot_lean_dir,
  exec_cmd {cmd := "mkdir", args := ["-p", dot_lean_dir]},
  let user_toml_fn := dot_lean_dir ++ "/" ++ leanpkg_toml_fn,
  ex ← exists_file user_toml_fn,
  when (¬ ex) $ write_manifest {
      name := "_user_local_packages",
      version := "1"
    } user_toml_fn,
  change_dir dot_lean_dir,
  add dep,
  build []
| "dump"       []    []        := read_manifest >>= io.print_ln ∘ repr
| "help"       ["configure"] [] := io.print_ln "Download dependencies

Usage:
  leanpkg configure

This command sets up the `_target/deps` directory and the `leanpkg.path` file.

For each (transitive) git dependency, the specified commit is checked out
into a sub-directory of `_target/deps`. If there are dependencies on multiple
versions of the same package, the version materialized is undefined.

The `leanpkg.path` file used to resolve Lean imports is populated with paths
to the `src` directories of all (transitive) dependencies. No copy is made
of local dependencies."
| "help"       ["build"] []    := io.print_ln "Download dependencies and build *.olean files

Usage:
  leanpkg build [-- <lean-args>]

This command invokes `leanpkg configure` followed by
`lean --make src <lean-args>`, building the package's Lean files as well as
(transitively) imported files of dependencies. If defined, the `package.timeout`
configuration value is passed to Lean via its `-T` parameter."
| "help"       ["test"] []     := io.print_ln "Download dependencies, build *.olean files, and run test files

Usage:
  leanpkg test [-- <lean-args>]

This command invokes `leanpkg build <lean-args>` followed by
`lean --make test <lean-args>`, executing the package's test files. A failed
test should generate a Lean error message, which makes this command return a
non-zero exit code."
| "help"       ["add"] []      := io.print_ln sformat!"Add a dependency

Usage:
  leanpkg add <local-path>
  leanpkg add <git-url>
  leanpkg add <github-user>/<github-repo>

Examples:
  leanpkg add ../mathlib
  leanpkg add https://github.com/leanprover/mathlib
  leanpkg add leanprover/mathlib

This command adds the specified local or git dependency, then calls
`leanpkg configure`. For git dependencies, the pinned commit is
the head of the branch `lean-<version>` (e.g. `lean-3.3.0`) on stable
releases of Lean, or else `master` (current branch: {upstream_git_branch})."
| "help"       ["new"] []      := io.print_ln "Create a new Lean package in a new directory

Usage:
  leanpkg new <path>/.../<name>

This command creates a new Lean package named '<name>' in a new directory
`<path>/.../<name>`. A new git repository is initialized to the branch name
expected by `leanpkg add` (see `leanpkg help add`).

For converting an existing directory into a Lean package, use `leanpkg init`."
| "help"       ["init"] []     := io.print_ln "Create a new Lean package in the current directory

Usage:
  leanpkg init <name>

This command creates a new Lean package with the given name in the current
directory. Existing Lean source files should be moved into the new `src`
directory."
| "help"       ["upgrade"] []  := io.print_ln "Upgrade all git dependencies to the latest upstream version

Usage:
  leanpkg upgrade

This command fetches the remote repositories of all git dependencies and updates
the pinned commits to the head of the respective branch (see
`leanpkg help add`)."
| "help"       ["install"] []  := io.print_ln "Install a user-wide package

Usage:
  leanpkg install <local-path>
  leanpkg install <git-url>
  leanpkg install <github-user>/<github-repo>

This command adds a dependency to a user-wide \"meta\" package in `~/.lean`.
For files not part of a Lean package, Lean falls back to the core library
and this meta package for import resolution.

For removing or upgrading user-wide dependencies, you currently have to change
into `~/.lean` yourself and edit the leanpkg.toml file or execute
`leanpkg upgrade`, respectively."
| "help"       _     []        := io.print_ln usage
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
