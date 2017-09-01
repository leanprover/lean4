/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.lean_version system.io
variable [io.interface]

namespace leanpkg

def upstream_git_branch :=
if lean_version.is_release then
    "lean-" ++ lean_version_string_core
else
    "master"

def git_parse_revision (git_repo_dir : string) (rev : string) : io string := do
rev ← io.cmd {cmd := "git", args := ["rev-parse", "-q", "--verify", rev], cwd := git_repo_dir},
return rev.pop_back -- remove newline at end

def git_head_revision (git_repo_dir : string) : io string :=
git_parse_revision git_repo_dir "HEAD"

def git_parse_origin_revision (git_repo_dir : string) (rev : string) : io string :=
(git_parse_revision git_repo_dir $ "origin/" ++ rev) <|> git_parse_revision git_repo_dir rev
    <|> io.fail ("cannot find revision " ++ rev ++ " in repository " ++ git_repo_dir)

def git_latest_origin_revision (git_repo_dir : string) : io string := do
io.cmd {cmd := "git", args := ["fetch"], cwd := git_repo_dir},
git_parse_origin_revision git_repo_dir upstream_git_branch

end leanpkg