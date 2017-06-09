open lean
open lean.parser
open interactive
open tactic

-- missing tk
@[user_command]
meta def foo_cmd : parser unit := pure ()

-- wrong return type
@[user_command]
meta def foo_cmd (_ : parse $ tk "foo") : unit := ()

foo

@[user_command]
meta def foo_cmd (_ : parse $ tk "foo") : parser unit :=
trace "foo"

run_cmd skip

foo
private foo

@[user_command]
meta def foo_cmd2 (_ : parse $ tk "foo") : parser unit :=
trace "bar"

foo

@[user_command]
meta def foo_cmd3 (dmi : decl_meta_info) (_ : parse $ tk "foo") : parser unit :=
trace format!"{dmi.modifiers.is_private}"

foo
private foo
