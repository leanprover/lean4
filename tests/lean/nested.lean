(**
cmd_macro("Simple",
          { macro_arg.String },
          function (env, str)
             print("OUTPUT: " .. str)
          end
)

parse_lean_cmds([[
   Simple "foo"
]])
**)

Simple "testing"

(**
parse_lean_cmds([[
   Simple "bla"
]])
**)
