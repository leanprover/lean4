(**
macro("IdMacro",
      { macro_arg.Expr },
      function (env, e)
         return e
      end
)
**)

Show IdMacro 10.
Import "module.lean"
