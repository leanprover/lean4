-- Parse a template expression string 'str'.
-- The string 'str' may contain placeholders of the form '% i', where 'i' is a numeral.
-- The placeholders are replaced with values from the array 'arg_array'.
local arg_array = {}

-- We implement this feature using macros available in Lean.
macro("%",
      { macro_arg.Int },
      function (env, i)
         if i <= 0 then
            error("invalid template argument reference %" .. i .. ", first argument is 1")
         elseif i > #arg_array then
            error("invalid template argument reference %" .. i .. ", only " .. tostring(#arg_array) .. " argument(s) were provided")
         else
            return arg_array[i]
         end
      end
)

-- Parse a template.
-- Example:
--    r = parse_template("%1 + %2 + %1", {Const("a"), Const("b")})
--    print(r)
--    >> a + b + a
function parse_template(str, args, env, opts, fmt)
   assert(type(str)  == "string")
   assert(type(args) == "table")
   assert(env == nil or is_environment(env))
   arg_array = args
   return parse_lean(str, env, opts, fmt)
end
