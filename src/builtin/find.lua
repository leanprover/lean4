-- Define the command
--
--       Find [regex]
--
-- It displays objects in the environment whose name match the given regular expression.
-- Example: the command
--       Find "^[cC]on"
-- Displays all objects that start with the string "con" or "Con"
cmd_macro("Find",
          { macro_arg.String },
          function(env, pattern)
             local opts  = get_options()
             -- Do not display the definition value
             opts = opts:update({"lean", "pp", "definition_value"}, false)
             local fmt   = get_formatter()
             local found = false
             for obj in env:objects() do
                if obj:has_name() and obj:has_type() and string.match(tostring(obj:get_name()), pattern) then
                   print(fmt(obj, opts))
                   found = true
                end
             end
             if not found then
                error("no object name in the environment matches the regular expression '" .. pattern .. "'")
             end
          end
)
