-- Output a C++ statement that creates the given name
function sanitize(s)
   s, _ = string.gsub(s, "'", "_")
   return s
end
function name_to_cpp_expr(n)
   function rec(n)
      if not n:is_atomic() then
         rec(n:get_prefix())
         io.write(", ")
      end
      if n:is_string() then
         local s = n:get_string()
         io.write("\"" .. sanitize(s) .. "\"")
      else
         error("numeral hierarchical names are not supported in the C++ interface: " .. tostring(n))
      end
   end

   io.write("name(")
   if n:is_atomic() then
      rec(n)
   else
      io.write("{")
      rec(n)
      io.write("}")
   end
   io.write(")")
end

-- Output a C++ constant name based on the given hierarchical name
-- It uses '_' to glue the hierarchical name parts
function name_to_cpp_decl(n)
   if not n:is_atomic(n) then
      name_to_cpp_decl(n:get_prefix())
      io.write("_")
   end
   if n:is_string() then
      local s = n:get_string()
      io.write(sanitize(s))
   else
      error("numeral hierarchical names are not supported in the C++ interface: " .. tostring(n))
   end
end
