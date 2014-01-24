(*
 -- Auxiliary script for generating .h file that declare mk_* and is_* functions for
 -- constants defined in Lean
 local env = get_environment()
 local num_imports = 0
 print('/*')
 print('Copyright (c) 2013 Microsoft Corporation. All rights reserved.')
 print('Released under Apache 2.0 license as described in the file LICENSE.')
 print('*/')
 print("// Automatically generated file, DO NOT EDIT")
 print('#include "kernel/expr.h"')
 print('namespace lean {')
 for obj in env:objects() do
    if obj:is_begin_import() or obj:is_begin_builtin_import() then
       num_imports = num_imports + 1
    elseif obj:is_end_import() then
       num_imports = num_imports - 1
    elseif num_imports == 0 and obj:has_name() and obj:has_type() and not is_explicit(env, obj:get_name()) and not obj:is_builtin() then
       local ty    = env:normalize(obj:get_type())
       local is_fn = ty:is_pi()
       local arity = 0
       while ty:is_pi() do
          n, d, ty = ty:fields()
          arity = arity + 1
       end
       local is_th = obj:is_theorem() or obj:is_axiom()
       io.write("expr mk_")
       name_to_cpp_decl(obj:get_name())
       if is_fn then
          io.write("_fn");
       end
       print("();")
       io.write("bool is_")
       name_to_cpp_decl(obj:get_name())
       if is_fn then
          io.write("_fn");
       end
       print("(expr const & e);")
       if is_fn and not is_th then
          io.write("inline bool is_")
          name_to_cpp_decl(obj:get_name())
          io.write("(expr const & e) { return is_app(e) && is_");
          name_to_cpp_decl(obj:get_name())
          print("_fn(arg(e, 0)) && num_args(e) == " .. (arity+1) .. "; }")
       end
       if is_fn then
          io.write("inline expr mk_")
          name_to_cpp_decl(obj:get_name())
          if is_th then
             io.write("_th");
          end
          io.write("(");
          for i = 1, arity do
             if i > 1 then
                io.write(", ")
             end
             io.write("expr const & e" .. tostring(i))
          end
          io.write(") { return mk_app({mk_");
          name_to_cpp_decl(obj:get_name())
          io.write("_fn()")
          for i = 1, arity do
             io.write(", e" .. tostring(i))
          end
          print ("}); }")
       end
    end
 end
 print('}')

*)
