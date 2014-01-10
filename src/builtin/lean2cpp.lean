(*
 -- Auxiliary script for generating .cpp files that define
 -- constants defined in Lean
 local env = get_environment()
 local num_imports = 0
 print('/*')
 print('Copyright (c) 2013 Microsoft Corporation. All rights reserved.')
 print('Released under Apache 2.0 license as described in the file LICENSE.')
 print('*/')
 print("// Automatically generated file, DO NOT EDIT")
 print('#include "kernel/environment.h"')
 print('#include "kernel/decl_macros.h"')
 print('namespace lean {')
 for obj in env:objects() do
    if obj:is_begin_import() or obj:is_begin_builtin_import() then
       num_imports = num_imports + 1
    elseif obj:is_end_import() then
       num_imports = num_imports - 1
    elseif num_imports == 0 and obj:has_name() and obj:has_type() and not is_explicit(env, obj:get_name()) and not obj:is_builtin() then
       local is_fn = env:normalize(obj:get_type()):is_pi()
       io.write('MK_CONSTANT(')
       name_to_cpp_decl(obj:get_name())
       if is_fn then
          io.write('_fn')
       end
       io.write(', ')
       name_to_cpp_expr(obj:get_name())
       print(');')
    end
 end
 print('}')
*)
