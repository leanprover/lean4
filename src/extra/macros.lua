-- Extra macros for automating proof construction using Lua.

-- This macro creates the syntax-sugar
--     name bindings ',' expr
-- For a function f with signature
--    f : ... (A : Type) ... (Pi x : A, ...)
--
-- farity is the arity of f
-- typepos is the position of (A : Type) argument
-- lambdapos is the position of the (Pi x : A, ...) argument
--
-- Example: suppose we invoke
--
--    binder_macro("for", Const("ForallIntro"), 3, 1, 3)
--
-- Then, the macro expression
--
--     for x y : Int, H x y
--
-- produces the expression
--
--     ForallIntro Int _ (fun x : Int, ForallIntro Int _ (fun y : Int, H x y))
--
-- The _ are placeholders (aka) holes that will be filled by the Lean
-- elaborator.
function binder_macro(name, f, farity, typepos, lambdapos)
   macro(name, { macro_arg.Bindings, macro_arg.Comma, macro_arg.Expr },
         function (bindings, body)
            local r = body
            for i = #bindings, 1, -1 do
               local bname = bindings[i][1]
               local btype = bindings[i][2]
               local args  = {}
               args[#args + 1] = f
               for j = 1, farity, 1 do
                  if j == typepos then
                     args[#args + 1] = btype
                  elseif j == lambdapos then
                     args[#args + 1] = fun(bname, btype, r)
                  else
                     args[#args + 1] = mk_placeholder()
                  end
               end
               r = mk_app(unpack(args))
            end
            return r
   end)
end

-- The following macro is used to create nary versions of operators such as MP and ForallElim.
-- Example: suppose we invoke
--
--    nary_macro("mp", Const("MP"), 4)
--
-- Then, the macro expression
--
--     mp Foo H1 H2 H3
--
-- produces the expression
--
--     (MP (MP (MP Foo H1) H2) H3)
function nary_macro(name, f, farity)
   local bin_app = function(e1, e2)
      local args = {}
      args[#args + 1] = f
      for i = 1, farity - 2, 1 do
         args[#args + 1] = mk_placeholder()
      end
      args[#args + 1] = e1
      args[#args + 1] = e2
      return mk_app(unpack(args))
   end

   macro(name, { macro_arg.Expr, macro_arg.Expr, macro_arg.Exprs },
         function (e1, e2, rest)
            local r = bin_app(e1, e2)
            for i = 1, #rest do
               r = bin_app(r, rest[i])
            end
            return r
   end)
end

binder_macro("for", Const("ForallIntro"), 3, 1, 3)
binder_macro("assume", Const("Discharge"), 3, 1, 3)
nary_macro("instantiate", Const("ForallElim"), 4)
nary_macro("mp", Const("MP"), 4)
