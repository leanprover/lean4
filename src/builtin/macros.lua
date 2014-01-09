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
function binder_macro(name, f, farity, typepos, lambdapos)
   local precedence = 0
   macro(name, { macro_arg.Parameters, macro_arg.Comma, macro_arg.Expr },
         function (env, bindings, body)
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
         end,
         precedence)
end

-- The following macro is used to create nary versions of operators such as mp.
-- Example: suppose we invoke
--
--    nary_macro("eqmp'", Const("eqmp"), 4)
--
-- Then, the macro expression
--
--     eqmp' Foo H1 H2 H3
--
-- produces the expression
--
--     (eqmp (eqmp (eqmp Foo H1) H2) H3)
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
         function (env, e1, e2, rest)
            local r = bin_app(e1, e2)
            for i = 1, #rest do
               r = bin_app(r, rest[i])
            end
            return r
   end)
end

-- exists::elim syntax-sugar
-- Example:
-- Assume we have the following two axioms
--      Axiom Ax1: exists x y, P x y
--      Axiom Ax2: forall x y, not P x y
-- Now, the following macro expression
--    obtain (a b : Nat) (H : P a b) from Ax1,
--         have false : absurd H (instantiate Ax2 a b)
-- expands to
--    exists::elim Ax1
--        (fun (a : Nat) (Haux : ...),
--           exists::elim Haux
--              (fun (b : Na) (H : P a b),
--                   have false : absurd H (instantiate Ax2 a b)
macro("obtain", { macro_arg.Parameters, macro_arg.Comma, macro_arg.Id, macro_arg.Expr, macro_arg.Comma, macro_arg.Expr },
      function (env, bindings, fromid, exPr, body)
         local n = #bindings
         if n < 2 then
            error("invalid 'obtain' expression at least two bindings must be provided")
         end
         if fromid ~= name("from") then
            error("invalid 'obtain' expression, 'from' keyword expected, got '" .. tostring(fromid) .. "'")
         end
         local exElim = mk_constant({"exists", "elim"})
         local H_name = bindings[n][1]
         local H_type = bindings[n][2]
         local a_name = bindings[n-1][1]
         local a_type = bindings[n-1][2]
         for i = n - 2, 1, -1 do
            local Haux = name("obtain", "macro", "H", i)
            body = mk_app(exElim, mk_placeholder(), mk_placeholder(), mk_placeholder(), mk_constant(Haux),
                          fun(a_name, a_type, fun(H_name, H_type, body)))
            H_name = Haux
            H_type = mk_placeholder()
            a_name = bindings[i][1]
            a_type = bindings[i][2]
            -- We added a new binding, so we must lift free vars
            body = body:lift_free_vars(0, 1)
         end
         -- exPr occurs after the bindings, so it is in the context of them.
         -- However, this is not the case for ExistsElim.
         -- So, we must lower the free variables there
         exPr = exPr:lower_free_vars(n, n)
         return mk_app(exElim, mk_placeholder(), mk_placeholder(), mk_placeholder(), exPr,
                       fun(a_name, a_type, fun(H_name, H_type, body)))
      end,
      0)
