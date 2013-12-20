(**
 -- This example demonstrates how to create Macros for automating proof
 -- construction using Lua.

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
**)

Definition Set (A : Type) : Type := A → Bool

Definition element {A : Type} (x : A) (s : Set A) := s x
Infix 60 ∈ : element

Definition subset {A : Type} (s1 : Set A) (s2 : Set A) := ∀ x, x ∈ s1 ⇒ x ∈ s2
Infix 50 ⊆ : subset

Theorem SubsetTrans (A : Type) : ∀ s1 s2 s3 : Set A, s1 ⊆ s2 ⇒ s2 ⊆ s3 ⇒ s1 ⊆ s3 :=
   for s1 s2 s3, assume (H1 : s1 ⊆ s2) (H2 : s2 ⊆ s3),
      show s1 ⊆ s3,
        for x, assume Hin : x ∈ s1,
           show x ∈ s3,
             let L1 : x ∈ s2 := mp (instantiate H1 x) Hin
             in mp (instantiate H2 x) L1
