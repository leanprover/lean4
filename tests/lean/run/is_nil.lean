import logic
using tactic

inductive list (A : Type) : Type :=
nil {} : list A,
cons   : A → list A → list A

definition is_nil {A : Type} (l : list A) : Prop
:= list_rec true (fun h t r, false) l

theorem is_nil_nil (A : Type) : is_nil (@nil A)
:= eq_true_elim (refl true)

theorem cons_ne_nil {A : Type} (a : A) (l : list A) : ¬ cons a l = nil
:= not_intro (assume H : cons a l = nil,
     absurd
       (calc true = is_nil (@nil A)   : refl _
              ... = is_nil (cons a l) : { symm H }
              ... = false             : refl _)
       true_ne_false)

theorem T : is_nil (@nil Prop)
:= by apply is_nil_nil

(*
local list   = Const("list", {1})(Prop)
local isNil = Const("is_nil", {1})(Prop)
local Nil   = Const("nil", {1})(Prop)
local m     = mk_metavar("m", list)
print(isNil(Nil))
print(isNil(m))


function test_unify(env, m, lhs, rhs, num_s)
   print(tostring(lhs) .. " =?= " .. tostring(rhs) .. ", expected: " .. tostring(num_s))
   local ss = unify(env, lhs, rhs, name_generator(), substitution())
   local n  = 0
   for s in ss do
      print("solution: " .. tostring(s:instantiate(m)))
      n = n + 1
   end
   if num_s ~= n then print("n: " .. n) end
   assert(num_s == n)
end
print("=====================")
test_unify(get_env(), m, isNil(Nil), isNil(m), 2)
*)
