import("util.lua")

function pibody(e)
   while (e:is_pi()) do
      local _, _, r = e:fields()
      e = r
   end
   return e
end

function funbody(e)
   while (e:is_lambda()) do
      local _, _, r = e:fields()
      e = r
   end
   return e
end

function hoptst(rule, target, expected, perfect_match, no_env)
   if expected == nil then
      expected = true
   end
   local th  = parse_lean(rule)
   local p   = pibody(th):arg(2)
   local t   = funbody(parse_lean(target))
   local r
   if no_env then
      r = hop_match(p, t, nil)
   else
      r = hop_match(p, t)
   end
   -- print(p, t)
   if (r and not expected) or (not r and expected) then
      error("test failed: " .. tostring(rule) .. " === " .. tostring(target))
   end
   if r then
      local s = p:instantiate(r):beta_reduce()
      print "Solution:"
      for i = 1, #r do
         print("#" .. tostring(i) .. " <--- " .. tostring(r[i]))
      end
      print ""
      if perfect_match then
         t = t:beta_reduce()
         if s ~= t then
            print("Mismatch")
            print(s)
            print(t)
         end
         assert(s == t)
      end
   end
end

parse_lean_cmds([[
  variable f : Nat -> Nat -> Nat
  variable g : Nat -> Nat
  variable p : Nat -> Bool
  variable n : Nat
]])

hoptst([[forall (h : Nat -> Nat), (forall x : Nat, h 0 = h x) = true]],
       [[fun (ff : Nat -> Nat), forall x : Nat, ff 0 = ff x]])

hoptst([[forall (h : Nat -> Nat -> Nat) (a : Nat), (forall x : Nat, (h x a) = a) = true]],
       [[fun (a b c : Nat), (forall x : Nat, (f x b) = b)]])

hoptst([[forall (A : TypeU) (P Q : A -> Bool), (forall x : A, P x /\ Q x) = ((forall x : A, P x) /\ (forall x : A, Q x))]],
       [[forall x : Nat, p (f x 0) /\ f (f x x) 1 >= 0]])

hoptst([[forall (F G : Nat -> Nat), (forall x y : Nat, F x = x /\ G y = y) = (F = G)]],
       [[(forall x y : Nat, f x (g x) = x /\ g (g (g y)) = y)]])

hoptst([[forall (F G : Nat -> Nat), (forall x y : Nat, F x = x /\ G y = y) = (F = G)]],
       [[fun (a b c : Nat), (forall x y : Nat, f x (f (g b) c) = x /\ (f (g (g (f y c))) a) = y)]])

hoptst([[forall (a b c : Bool), ((a /\ b) /\ c) = (a /\ (b /\ c))]],
       [[fun (p1 p2 p3 p4 p5 : Bool), (((p1 ∧ p2) ∧ p3) ∧ (p4 ∧ p2))]])

hoptst([[forall (F G : Nat -> Bool), (forall x : Nat, F x = (F x ∧ G x)) = (F = G)]],
       [[forall x : Nat, p (f x x) = (p (f x x) ∧ p (f x 0))]])

hoptst([[forall (F G : Nat -> Bool), (forall x : Nat, F x = (F x ∧ G x)) = (F = G)]],
       [[forall x : Nat, p (f x x) = (p (f (g x) x) ∧ p (f x 0))]], false)

hoptst([[forall (F G : Nat -> Nat), (forall x y : Nat, F x = x /\ G y = y) = (F = G)]],
       [[fun (a b c : Nat), (forall x y : Nat, f x (f (g y) c) = x /\ (f (g (g (f y c))) a) = y)]], false)

hoptst([[forall (a : Bool), (a /\ true) = a]],
       [[fun (p1 p2 p3 : Bool), (p1 /\ p2) /\ true]])

hoptst([[forall (a : Bool), (a /\ true) = a]],
       [[fun (p1 p2 p3 : Bool), (p1 /\ p2) /\ false]], false)

hoptst([[forall (h : Nat -> Nat) (a : Nat), (h a) = a]],
       [[fun (a b c : Nat), f a b]])

hoptst([[forall (a : Nat), (g a) = a]],
       [[fun (a b c : Nat), f a b]], false)

hoptst([[forall (A : Type) (a : A), (a = a) = true]],
       [[fun (a b : Nat), b = b]])

hoptst([[forall (h : Nat -> Nat), (forall x : Nat, h x = h 0) = true]],
       [[fun (ff : Nat -> Nat), forall x : Nat, ff x = ff 0]])

hoptst([[forall (h : Nat -> Nat), (forall x : Nat, h x = h 0) = true]],
       [[fun (ff : Nat -> Nat) (a b c : Nat), forall x : Nat, ff x = ff 0]])

hoptst([[forall (h : Nat -> Nat -> Bool), (forall x : Nat, h x x) = true]],
       [[fun (a b : Nat), forall x : Nat, f x x]])

hoptst([[forall (h : Nat -> Nat -> Bool), (forall x : Nat, h x x) = true]],  -- this is not a higher-order pattern
       [[fun (a b : Nat), forall x : Nat, f (f x) (f x)]], false)

hoptst([[forall (h : Nat -> Nat -> Bool), (forall x : Nat, h n x) = true]],
       [[fun (ff : Nat -> Nat -> Bool) (a b : Nat), forall x : Nat, ff n x]])

hoptst([[forall (h : Nat -> Nat -> Bool), (forall x : Nat, h n x) = true]],  -- this is not a higher-order pattern
       [[fun (ff : Nat -> Nat -> Bool) (a b : Nat), forall x : Nat, ff n (g x)]], false)

hoptst([[forall (h : Nat -> Bool), (forall x y : Nat, h x) = true]],
       [[fun (a b : Nat), forall x y : Nat,  (fun z : Nat, z + x) (fun w1 w2 : Nat, w1 + w2 + x)]])

hoptst([[forall (h : Nat -> Bool), (forall x y : Nat, h y) = true]],
       [[fun (a b : Nat), forall x y : Nat,  (fun z : Nat, z + y) (fun w1 w2 : Nat, w1 + w2 + y)]])

parse_lean_cmds([[
   definition ww := 0
]])

hoptst('ww = 0', '0', true, false)
hoptst('ww = 0', '0', false, false, true)
