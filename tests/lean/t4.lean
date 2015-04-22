prelude definition Prop : Type.{1} := Type.{0}
constant N : Type.{1}
check N
constant a : N
check a
check Prop → Prop
constant F.{l} : Type.{l} → Type.{l}
check F.{2}
universe u
check F.{u}
constant vec.{l} (A : Type.{l}) (n : N) : Type.{l}
constant f (a b : N) : N
constant len.{l} (A : Type.{l}) (n : N) (v : vec.{l} A n) : N
check f
check len.{1}
section
   parameter A  : Type
   parameter B  : Prop
   hypothesis H : B
   parameter {C : Type}
   check B -> B
   check A → A
   check C
end
check A -- Error: A is part of the section

constant R : Type → Type
check R.{1 0}

check fun x y : N, x

namespace tst
  constant N : Type.{2}
  constant M : Type.{2}
  print raw N -- Two possible interpretations N and tst.N
  print raw tst.N -- Only one interpretation
end tst
print raw N -- Only one interpretation
namespace foo
  constant M : Type.{3}
  print raw M -- Only one interpretation
end foo
check tst.M
check foo.M
namespace foo
  check M
end foo
check M -- Error

print "ok"
(*
local env = get_env()
print("Declarations:")
env:for_each_decl(function(d) print(d:name()) end)
print("-------------")
*)

universe l_1
constant T1 : Type -- T1 parameter is going to be called l_2
