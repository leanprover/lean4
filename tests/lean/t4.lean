definition Prop [inline] : Type.{1} := Type.{0}
variable N : Type.{1}
check N
variable a : N
check a
check Prop → Prop
variable F.{l} : Type.{l} → Type.{l}
check F.{2}
universe u
check F.{u}
variable vec.{l} (A : Type.{l}) (n : N) : Type.{l}
variable f (a b : N) : N
variable len.{l} (A : Type.{l}) (n : N) (v : vec.{l} A n) : N
check f
check len.{1}
section
   variable A  : Type
   variable B  : Prop
   hypothesis H : B
   parameter {C : Type}
   check B -> B
   check A → A
   check C
end
check A -- Error: A is part of the section

variable R : Type → Type
check R.{1 0}

check fun x y : N, x

namespace tst
  variable N : Type.{2}
  variable M : Type.{2}
  print raw N -- Two possible interpretations N and tst.N
  print raw tst.N -- Only one interpretation
end
print raw N -- Only one interpretation
namespace foo
  variable M : Type.{3}
  print raw M -- Only one interpretation
end
check tst.M
check foo.M
namespace foo
  check M
end
check M -- Error

print "ok"
(*
local env = get_env()
print("Declarations:")
env:for_each_decl(function(d) print(d:name()) end)
print("-------------")
*)

universe l_1
variable T1 : Type -- T1 parameter is going to be called l_2
