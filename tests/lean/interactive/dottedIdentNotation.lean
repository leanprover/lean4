/-!
# Interactive tests of dotted ident notation (`.f x y z`)
-/

/-!
Basic tests
-/

inductive MyNat
  | zero | succ (n : MyNat)

example : MyNat := .ze
                    --^ completion

example : MyNat → MyNat := .su
                            --^ completion

/-!
Unfolding a type
-/

def MyNat' := MyNat

example : MyNat' := .ze
                     --^ completion

example : MyNat' → MyNat' := .su
                              --^ completion

/-!
Seeing through type annotations
-/

example : outParam MyNat := .ze
                             --^ completion

-- Definitions that are in the annotation's namespace are *not* reported
def outParam.baz : MyNat := .zero
example : outParam MyNat := .ba
                             --^ completion

/-!
Aliases are currently not supported
-/
namespace MyLib
def MyNat.zero' : MyNat := .zero
end MyLib
namespace MyNat
export MyLib.MyNat (zero')
end MyNat

example : MyNat := .zero
                      --^ completion
example : MyNat := .zero' -- it successfully elaborates

/-!
Open namespaces are currently not supported
-/

namespace MyLib
def MyNat.succ' : MyNat → MyNat := .succ
end MyLib

open MyLib in
example : MyNat → MyNat := .succ
                              --^ completion
open MyLib in
example : MyNat → MyNat := .succ' -- it successfully elaborates
