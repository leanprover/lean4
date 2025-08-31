/-!
# Interactive tests of dotted ident notation (`.f x y z`)
-/

/-!
Basic tests
-/

inductive MyNat
  | zero | succ (n : MyNat)

example : MyNat := .ze
                    --^ textDocument/completion

example : MyNat → MyNat := .su
                            --^ textDocument/completion

/-!
Unfolding a type
-/

def MyNat' := MyNat

example : MyNat' := .ze
                     --^ textDocument/completion

example : MyNat' → MyNat' := .su
                              --^ textDocument/completion

/-!
Seeing through type annotations
-/

example : outParam MyNat := .ze
                             --^ textDocument/completion

-- Definitions that are in the annotation's namespace are *not* reported
def outParam.baz : MyNat := .zero
example : outParam MyNat := .ba
                             --^ textDocument/completion

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
                      --^ textDocument/completion
example : MyNat := .zero' -- it successfully elaborates

/-!
Open namespaces are currently not supported
-/

namespace MyLib
def MyNat.succ' : MyNat → MyNat := .succ
end MyLib

open MyLib in
example : MyNat → MyNat := .succ
                              --^ textDocument/completion
open MyLib in
example : MyNat → MyNat := .succ' -- it successfully elaborates
