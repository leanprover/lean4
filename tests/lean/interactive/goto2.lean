set_option trace.Elab.info true
mutual

def h (x : Nat) : Int:=
  match x with
  | 0 => 1
             --v textDocument/definition
  | x+1 => r x + r x + h x ^ 2
                         --^ textDocument/definition
         --^ textDocument/definition

def r (x : Nat) := x + 1
end
