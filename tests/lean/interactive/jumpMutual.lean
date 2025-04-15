mutual
--^ waitForILeans
def h (x : Nat) : Nat :=
  match x with
  | 0 => 1
                     --v textDocument/definition
               --v textDocument/definition
  | x+1 => f x + r x + h x
         --^ textDocument/definition
where
  r : Nat → Nat
  | 0 => 1
           --v textDocument/definition
  | x + 1 => r x * h x
                 --^ textDocument/definition

def f (x : Nat) : Nat :=
  let rec g : Nat → Nat
    | 0 => 1
               --v textDocument/definition
    | n+1 => 2 * g n
--v textDocument/definition
  g x + h x
      --^ textDocument/definition
end
