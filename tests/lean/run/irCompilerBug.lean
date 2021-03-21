--

structure Payload :=
(key : Nat)
(val : Nat)



@[noinline] def get? (p : Payload) (k : Nat) : OptionM Nat :=
if p.key == k then p.val else none

inductive T
| a (i : Nat)
| b (i : Nat)
| c (i : Nat)
| d (i : Nat)

@[noinline] def foo (p : Payload) : OptionM T :=
(do
  let i ← get? p 1;
  pure (T.a i))
<|> (do
  let i ← get? p 2;
  pure (T.b i))
<|> (do
  let i ← get? p 3;
  pure (T.c i))
<|> (do
  let i ← get? p 4;
  let i ← get? p 5;
  pure (T.d i))

def wrongOutput : String :=
match foo (Payload.mk 1 20) with
| some (t : T) =>
  match t with
  | T.a i => "1: " ++ toString i
  | T.b i => "2: " ++ toString i
  | T.c i => "3: " ++ toString i
  | T.d i => "4: " ++ toString i
| none => "5"

#eval wrongOutput

def main (xs : List String) : IO Unit :=
IO.println wrongOutput
