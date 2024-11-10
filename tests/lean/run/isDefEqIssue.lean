opaque getA (s : String) : Array String := #[]

private def resolveLValAux (s : String) (i : Nat) : Nat :=
  let s1 := s
  let as := getA s1
  if h : i < as.size then
    i - 1
  else
    i

/--
this used to give
(kernel) declaration has free variables '_example'
-/
example : Unit :=
  let x : Nat → Unit := _
  let N := Nat;
  (fun a : N =>
    have : x a = () := rfl
    ()) Nat.zero

/--
this used to give
(kernel) declaration has free variables '_example'
-/
example : IO Unit := do
 pure ()
 match some () with
 | some u => do
  let pair := match () with | _ => ((),())
  let i := ()
  if h : i = pair.1 then
   let k := 0
 | _ => return
