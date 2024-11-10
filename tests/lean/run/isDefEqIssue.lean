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


class Foo (a b : Nat) (h : a = b) (β : Nat → Type) where
  val : β a

@[default_instance]
instance (a b : Nat) (h : a = b) : Foo a b h Fin where
  val := sorry

/--
this used to give
typeclass instance problem is stuck, it is often due to metavariables
  Foo a Nat.zero h (?m.734 h)
-/
example :=
  let a : Nat := Nat.zero
  fun (h : a = Nat.zero) => Foo.val h
