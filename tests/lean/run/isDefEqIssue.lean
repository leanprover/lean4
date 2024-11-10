opaque getA (s : String) : Array String := #[]

private def resolveLValAux (s : String) (i : Nat) : Nat :=
  let s1 := s
  let as := getA s1
  if h : i < as.size then
    i - 1
  else
    i


/--
This used to give
(kernel) declaration has free variables '_example'
-/
example : Unit :=
  let x : Nat → Unit := _
  let N := Nat;
  (fun a : N =>
    have : x a = () := rfl
    ()) Nat.zero


/--
This used to give
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


/-
This used to give
(kernel) declaration has free variables '_example'
-/
/--
error: type mismatch
  rfl
has type
  x b a = x b a : Prop
but is expected to have type
  x b a = Nat.zero : Prop
-/
#guard_msgs in
example : Unit :=
  let x : Nat → Nat → Nat := _
  (fun (a : Nat) (b : let _ := a; Nat) =>
    have : x b a = Nat.zero := rfl
    ()
    ) Nat.zero Nat.zero

class Foo (a b : Nat) (h : a = b) (β : Nat → Type) where
  val : β a

@[default_instance]
instance (a b : Nat) (h : a = b) : Foo a b h Fin where
  val := sorry

/--
This used to give
typeclass instance problem is stuck, it is often due to metavariables
  Foo a Nat.zero h (?m.734 h)
-/
example :=
  let a : Nat := Nat.zero
  fun (h : a = Nat.zero) => Foo.val h
