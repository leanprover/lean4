module

/-!
Test for `unif_hint` under the module system
-/

@[expose] public def Type1 := Fin
@[expose] public def Type2 := Fin

/-!
`Type1` gets a public unification hint and `Type2` a private unification hint.
-/

unif_hint (n : Nat) where ⊢ Type1 n =?= Fin n

local unif_hint (n : Nat) where ⊢ Type2 n =?= Fin n

/-!
Both unification hints work in a private context
-/

def privateTest1 (x : Fin 2) : Type1 2 := by with_reducible exact x
def privateTest2 (x : Fin 2) : Type2 2 := by with_reducible exact x

/-!
The public hint also works in a public context
-/

@[expose]
public def publicTest1 (x : Fin 2) : Type1 2 := by with_reducible exact x

/-!
The private hint does not work in a public context, producing a type mismatch error.

It previously produced an unknown constant error, see https://github.com/leanprover/lean4/issues/14734
-/

/--
error: Type mismatch
  x
has type
  Fin 2
but is expected to have type
  Type2 2
-/
#guard_msgs in
@[expose]
public def publicTest2 (x : Fin 2) : Type2 2 := by with_reducible exact x

/-!
If the unification hint cannot be used but there is an alternative way to show definitional
equality, definitional equality still succeeds.
-/

@[reducible, expose]
public def Ignore (_α : Type) : Type := Unit

@[expose]
public def publicTest2' (x : Ignore (Fin 2)) : Ignore (Type2 2) := by with_reducible exact x
