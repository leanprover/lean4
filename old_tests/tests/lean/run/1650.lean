def A : inhabited true → Type | ⟨t⟩ := inhabited (t = t)
def B (T : Type) (t : T) : Prop := t = t
def C {T x} : B T x := rfl

structure X :=
  ( x : inhabited true )
  ( y : A x )
  ( z : B _ y )

def test : X := {
    x := ⟨let t := trivial in t⟩,
    y := sorry,
    z := C
}

constant T : nat → Type
open tactic

example : true :=
by do
  let t1 : expr := `(sorry : T (1+1)),
  let t2 : expr := `(sorry : T 2),
  is_def_eq t1 t2,
  constructor
