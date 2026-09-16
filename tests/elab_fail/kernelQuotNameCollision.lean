prelude

/-!
The kernel must reject `init_quot` when one of the quotient primitives is already declared.

`add_quot` adds `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind` with a raw insert, so without a name
check it silently replaced whatever occupied those names. A declaration checked against the old
constant then stayed in the environment, ill typed and with no axiom dependency to show for it.

`init_quot` runs here because a `prelude` module with no imports has not initialized the quotient
module yet.

**Note**: Comparator also catches this kind of exploit.
-/

inductive False : Prop

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

axiom Quot.lift : False

theorem bad : False := Quot.lift

init_quot

#print axioms bad
