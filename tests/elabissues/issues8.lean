def forceNat (a : Nat) := true
def forceInt (a : Int) := false

def f1 :=
/-
The following example works, but it adds a coercion at `forceInt i`.
The elaborated term is
```
fun (n i : Nat) => if n == i then forceNat n else forceInt (coe i)
-/
fun n i => if n == i then forceNat n else forceInt i -- works

def f2 :=
fun n i => if coe n == i then forceInt i else forceNat n -- works

#check f1 -- Nat → Nat → Bool
#check f2 -- Nat → Int → Bool

def f3 :=
/- Fails.
   - `n == i` generates type constraint enforcing `n` and `i` to have the same type.
   - `forceInt i` forces `i` (and consequently `n`) to have type `Int`.
   - `forceNat n` fails because there is no coercion from `Nat` to `Int`. -/
fun n i => if n == i then forceInt i else forceNat n
