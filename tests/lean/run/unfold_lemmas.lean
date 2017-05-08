open nat well_founded

def gcd.F : Π (y : ℕ), (Π (y' : ℕ), y' < y → nat → nat) → nat → nat
| 0        f x := x
| (succ y) f x := f (x % succ y) (mod_lt _ $ succ_pos _) (succ y)

def gcd (x y : nat) := fix lt_wf gcd.F y x

set_option type_context.unfold_lemmas true
@[simp] lemma gcd_zero_right (x : nat) : gcd x 0 = x := rfl
