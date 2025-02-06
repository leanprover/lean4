def Vect (n: Nat) (A: Type u) := {l: List A // l.length = n}

def Vect.cons (a: A) (v: Vect n A): Vect (n + 1) A :=
  ⟨a::v.val, by simp [v.property]⟩

instance: GetElem (Vect n A) Nat A (λ _ i => i < n) where
  getElem vec i _ := match vec with | ⟨l, _⟩ => l[i]

set_option pp.mvars false
/--
error: type mismatch
  xm[i]
has type
  Vect m A : outParam (Type _)
but is expected to have type
  A : outParam (Type _)
---
error: type mismatch, term
  ih
after simplification has type
  i < as.length : Prop
but is expected to have type
  ?_ : Type _
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
A : Type _
m i j : Nat
as : List A
xm : List (Vect m A)
h0 : xm.length = as.length
ih : i < (List.zipWith cons as xm).length
jh : j < m
⊢ ?_ sorry j
-/
#guard_msgs in
theorem Vect.aux
    {as: List A} {xm: List (Vect m A)}
    (h0: xm.length = as.length)
    (ih: i < (List.zipWith cons as xm).length)
    (jh: j < m)
    : ((List.zipWith cons as xm)[i])[j + 1] =
        xm[i]'(by simpa[h0] using ih)[j] := by
        -- Correct syntax requires an extra pair of parentheses:
        -- (xm[i]'(by simpa[h0] using ih))[j]
        -- but `lean` should not crash.
  sorry
