inductive is_some {A : Type} (mx : option A)  : Prop
  | mk : ∀ x : A, mx = some x → is_some

lemma foo {A : Type} (x : A) (mx : option A)
  (H : mx = some x)
  : is_some mx
:= begin
existsi x, assumption
end

set_option pp.all true
set_option pp.beta false
set_option pp.instantiate_mvars false

-- same lemma as above
lemma foo' {A : Type} (x : A) (mx : option A)
  (H : mx = some x)
  : is_some mx
:= begin
apply (if true then _ else _), -- in this case, we branch first
{ existsi x, assumption },
{ existsi x, assumption }
end
