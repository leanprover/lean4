section

parameter T : Type

def eqT : T -> T ->  Prop
| t1 t2 := t1 = t2

lemma sm : forall t1 t2,
eqT t1 t2 ->
t1 = t2 :=
begin
intros,
simp [eqT] at a,
assumption
end

end
