open tactic

lemma test1 (x y z : Prop) (f : x → y → z) (xp : x) (yp : y) : z :=
begin
    specialize (f xp yp), assumption
end

lemma test2 (B C : Prop) (f : forall (A : Prop), A → C) (x : B) : C :=
begin
  specialize f _ x, exact f,
end

lemma test3 (B C : Prop) (f : forall {A : Prop}, A → C) (x : B) : C :=
begin
  specialize (f x), exact f,
end

lemma test4 (B C : Prop) (f : forall {A : Prop}, A → C) (x : B) : C :=
begin
  specialize (@f _ x), exact f,
end

lemma test5 (X : Type) [has_add X] (f : forall {A : Type} [has_add A], A → A → A) (x : X) : X :=
begin
  specialize (f x x), assumption
end
