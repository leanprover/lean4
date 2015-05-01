import data.set

example {A : Type} (H : set A) (a x : A) (p : a = x) (l : H x) : H a :=
begin
  rewrite p, exact l
end
