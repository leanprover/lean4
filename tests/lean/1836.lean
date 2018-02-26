structure pType :=
  (carrier : Type)
  (Point   : carrier)

structure pmap (A B : pType) : Type :=
 (f : A.carrier → B.carrier)
 (p : f A.Point = B.Point)

def ex1 {A B : pType} (f : pmap A B) : f = f :=
begin
  induction B with B b, induction f with f pf,
  cases pf -- should fail because of dependency
end

def ex2 {A B : pType} (f : pmap A B) : f = f :=
begin
  induction B with B b, induction f with f pf,
  dsimp at f, /- break dependency using reduction -/
  cases pf,
  refl
end
