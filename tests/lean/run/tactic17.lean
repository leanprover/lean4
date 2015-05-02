import logic
open tactic

constant A : Type.{1}
constant f : A → A → A

theorem tst {a b c : A} (H1 : a = b) (H2 : b = c) : f a b = f b c :=
begin
  apply (@congr A A (f a) (f b)),
  assumption,
  apply (congr_arg f),
  assumption
end
