new_frontend

open Lean

syntax [myintro] "intros" (sepBy ident ",") : tactic

macro_rules [myintro]
| `(tactic| intros $x*) => pure $ Syntax.node `Lean.Parser.Tactic.intros #[Syntax.atom none "intros", mkNullNode x.getSepElems]

theorem tst1 {p q : Prop} : p → q → p :=
begin
  intros h1, h2;
  assumption
end

theorem tst2 {p q : Prop} : p → q → p :=
begin
  intros h1; -- the builtin and myintro overlap here.
  intros h2; -- the builtin and myintro overlap here.
  assumption
end

theorem tst3 {p q : Prop} : p → q → p :=
begin
  intros h1 h2;
  assumption
end
