open Lean

syntax (name := myintro) "intros" sepBy(ident, ",") : tactic

macro_rules (kind := myintro)
| `(tactic| intros $x,*) => pure $ Syntax.node `Lean.Parser.Tactic.intros #[mkAtom "intros", mkNullNode x]

theorem tst1 {p q : Prop} : p → q → p :=
by {
  intros h1, h2;
  assumption
}

theorem tst2 {p q : Prop} : p → q → p :=
by {
  intros h1; -- the builtin and myintro overlap here.
  intros h2; -- the builtin and myintro overlap here.
  assumption
}

theorem tst3 {p q : Prop} : p → q → p :=
by {
  intros h1 h2;
  assumption
}
