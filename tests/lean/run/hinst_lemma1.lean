open tactic

constant p : nat → nat → Prop
constant q : nat → nat → Prop
constant r : nat → nat → Prop

axiom foo : ∀ a b c : nat, p a b → q b c → q a c → r a c
axiom boo : ∀ a b c : nat, p a b → (:q b c:) → q a c → (:r a c:)

meta def pp_lemma (n : name) : tactic unit :=
do h ← hinst_lemma.mk_from_decl n,
   h^.pp >>= trace

example : true :=
by do
  pp_lemma `add_assoc,
  pp_lemma `foo,
  pp_lemma `boo,
  constructor
