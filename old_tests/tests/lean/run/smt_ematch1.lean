constant f : nat → nat
axiom fax : ∀ x, f x = x

attribute [ematch] fax

lemma ex1 (a b c : nat) : f a = b → b = f c → a = c :=
begin [smt]
  intros,
  trace_state,
  ematch
end

constant g : nat → nat → nat
axiom gax : ∀ x, g x x = x

lemma ex2 (a b c d e : nat) : d = a → c = e → g a d = b → b = g e c → f a = c :=
begin [smt]
  intros,
  add_lemma gax,
  ematch
end

lemma ex3 (a b c d e : nat) : d = a → c = e → g a d = b → b = g e c → f a = c :=
begin [smt]
  intros,
  ematch_using [fax, gax]
end

local attribute [-ematch] fax

lemma ex4 (a b c d e : nat) : d = a → c = e → g a d = b → b = g e c → f a = c :=
begin [smt]
  intros,
  add_lemma [fax, gax],
  ematch
end

lemma ex5 (a b c d e : nat) : d = a → c = e → g a d = b → b = g e c → f a = c :=
begin [smt]
  intros,
  ematch_using [fax, gax]
end

lemma ex6 (a b c d e : nat) : (∀ x, g x (f x) = 0) → a = f b → g b a + 0 = f 0 :=
begin [smt]
   intros,
   have h : ∀ x, g x (f x) = 0,
   add_lemma [h, fax, add_zero],
   ematch
end

lemma ex7 (a b c d e : nat) : (∀ x, g x (f x) = 0) → a = f b → g b a + 0 = f 0 :=
begin [smt]
   intros,
   have h : ∀ x, g x (f x) = 0,
   ematch_using [h, fax, add_zero]
end

local attribute [ematch] fax add_zero

open smt_tactic

lemma ex8 (a b c d e : nat) : (∀ x, g x (f x) = 0) → a = f b → g b a + 0 = f 0 :=
begin [smt]
  intros,
  add_lemmas_from_facts,
  ematch
end

lemma ex9 (a b c d e : nat) : d ≠ e → (∀ x, g x (f x) = 0) → a = f b → g b a + 0 = f 0 :=
begin [smt]
  intros,
  get_facts >>= trace,
  get_refuted_facts >>= trace,
  add_lemmas_from_facts,
  ematch
end
