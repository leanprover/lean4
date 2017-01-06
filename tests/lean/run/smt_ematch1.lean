constant f : nat → nat
axiom fax : ∀ x, f x = x

attribute [ematch] fax

example (a b c : nat) : f a = b → b = f c → a = c :=
begin [smt]
  trace_state,
  ematch
end

constant g : nat → nat → nat
axiom gax : ∀ x, g x x = x

example (a b c d e : nat) : d = a → c = e → g a d = b → b = g e c → f a = c :=
begin [smt]
  add_lemma gax,
  ematch
end

example (a b c d e : nat) : d = a → c = e → g a d = b → b = g e c → f a = c :=
begin [smt]
  ematch_using [fax, gax]
end

local attribute [-ematch] fax

example (a b c d e : nat) : d = a → c = e → g a d = b → b = g e c → f a = c :=
begin [smt]
  add_lemma [fax, gax],
  ematch
end

example (a b c d e : nat) : d = a → c = e → g a d = b → b = g e c → f a = c :=
begin [smt]
  ematch_using [fax, gax]
end

example (a b c d e : nat) : (∀ x, g x (f x) = 0) → a = f b → g b a + 0 = f 0 :=
begin [smt]
   assert h : ∀ x, g x (f x) = 0,
   add_lemma [h, fax, add_zero],
   ematch
end

example (a b c d e : nat) : (∀ x, g x (f x) = 0) → a = f b → g b a + 0 = f 0 :=
begin [smt]
   assert h : ∀ x, g x (f x) = 0,
   ematch_using [h, fax, add_zero]
end

local attribute [ematch] fax add_zero

open smt_tactic

example (a b c d e : nat) : (∀ x, g x (f x) = 0) → a = f b → g b a + 0 = f 0 :=
begin [smt]
  add_lemmas_from_facts,
  ematch
end

example (a b c d e : nat) : d ≠ e → (∀ x, g x (f x) = 0) → a = f b → g b a + 0 = f 0 :=
begin [smt]
  get_facts >>= trace,
  get_refuted_facts >>= trace,
  add_lemmas_from_facts,
  ematch
end
