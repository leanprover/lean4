/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP
public import Std.Internal.Do.ExceptPost
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

/-!
# Hoare triples

Hoare triples form the basis for compositional functional correctness proofs about monadic programs.

As usual, `Triple x pre post epost` holds iff the precondition `pre` entails the weakest
precondition `wp x post epost` of `x : m α` for the postcondition `post` and error
postcondition `epost`.
It is thus defined in terms of an instance `WPMonad m Pred EPred`.
-/

namespace Std.Internal.Do

universe u v
variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u}

/-- A Hoare triple for reasoning about programs. A Hoare triple `Triple x pre post epost`
is a *specification* for `x`: if assertion `pre` holds before `x`, then postcondition `post` holds
after running `x` (and `epost` handles any errors). -/
structure Triple {Prog : Type v} {Value : Type u} [Assertion Pred] [Assertion EPred] (x : Prog) [WP Prog Value Pred EPred] (pre : Pred) (post : Value → Pred) (epost : EPred) : Prop where
  /-- Construct a triple from a weakest precondition entailment. -/
  intro ::
  /-- The weakest precondition entailment witnessing the triple. -/
  le_wp : pre ⊑ wp x post epost

open Lean in
/-- A program whose `match`/`if`/`do` elaboration postpones on a metavariable expected type and so
needs the monadic-application hint `(_ : _ → _) _` to recover its monad by first-order unification. -/
private meta partial def isSplitProgram (c : Syntax) : Bool :=
  if c.isOfKind `Lean.Parser.Term.paren then
    isSplitProgram c[1]
  else
    c.isOfKind `Lean.Parser.Term.match ||
    c.isOfKind `termIfThenElse ||
    c.isOfKind `termDepIfThenElse ||
    c.isOfKind `Lean.Parser.Term.do

open Lean in
/-- Ascribe the program so its monad can be recovered during elaboration. An explicit `(m := …)`
ascribes the program to `… _`, supplying the monad head directly. Otherwise a `match`/`if`/`do`
program gets the monadic-application hint `(_ : _ → _) _`, recovering its monad by first-order
unification. Other programs are untouched. -/
private meta def hintProgram (c : Term) (m? : Option Term) : MacroM Term :=
  match m? with
  | some m => `(($c : $m _))
  | none => if isSplitProgram c.raw then `(($c : (_ : _ → _) _)) else pure c

/-- Hoare triple notation without exception postcondition (defaults to `⊥`). An optional `(m := …)`
after the precondition ascribes the program to monad `…`. -/
scoped syntax:60 (name := tripleNotation)
  "⦃ " term " ⦄ " (atomic("(" ident " := ") term ")")? term " ⦃ " term " ⦄" : term
/-- Hoare triple notation with a binder for the return value. -/
scoped syntax:60 (name := tripleBinderNotation)
  "⦃ " term " ⦄ " (atomic("(" ident " := ") term ")")? term " ⦃ " ident ", " term " ⦄" : term
/-- Hoare triple notation with an exception postcondition:
`⦃ P ⦄ x ⦃ Q; E ⦄ := Triple x P Q E`. -/
scoped syntax:60 (name := tripleEPost)
  "⦃ " term " ⦄ " (atomic("(" ident " := ") term ")")? term " ⦃ " term "; " term " ⦄" : term
/-- Hoare triple notation with a binder for the return value and an exception postcondition. -/
scoped syntax:60 (name := tripleBinderEPost)
  "⦃ " term " ⦄ " (atomic("(" ident " := ") term ")")? term " ⦃ " ident ", " term "; " term " ⦄" : term

macro_rules (kind := tripleNotation)
  | `(⦃ $P ⦄ $[(m := $m)]? $c ⦃ $Q ⦄) => do `(Triple $(← hintProgram c m) $P $Q Lean.Order.bot)
macro_rules (kind := tripleBinderNotation)
  | `(⦃ $P ⦄ $[(m := $m)]? $c ⦃ $v, $Q ⦄) => do
      `(Triple $(← hintProgram c m) $P (fun $v => $Q) Lean.Order.bot)
macro_rules (kind := tripleEPost)
  | `(⦃ $P ⦄ $[(m := $m)]? $c ⦃ $Q; $E ⦄) => do `(Triple $(← hintProgram c m) $P $Q $E)
macro_rules (kind := tripleBinderEPost)
  | `(⦃ $P ⦄ $[(m := $m)]? $c ⦃ $v, $Q; $E ⦄) => do
      `(Triple $(← hintProgram c m) $P (fun $v => $Q) $E)

/-- Pretty-print `Triple` applications back as `⦃ … ⦄` notation. -/
@[app_unexpander Triple]
meta def unexpandTriple : Lean.PrettyPrinter.Unexpander
  | `($(_) $c $P $Q ⊥) => `(⦃ $P ⦄ $c ⦃ $Q ⦄)
  | `($(_) $c $P $Q Lean.Order.bot) => `(⦃ $P ⦄ $c ⦃ $Q ⦄)
  | `($(_) $c $P $Q $E) => `(⦃ $P ⦄ $c ⦃ $Q; $E ⦄)
  | _ => throw ()

namespace Triple

variable {Prog : Type v} {Value : Type u} [Assertion Pred] [Assertion EPred]
  [WP Prog Value Pred EPred]

theorem iff {x : Prog} {pre : Pred} {post : Value → Pred} {epost : EPred} :
    Triple x pre post epost ↔ (pre ⊑ wp x post epost) :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem iff_conseq {x : Prog} {pre : Pred} {post : Value → Pred} {epost : EPred} :
    Triple x pre post epost ↔
    (∀ pre' post', (pre' ⊑ pre) → (post ⊑ post') → pre' ⊑ wp x post' epost) := by
  constructor
  · intro ⟨h⟩ pre' post' hpre hpost
    exact PartialOrder.rel_trans hpre (PartialOrder.rel_trans h (WP.wp_consequence x _ _ epost hpost))
  · intro h
    exact ⟨h _ _ PartialOrder.rel_refl (fun _ => PartialOrder.rel_refl)⟩

theorem entails_wp_of_pre_post {x : Prog} {pre pre' : Pred} {post post' : Value → Pred} {epost : EPred}
    (h : Triple x pre' post' epost) (hpre : pre ⊑ pre') (hpost : post' ⊑ post) :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ hpre hpost

theorem entails_wp_of_pre {x : Prog} {pre pre' : Pred} {post : Value → Pred} {epost : EPred}
    (h : Triple x pre' post epost) (hpre : pre ⊑ pre') :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ hpre (fun _ => PartialOrder.rel_refl)

theorem entails_wp_of_post {x : Prog} {pre : Pred} {post post' : Value → Pred} {epost : EPred}
    (h : Triple x pre post' epost) (hpost : post' ⊑ post) :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ PartialOrder.rel_refl hpost

section Monad
variable [Monad m] [WPMonad m Pred EPred]

theorem pure (a : α) (h : pre ⊑ post a) :
    Triple (pure (f := m) a) pre post epost :=
  ⟨PartialOrder.rel_trans h (WPMonad.pure_le_wp_pure a post epost)⟩

theorem bind (x : m α) (f : α → m β)
    (mid : α → Pred)
    (hx : Triple x pre mid epost)
    (hf : ∀ a, Triple (f a) (mid a) post epost) :
    Triple (x >>= f) pre post epost :=
  ⟨PartialOrder.rel_trans hx.le_wp
    (PartialOrder.rel_trans
      (WP.wp_consequence x mid (fun a => wp (f a) post epost) epost (fun a => (hf a).le_wp))
      (WPMonad.bind_le_wp_bind x f post epost))⟩

theorem map [LawfulMonad m] (f : α → β) (x : m α)
    (h : Triple x pre (fun a => post (f a)) epost) :
    Triple (f <$> x) pre post epost :=
  ⟨PartialOrder.rel_trans h.le_wp (WPMonad.map_le_wp_map f x post epost)⟩

theorem seq [LawfulMonad m] (x : m (α → β)) (y : m α)
    (h : Triple x pre (fun f => wp y (fun a => post (f a)) epost) epost) :
    Triple (x <*> y) pre post epost :=
  ⟨PartialOrder.rel_trans h.le_wp (WPMonad.seq_le_wp_seq x y post epost)⟩

end Monad

end Triple

end Std.Internal.Do
