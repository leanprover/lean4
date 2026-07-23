/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Std.Tactic.Do
import Std.Internal.Do
import Std.Internal.Do.Triple.SpecLemmas

/-!
# `vcgen` on a non-monadic program type

This test exercises the `WP`/`WPMonad` split: it defines a small IMP language with (non-reentrant)
function calls whose weakest precondition is an *operational* semantics, gives it a `WP` instance
(without any `WPMonad` instance, since `Cmd` is not a monad), and uses `vcgen` to generate
verification conditions. The environment lives in the assertion (`Env → State → Prop`) so the
program stays a bare `Cmd` and `vcgen` discriminates on its constructors.

Functions are identified by name. A single unfolding lemma models "unfolding" of a call; each
concrete function gets a registered contract, proven once from its body and used by callers.
-/

open Std.Internal.Do
open Lean.Order

set_option mvcgen.warning false

/-! ## IMP syntax and state -/

abbrev Var := String
abbrev State := Var → Nat

@[grind] def State.update (s : State) (x : Var) (v : Nat) : State :=
  fun y => if y = x then v else s y

inductive Expr where
  | lit (n : Nat)
  | var (x : Var)
  | add (e₁ e₂ : Expr)
  | sub (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)
  | mod (e₁ e₂ : Expr)
  | le (e₁ e₂ : Expr)

@[simp, grind] def Expr.eval (s : State) : Expr → Nat
  | .lit n => n
  | .var x => s x
  | .add e₁ e₂ => e₁.eval s + e₂.eval s
  | .sub e₁ e₂ => e₁.eval s - e₂.eval s
  | .mul e₁ e₂ => e₁.eval s * e₂.eval s
  | .mod e₁ e₂ => e₁.eval s % e₂.eval s
  | .le e₁ e₂ => if e₁.eval s ≤ e₂.eval s then 1 else 0

abbrev FName := String

inductive Cmd where
  | skip
  | assign (x : Var) (e : Expr)
  | seq (c₁ c₂ : Cmd)
  | ite (cond : Expr) (c₁ c₂ : Cmd)
  | while (cond : Expr) (body : Cmd)
  | call (f : FName)

/-! ## Non-reentrant function environment

Functions are looked up by name; `lookup` returns the body together with the *prefix*
environment in which it was defined, so a function can call only earlier-defined ones. -/

inductive Env where
  | nil
  | snoc (Φ : Env) (name : FName) (body : Cmd)

@[grind] def Env.lookup : Env → FName → Option (Env × Cmd)
  | .nil, _ => none
  | .snoc Φ name body, f => if f = name then some (Φ, body) else Φ.lookup f

theorem Env.lookup_sizeOf_lt {Φ Φ' : Env} {body : Cmd} {f : FName}
    (h : Φ.lookup f = some (Φ', body)) : sizeOf Φ' < sizeOf Φ := by
  induction Φ with
  | nil => simp [Env.lookup] at h
  | snoc Ψ name b ih =>
    simp only [Env.lookup] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp only [Env.snoc.sizeOf_spec]; omega
    · have := ih h
      simp only [Env.snoc.sizeOf_spec]; omega

/-! ## Omni-style weakest precondition -/

def wpCmd (Φ : Env) : Cmd → (State → Prop) → State → Prop
  | .skip, Q, s => Q s
  | .assign x e, Q, s => Q (s.update x (e.eval s))
  | .seq c₁ c₂, Q, s => wpCmd Φ c₁ (fun s' => wpCmd Φ c₂ Q s') s
  | .ite cond c₁ c₂, Q, s =>
    if cond.eval s ≠ 0 then wpCmd Φ c₁ Q s else wpCmd Φ c₂ Q s
  | .while cond body, Q, s =>
    ∃ I : State → Prop,
      I s ∧
      (∀ s', I s' → cond.eval s' ≠ 0 → wpCmd Φ body I s') ∧
      (∀ s', I s' → cond.eval s' = 0 → Q s')
  | .call f, Q, s =>
    match _h : Φ.lookup f with
    | some (Φ', body) => wpCmd Φ' body Q s
    | none => False
  termination_by c => (sizeOf Φ, sizeOf c)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ (Env.lookup_sizeOf_lt _h)
      | (apply Prod.Lex.right
         simp only [Cmd.seq.sizeOf_spec, Cmd.ite.sizeOf_spec, Cmd.while.sizeOf_spec]; omega)

theorem wpCmd_mono {Φ : Env} {c : Cmd} {Q Q' : State → Prop} (hQ : ∀ s, Q s → Q' s) :
    ∀ s, wpCmd Φ c Q s → wpCmd Φ c Q' s := by
  match Φ, c with
  | Φ, .skip => intro s h; simp only [wpCmd] at h ⊢; exact hQ s h
  | Φ, .assign x e => intro s h; simp only [wpCmd] at h ⊢; exact hQ _ h
  | Φ, .seq c₁ c₂ =>
    intro s h
    simp only [wpCmd] at h ⊢
    exact wpCmd_mono (fun s' h' => wpCmd_mono hQ s' h') s h
  | Φ, .ite cond c₁ c₂ =>
    intro s h
    simp only [wpCmd] at h ⊢
    split
    · exact wpCmd_mono hQ s (by rwa [if_pos (by assumption)] at h)
    · exact wpCmd_mono hQ s (by rwa [if_neg (by assumption)] at h)
  | Φ, .while cond body =>
    intro s h
    simp only [wpCmd] at h ⊢
    obtain ⟨I, hI, hstep, hexit⟩ := h
    exact ⟨I, hI, hstep, fun s' hI' hc => hQ s' (hexit s' hI' hc)⟩
  | Φ, .call f =>
    intro s h
    simp only [wpCmd] at h ⊢
    split
    · next Φ' body heq => rw [heq] at h; exact wpCmd_mono hQ s h
    · next heq => rw [heq] at h; exact h.elim
  termination_by (sizeOf Φ, sizeOf c)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ (Env.lookup_sizeOf_lt (by assumption))
      | (apply Prod.Lex.right
         simp only [Cmd.seq.sizeOf_spec, Cmd.ite.sizeOf_spec]; omega)

/-! ## `WP` instance: the env lives in the assertion -/

abbrev Assn := Env → State → Prop

instance : WP Cmd Unit Assn EPost.Nil where
  wpTrans c := ⟨fun Q _epost Φ s => wpCmd Φ c (Q () Φ) s⟩
  wp_trans_monotone c := by
    intro Q Q' e e' _he hQ Φ s h
    exact wpCmd_mono (fun s' h' => hQ () Φ s' h') s h

variable {Q : Unit → Assn} {epost : EPost.Nil}

/-! ## `wp` equations, one per constructor

`wpCmd`'s defining equations transported to `wp` itself: each fires only on a concrete `Cmd`
constructor applied to a postcondition `Q`, and the recursive cases stay at the `wp` level (no
`wpCmd` leaks into goals). The `while` equation is intentionally not a `simp` lemma so loops stay
opaque for the `Spec.while`/`inv1` mechanism. -/

/-- `wp` of a `Cmd` is `wpCmd` at the assertion's environment. Not a `simp` lemma; it is the rfl
bridge behind the per-constructor equations below. -/
private theorem wp_apply (c : Cmd) :
    Std.Internal.Do.wp c Q epost = fun Φ s => wpCmd Φ c (Q () Φ) s := rfl

@[simp] theorem wp_skip_eq (Φ : Env) (s : State) :
    Std.Internal.Do.wp Cmd.skip Q epost Φ s = Q () Φ s := by
  simp only [wp_apply, wpCmd]

@[simp] theorem wp_assign_eq (x : Var) (e : Expr) (Φ : Env) (s : State) :
    Std.Internal.Do.wp (Cmd.assign x e) Q epost Φ s = Q () Φ (s.update x (e.eval s)) := by
  simp only [wp_apply, wpCmd]

@[simp] theorem wp_seq_eq (c₁ c₂ : Cmd) (Φ : Env) (s : State) :
    Std.Internal.Do.wp (Cmd.seq c₁ c₂) Q epost Φ s =
      Std.Internal.Do.wp c₁ (fun _ => Std.Internal.Do.wp c₂ Q epost) epost Φ s := by
  simp only [wp_apply, wpCmd]

@[simp] theorem wp_ite_eq (cond : Expr) (c₁ c₂ : Cmd) (Φ : Env) (s : State) :
    Std.Internal.Do.wp (Cmd.ite cond c₁ c₂) Q epost Φ s =
      if cond.eval s ≠ 0 then Std.Internal.Do.wp c₁ Q epost Φ s
      else Std.Internal.Do.wp c₂ Q epost Φ s := by
  simp only [wp_apply, wpCmd]

@[simp] theorem wp_call_eq (f : FName) (Φ : Env) (s : State) :
    Std.Internal.Do.wp (Cmd.call f) Q epost Φ s =
      (Φ.lookup f).elim False (fun p => Std.Internal.Do.wp p.2 (fun u _ => Q u Φ) epost p.1 s) := by
  show wpCmd Φ (Cmd.call f) (Q () Φ) s = _
  rw [wpCmd]; cases Φ.lookup f <;> rfl

theorem wp_while_eq (cond : Expr) (body : Cmd) (Φ : Env) (s : State) :
    Std.Internal.Do.wp (Cmd.while cond body) Q epost Φ s =
      ∃ I : State → Prop, I s ∧
        (∀ s', I s' → cond.eval s' ≠ 0 → Std.Internal.Do.wp body (fun _ _ => I) epost Φ s') ∧
        (∀ s', I s' → cond.eval s' = 0 → Q () Φ s') := by
  simp only [wp_apply, wpCmd]

/-- Build a triple from the pointwise `wp` equation of the program. -/
private theorem triple_of_wp {c : Cmd} {pre : Assn}
    (h : ∀ Φ s, Std.Internal.Do.wp c Q epost Φ s = pre Φ s) : Triple c pre Q epost :=
  Triple.iff.mpr (by rw [funext fun Φ => funext fun s => h Φ s]; exact PartialOrder.rel_refl)

/-! ## Specification lemmas, one per constructor -/

@[spec] theorem Spec.skip :
    Triple Cmd.skip (Q ()) Q epost := triple_of_wp wp_skip_eq

@[spec] theorem Spec.assign (x : Var) (e : Expr) :
    Triple (Cmd.assign x e) (fun Φ s => Q () Φ (s.update x (e.eval s))) Q epost :=
  triple_of_wp (wp_assign_eq x e)

@[spec] theorem Spec.seq (c₁ c₂ : Cmd) :
    Triple (Cmd.seq c₁ c₂)
      (Std.Internal.Do.wp c₁ (fun _ => Std.Internal.Do.wp c₂ Q epost) epost) Q epost :=
  triple_of_wp (wp_seq_eq c₁ c₂)

@[spec] theorem Spec.ite (cond : Expr) (c₁ c₂ : Cmd) :
    Triple (Cmd.ite cond c₁ c₂)
      (fun Φ s => if cond.eval s ≠ 0
        then Std.Internal.Do.wp c₁ Q epost Φ s else Std.Internal.Do.wp c₂ Q epost Φ s) Q epost :=
  triple_of_wp (wp_ite_eq cond c₁ c₂)

/-- Lift a body's contract through a call: if `f` resolves to `body` in prefix environment `Φ'`, a
triple for `body` (proven with `Φ` pinned to `Φ'`, so its own inner calls resolve) yields a triple
for `call f`. The call analogue of `Spec.while`: each concrete function's contract is one application
of this lemma over its body. -/
theorem Spec.call_of_body (f : FName) (Φ' : Env) (body : Cmd) {P' Q' : State → Prop}
    (hbody : Triple body (fun Φ s => Φ = Φ' ∧ P' s) (fun _ _ s => Q' s) epost) :
    Triple (Cmd.call f) (fun Φ s => Φ.lookup f = some (Φ', body) ∧ P' s) (fun _ _ s => Q' s) epost :=
  Triple.iff.mpr (by
    rintro Φ s ⟨hlk, hp⟩
    simp only [wp_call_eq, hlk, Option.elim]
    exact Triple.le_wp hbody Φ' s ⟨rfl, hp⟩)

/-- A `while` loop invariant: an IMP assertion `Env → State → Prop`. Marked `@[spec_invariant_type]`
so `vcgen` classifies it as an `inv1` case rather than an ordinary verification condition. -/
@[spec_invariant_type]
def WhileInvariant := Assn

/-- An invariant `I` proves a `while` triple: it holds on entry, is preserved by running the body
whenever the guard is nonzero, and implies the postcondition when the guard is zero. `vcgen`
instantiates `I` from the `inv1` case, recurses into `body` for the preservation `step`, and leaves
the exit condition as a VC. `I` is applied pointwise so the triple's assertion type stays `Assn`
rather than `WhileInvariant`. -/
@[spec] theorem Spec.while (cond : Expr) (body : Cmd) (I : WhileInvariant)
    (step : Triple body (fun Φ s => I Φ s ∧ cond.eval s ≠ 0) (fun _ Φ s => I Φ s) epost)
    (hexit : ∀ Φ s, I Φ s → cond.eval s = 0 → Q () Φ s) :
    Triple (Cmd.while cond body) (fun Φ s => I Φ s) Q epost :=
  Triple.iff.mpr (by
    intro Φ s hs
    simp only [wp_while_eq]
    exact ⟨I Φ, hs, fun s' h' hc => Triple.le_wp step Φ s' ⟨h', hc⟩,
      fun s' h' hc => hexit Φ s' h' hc⟩)

/-! ## Surface notation

A small concrete syntax elaborating to the `Expr`/`Cmd` AST, so example programs read like
imperative code rather than nested constructors. -/

declare_syntax_cat imp_expr
syntax num : imp_expr
syntax ident : imp_expr
syntax:50 imp_expr:50 " <= " imp_expr:51 : imp_expr
syntax:65 imp_expr:65 " + " imp_expr:66 : imp_expr
syntax:65 imp_expr:65 " - " imp_expr:66 : imp_expr
syntax:70 imp_expr:70 " * " imp_expr:71 : imp_expr
syntax:70 imp_expr:70 " % " imp_expr:71 : imp_expr
syntax "(" imp_expr ")" : imp_expr

declare_syntax_cat imp_cmd
syntax "skip" : imp_cmd
syntax ident " := " imp_expr : imp_cmd
syntax:2 imp_cmd:3 "; " imp_cmd:2 : imp_cmd
syntax "if " imp_expr " then " imp_cmd " else " imp_cmd " fi" : imp_cmd
syntax "while " imp_expr " do " imp_cmd " od" : imp_cmd
syntax "call " ident : imp_cmd
syntax "(" imp_cmd ")" : imp_cmd

/-- `⟪ e ⟫` elaborates an IMP expression to `Expr`. -/
syntax "⟪" imp_expr "⟫" : term
/-- `⟦ c ⟧` elaborates an IMP command to `Cmd`. -/
syntax "⟦" imp_cmd "⟧" : term

open Lean in
macro_rules
  | `(⟪ $n:num ⟫) => `(Expr.lit $n)
  | `(⟪ $x:ident ⟫) => `(Expr.var $(quote x.getId.toString))
  | `(⟪ $a <= $b ⟫) => `(Expr.le ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a + $b ⟫) => `(Expr.add ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a - $b ⟫) => `(Expr.sub ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a * $b ⟫) => `(Expr.mul ⟪$a⟫ ⟪$b⟫)
  | `(⟪ $a % $b ⟫) => `(Expr.mod ⟪$a⟫ ⟪$b⟫)
  | `(⟪ ($a) ⟫) => `(⟪$a⟫)

open Lean in
macro_rules
  | `(⟦ skip ⟧) => `(Cmd.skip)
  | `(⟦ $x:ident := $e ⟧) => `(Cmd.assign $(quote x.getId.toString) ⟪$e⟫)
  | `(⟦ $c₁ ; $c₂ ⟧) => `(Cmd.seq ⟦$c₁⟧ ⟦$c₂⟧)
  | `(⟦ if $b then $c₁ else $c₂ fi ⟧) => `(Cmd.ite ⟪$b⟫ ⟦$c₁⟧ ⟦$c₂⟧)
  | `(⟦ while $b do $c od ⟧) => `(Cmd.while ⟪$b⟫ ⟦$c⟧)
  | `(⟦ call $f:ident ⟧) => `(Cmd.call $(quote f.getId.toString))
  | `(⟦ ($c) ⟧) => `(⟦$c⟧)

/-! ## Straight-line, conditional, and loop -/

/-- Straight-line code: `vcgen` chains the `seq`/`assign` specs into one substitution. -/
example : ⦃ fun _ _ => True ⦄ ⟦ x := 5; y := x + x ⟧ ⦃ fun _ _ s => s "y" = 10 ⦄ := by
  vcgen
  simp [State.update]

/-- A conditional: `vcgen` applies `Spec.ite`, leaving the guarded weakest precondition as a VC. -/
example : ⦃ fun _ _ => True ⦄ ⟦ if x then y := 1 else y := 0 fi ⟧
    ⦃ fun _ _ s => s "y" = if s "x" ≠ 0 then 1 else 0 ⦄ := by
  vcgen
  simp only [wp_assign_eq, State.update, Expr.eval]; grind

/-- A loop preserved vacuously: the guard fails immediately. -/
example : ⦃ fun _ s => s "x" = 0 ⦄ ⟦ while x do x := x + 1 od ⟧ ⦃ fun _ _ s => s "x" = 0 ⦄ := by
  vcgen
  case inv1 => exact fun _ s => s "x" = 0
  all_goals simp_all [State.update]

/-! ## Euclid's gcd as a `while` loop -/

@[grind =] theorem gcd_step (a b : Nat) : Nat.gcd b (a % b) = Nat.gcd a b := by
  rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

def gcd : Cmd := ⟦
  while b do
    t := b;
    b := a % b;
    a := t
  od
⟧

/-- `gcd` leaves `Nat.gcd A B` in `a`. With `State.update`/`Expr.eval`/`gcd_step` available to `grind`,
`vcgen with finish` discharges the entry/preservation/exit verification conditions. -/
theorem gcd_correct (A B : Nat) :
    ⦃ fun _ s => s "a" = A ∧ s "b" = B ⦄ gcd ⦃ fun _ _ s => s "a" = Nat.gcd A B ⦄ := by
  unfold gcd
  vcgen invariants
  | inv1 => fun _ s => Nat.gcd (s "a") (s "b") = Nat.gcd A B
  with finish

/-! ## Integer square root as a `while` loop -/

def isqrt : Cmd := ⟦
  r := 0;
  while (r + 1) * (r + 1) <= n do
    r := r + 1
  od
⟧

/-- `isqrt` leaves `⌊√n⌋` in `r`: the invariant `r² ≤ n` is preserved while the guard holds, and the
negated guard at exit gives `n < (r+1)²`. -/
theorem isqrt_correct (N : Nat) :
    ⦃ fun _ s => s "n" = N ⦄ isqrt
      ⦃ fun _ _ s => s "r" * s "r" ≤ N ∧ N < (s "r" + 1) * (s "r" + 1) ⦄ := by
  unfold isqrt
  vcgen invariants
  | inv1 => fun _ s => s "r" * s "r" ≤ N ∧ s "n" = N
  with finish

/-! ## Compositional reasoning: `gcd` and `isqrt` as functions

`Δ` defines `gcd` and `isqrt` as named functions and a `main` routine. Each call contract is
`Spec.call_of_body` over the function's body theorem; callers are verified against the *contracts*,
not the bodies, with `with finish` discharging the `Δ` lookups. -/

def mainBody : Cmd := ⟦ call gcd ⟧

@[grind] def Δ : Env :=
  .snoc (.snoc (.snoc .nil "gcd" gcd) "isqrt" isqrt) "main" mainBody

/-- Contract for `call "gcd"`: `vcgen` applies the generic `Spec.call_of_body`, discharges the
body obligation with `gcd_correct`, and `with finish` settles the lookup. -/
@[spec] theorem Spec.gcd {A B : Nat} :
    ⦃ fun Φ s => Φ.lookup "gcd" = some (.nil, _root_.gcd) ∧ s "a" = A ∧ s "b" = B ⦄
      Cmd.call "gcd" ⦃ fun _ _ s => s "a" = Nat.gcd A B ⦄ :=
  Spec.call_of_body "gcd" .nil _root_.gcd <| Triple.iff.mpr (by
    rintro Φ s ⟨-, ha, hb⟩; exact Triple.le_wp (gcd_correct A B) Φ s ⟨ha, hb⟩)

/-- Contract for `call "isqrt"`, proven the same way from `isqrt_correct`. -/
@[spec] theorem Spec.isqrt {N : Nat} :
    ⦃ fun Φ s => Φ.lookup "isqrt" = some (.snoc .nil "gcd" _root_.gcd, _root_.isqrt) ∧ s "n" = N ⦄
      Cmd.call "isqrt"
      ⦃ fun _ _ s => s "r" * s "r" ≤ N ∧ N < (s "r" + 1) * (s "r" + 1) ⦄ :=
  Spec.call_of_body "isqrt" (.snoc .nil "gcd" _root_.gcd) _root_.isqrt <| Triple.iff.mpr (by
    rintro Φ s ⟨-, hn⟩; exact Triple.le_wp (isqrt_correct N) Φ s hn)

/-- Contract for `call "main"`: `main`'s body (`call gcd`) is verified against `Spec.gcd`, not the
gcd body. -/
@[spec] theorem Spec.main {A B : Nat} :
    ⦃ fun Φ s => Φ.lookup "main" = some (.snoc (.snoc .nil "gcd" _root_.gcd) "isqrt" _root_.isqrt,
        _root_.mainBody) ∧ s "a" = A ∧ s "b" = B ⦄
      Cmd.call "main" ⦃ fun _ _ s => s "a" = Nat.gcd A B ⦄ :=
  Spec.call_of_body "main" (.snoc (.snoc .nil "gcd" _root_.gcd) "isqrt" _root_.isqrt) _root_.mainBody <| by
    unfold mainBody; vcgen with finish

/-- The top-level property of `main` run in `Δ`, verified modularly through the contracts. -/
theorem main_correct (A B : Nat) :
    ⦃ fun Φ s => Φ = Δ ∧ s "a" = A ∧ s "b" = B ⦄ ⟦ call main ⟧
      ⦃ fun _ _ s => s "a" = Nat.gcd A B ⦄ := by
  vcgen with finish

/-- `isqrt` called directly in `Δ`, verified through `Spec.isqrt`. -/
theorem isqrt_call_correct (N : Nat) :
    ⦃ fun Φ s => Φ = Δ ∧ s "n" = N ⦄ ⟦ call isqrt ⟧
      ⦃ fun _ _ s => s "r" * s "r" ≤ N ∧ N < (s "r" + 1) * (s "r" + 1) ⦄ := by
  vcgen with finish
