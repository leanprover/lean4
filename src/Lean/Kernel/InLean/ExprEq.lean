/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Init

public import Lean.Expr
/- `withPtrEq`/`withPtrAddr` are public but not exposed (up to Lean v4.35.0);
`Expr.beq_eq_beqMemo` needs their bodies (`k ()`, `k 0`), as con-leche's
`ConLeche.Kernel.Expr` does. -/
import all Init.Util
/- The computed field `Expr.data`'s equations are not exposed by `Lean.Expr`;
`data_eraseK` (the key equality's data-word test) reads them. -/
import all Lean.Expr

/-!
# InLean: decidable equality of `Lean.Expr`, executed pointer-first

InLean is to be provable by a simulation onto con-leche's cached checker, so it
does not use core's opaque externs.
Core's `BEq Expr` is `Expr.eqv`, an `@[extern] opaque` (alpha-equivalence
in C++).  InLean's executed equality is con-leche's design
(`ConLeche.Kernel.Expr`, `Expr.beq`/`beqMemo`): **the specification
is decidable equality**, `Expr.beqI a b = decide (a = b)`, so `LawfulBEq`
holds by construction, and the executed function is the memoised,
pointer-first descent `Expr.beqMemo`, proved equal to it
(`beq_eq_beqMemo`) and substituted by `@[csimp]` — no `implemented_by`,
nothing `unsafe`; the runtime facts enter only through `Init.Util`'s
`withPtrEq`/`withPtrAddr`.

Decidable equality of `Lean.Expr` needs it for every component; core
provides it for `Name` only.  `Level`, `Literal` and `Expr` get a structural
decision executed pointer first (below; `Expr`'s runs the memoised descent);
the rest is derived here (`BinderInfo`, the ids, `SourceInfo`, `DataValue`,
`KVMap`); `Syntax` (an `mdata` payload can hold one) is a nested
inductive the deriving handler refuses, and gets a structural equality
with its two lemmas.

**The memo discipline** is con-leche's: only a pair whose two nodes are
both shared (`withIsExclusive`) is probed and recorded —
a pair with an exclusive side cannot be queried again within the
comparison.  The official kernel's `expr_eq_fn::check_cache` guards its
cache the same way.

The instance is `scoped` in `InLean`: every InLean module (all inside the
namespace) and every memo map's key type there compares expressions by
it; code outside keeps core's.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

deriving instance DecidableEq for LevelMVarId
deriving instance DecidableEq for FVarId
deriving instance DecidableEq for MVarId
deriving instance DecidableEq for BinderInfo

/-! ## Level and literal equality, pointer first at every level (twin of
`Level.decEq`/`decEqPtr`, `Literal.decEq`/`decEqPtr`)

Core's `BEq Level` is `Level.beq`, an `@[extern] opaque` (`lean_level_eq`,
`level.cpp`'s `operator==`: kind, hash, pointer, structure, at every node);
core's `BEq Literal` is derived (no pointer test; `lean_nat_dec_eq` on two big
numbers is `mpz_cmp`).  As con-leche's, the instance is the structural
decision and the executed function the pointer-first one, substituted by
`@[csimp]` on `Decidable`'s subsingleton property.  `Name` needs nothing:
core's `DecidableEq Name` is `Name.beq`, the C `lean_name_eq` (pointer, hash,
then the components, the pointer again at every prefix). -/

/-! Twins of `withPtrEqDecEq`: the pointer test, then `k`.  Written out (as
`ptrDec` below), since `withPtrEqDecEq`'s signature differs between Lean
v4.35.0 and later toolchains, and one per type, since later toolchains compile
`withPtrEq` only at a type they can see is free of types. -/

@[inline] def ptrDecNat (a b : Nat) (k : Unit → Decidable (a = b)) : Decidable (a = b) :=
  match h : withPtrEq a b (fun _ => toBoolUsing (k ())) (toBoolUsing_eq_true (k ())) with
  | true => isTrue (of_toBoolUsing_eq_true (d := k ()) (by simpa [withPtrEq] using h))
  | false => isFalse (of_toBoolUsing_eq_false (d := k ()) (by simpa [withPtrEq] using h))

@[inline] def ptrDecLiteral (a b : Literal) (k : Unit → Decidable (a = b)) : Decidable (a = b) :=
  match h : withPtrEq a b (fun _ => toBoolUsing (k ())) (toBoolUsing_eq_true (k ())) with
  | true => isTrue (of_toBoolUsing_eq_true (d := k ()) (by simpa [withPtrEq] using h))
  | false => isFalse (of_toBoolUsing_eq_false (d := k ()) (by simpa [withPtrEq] using h))

@[inline] def ptrDecLevel (a b : Level) (k : Unit → Decidable (a = b)) : Decidable (a = b) :=
  match h : withPtrEq a b (fun _ => toBoolUsing (k ())) (toBoolUsing_eq_true (k ())) with
  | true => isTrue (of_toBoolUsing_eq_true (d := k ()) (by simpa [withPtrEq] using h))
  | false => isFalse (of_toBoolUsing_eq_false (d := k ()) (by simpa [withPtrEq] using h))

/-- The specification of literal equality: the structural decision. -/
def Literal.decEqI : (a b : Literal) → Decidable (a = b)
  | .natVal n, .natVal m =>
    if h : n = m then isTrue (by rw [h]) else isFalse (fun e => h (Literal.natVal.inj e))
  | .strVal s, .strVal t =>
    if h : s = t then isTrue (by rw [h]) else isFalse (fun e => h (Literal.strVal.inj e))
  | .natVal _, .strVal _ | .strVal _, .natVal _ => isFalse (fun e => Literal.noConfusion e)

/-- Twin of `Literal.decEqPtr`: the `Literal` object, then the number's
object, then the value (`lean_string_eq` tests a string's pointer itself).  The
hash comes one level up: an `Expr.lit` pair is compared past the nodes' data
words, which hold the literal's hash. -/
@[inline] def Literal.decEqPtrI (a b : Literal) : Decidable (a = b) :=
  ptrDecLiteral a b fun _ =>
    match a, b with
    | .natVal n, .natVal m =>
      match ptrDecNat n m (fun _ => Nat.decEq n m) with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (fun e => h (Literal.natVal.inj e))
    | .strVal s, .strVal t =>
      if h : s = t then isTrue (by rw [h]) else isFalse (fun e => h (Literal.strVal.inj e))
    | .natVal _, .strVal _ | .strVal _, .natVal _ => isFalse (fun e => Literal.noConfusion e)

@[csimp] theorem Literal.decEqI_eq_decEqPtrI : @Literal.decEqI = @Literal.decEqPtrI := by
  funext a b; exact Subsingleton.elim _ _

/-- Every literal equality in InLean runs `Literal.decEqPtrI`. -/
instance instDecidableEqLiteralI : DecidableEq Literal := Literal.decEqI

/-- A level's cached data word (Lean's computed field: hash, depth, flags). -/
@[inline] def levelWord (l : Level) : UInt64 := l.data

/-- The specification of level equality: the structural decision. -/
def Level.decEqI : (a b : Level) → Decidable (a = b)
  | .zero, .zero => isTrue rfl
  | .succ u, .succ v =>
    match Level.decEqI u v with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => h (Level.succ.inj e))
  | .max u v, .max u' v' =>
    match Level.decEqI u u', Level.decEqI v v' with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (fun e => h (Level.max.inj e).1)
    | _, isFalse h' => isFalse (fun e => h' (Level.max.inj e).2)
  | .imax u v, .imax u' v' =>
    match Level.decEqI u u', Level.decEqI v v' with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (fun e => h (Level.imax.inj e).1)
    | _, isFalse h' => isFalse (fun e => h' (Level.imax.inj e).2)
  | .param n, .param m =>
    if h : n = m then isTrue (by rw [h]) else isFalse (fun e => h (Level.param.inj e))
  | .mvar n, .mvar m =>
    if h : n = m then isTrue (by rw [h]) else isFalse (fun e => h (Level.mvar.inj e))
  | .zero, .succ .. | .zero, .max .. | .zero, .imax .. | .zero, .param .. | .zero, .mvar ..
  | .succ .., .zero | .succ .., .max .. | .succ .., .imax .. | .succ .., .param ..
  | .succ .., .mvar ..
  | .max .., .zero | .max .., .succ .. | .max .., .imax .. | .max .., .param ..
  | .max .., .mvar ..
  | .imax .., .zero | .imax .., .succ .. | .imax .., .max .. | .imax .., .param ..
  | .imax .., .mvar ..
  | .param .., .zero | .param .., .succ .. | .param .., .max .. | .param .., .imax ..
  | .param .., .mvar ..
  | .mvar .., .zero | .mvar .., .succ .. | .mvar .., .max .. | .mvar .., .imax ..
  | .mvar .., .param .. =>
    isFalse (fun e => Level.noConfusion e)

/-- Twin of `Level.decEqPtr`: the pointer and the cached data word before the
structural step, at every node; the children start over with the pointer, the
parameter goes to core's `lean_name_eq`.  (con-leche compares the hash; Lean's
word also holds the depth and the flags, and is read without a shift.) -/
def Level.decEqPtrI (a b : Level) : Decidable (a = b) :=
  ptrDecLevel a b fun _ =>
    if hh : levelWord a = levelWord b then
      match a, b with
      | .zero, .zero => isTrue rfl
      | .succ u, .succ v =>
        match Level.decEqPtrI u v with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (fun e => h (Level.succ.inj e))
      | .max u v, .max u' v' =>
        match Level.decEqPtrI u u' with
        | isFalse h => isFalse (fun e => h (Level.max.inj e).1)
        | isTrue h =>
          match Level.decEqPtrI v v' with
          | isTrue h' => isTrue (by rw [h, h'])
          | isFalse h' => isFalse (fun e => h' (Level.max.inj e).2)
      | .imax u v, .imax u' v' =>
        match Level.decEqPtrI u u' with
        | isFalse h => isFalse (fun e => h (Level.imax.inj e).1)
        | isTrue h =>
          match Level.decEqPtrI v v' with
          | isTrue h' => isTrue (by rw [h, h'])
          | isFalse h' => isFalse (fun e => h' (Level.imax.inj e).2)
      | .param n, .param m =>
        if h : n = m then isTrue (by rw [h]) else isFalse (fun e => h (Level.param.inj e))
      | .mvar n, .mvar m =>
        if h : n = m then isTrue (by rw [h]) else isFalse (fun e => h (Level.mvar.inj e))
      | .zero, .succ .. | .zero, .max .. | .zero, .imax .. | .zero, .param .. | .zero, .mvar ..
      | .succ .., .zero | .succ .., .max .. | .succ .., .imax .. | .succ .., .param ..
      | .succ .., .mvar ..
      | .max .., .zero | .max .., .succ .. | .max .., .imax .. | .max .., .param ..
      | .max .., .mvar ..
      | .imax .., .zero | .imax .., .succ .. | .imax .., .max .. | .imax .., .param ..
      | .imax .., .mvar ..
      | .param .., .zero | .param .., .succ .. | .param .., .max .. | .param .., .imax ..
      | .param .., .mvar ..
      | .mvar .., .zero | .mvar .., .succ .. | .mvar .., .max .. | .mvar .., .imax ..
      | .mvar .., .param .. =>
        isFalse (fun e => Level.noConfusion e)
    else isFalse (fun e => hh (by rw [e]))

@[csimp] theorem Level.decEqI_eq_decEqPtrI : @Level.decEqI = @Level.decEqPtrI := by
  funext a b; exact Subsingleton.elim _ _

/-- Every level equality in InLean (`=` in an `if`, `beqGoX`'s `.sort` and
`.const` arms, `Level.beqI`) runs `Level.decEqPtrI`. -/
instance instDecidableEqLevelI : DecidableEq Level := Level.decEqI

deriving instance DecidableEq for Substring.Raw
deriving instance DecidableEq for SourceInfo
deriving instance DecidableEq for Syntax.Preresolved

mutual
/-- Structural equality of `Syntax` (the deriving handler refuses nested
inductives). -/
def synEq : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node i k ⟨as⟩, .node i' k' ⟨bs⟩ => decide (i = i') && decide (k = k') && synListEq as bs
  | .atom i v, .atom i' v' => decide (i = i') && decide (v = v')
  | .ident i r v p, .ident i' r' v' p' =>
    decide (i = i') && decide (r = r') && decide (v = v') && decide (p = p')
  | _, _ => false
def synListEq : List Syntax → List Syntax → Bool
  | [], [] => true
  | a :: as, b :: bs => synEq a b && synListEq as bs
  | _, _ => false
end

mutual
theorem synEq_sound : ∀ a b, synEq a b = true → a = b
  | .missing, .missing, _ => rfl
  | .node i k ⟨as⟩, .node i' k' ⟨bs⟩, h => by
    simp only [synEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [synListEq_sound as bs h]
  | .atom i v, .atom i' v', h => by
    simp only [synEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | .ident i r v p, .ident i' r' v' p', h => by
    simp only [synEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl
  | .missing, .node .., h | .missing, .atom .., h | .missing, .ident .., h
  | .node .., .missing, h | .node .., .atom .., h | .node .., .ident .., h
  | .atom .., .missing, h | .atom .., .node .., h | .atom .., .ident .., h
  | .ident .., .missing, h | .ident .., .node .., h | .ident .., .atom .., h => by simp [synEq] at h
theorem synListEq_sound : ∀ as bs, synListEq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [synListEq, Bool.and_eq_true] at h
    rw [synEq_sound a b h.1, synListEq_sound as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [synListEq] at h
end

mutual
theorem synEq_refl : ∀ a, synEq a a = true
  | .missing => rfl
  | .node _ _ ⟨as⟩ => by simp [synEq, synListEq_refl as]
  | .atom _ _ => by simp [synEq]
  | .ident _ _ _ _ => by simp [synEq]
theorem synListEq_refl : ∀ as, synListEq as as = true
  | [] => rfl
  | a :: as => by simp [synListEq, synEq_refl a, synListEq_refl as]
end

instance instDecidableEqSyntaxI : DecidableEq Syntax := fun a b =>
  if h : synEq a b then isTrue (synEq_sound a b h)
  else isFalse (fun e => by subst e; exact h (synEq_refl a))

deriving instance DecidableEq for DataValue
deriving instance DecidableEq for KVMap
/-- Twin of `Expr.decEq`: **the specification of expression equality**,
the structural decision (the instance below).  No derived `DecidableEq`:
compiled code runs `Expr.decEqPtrI` in its place (`Expr.decEqI_eq_decEqPtrI`),
and the only compiled references to this body are `ptrDecStruct`'s
pure-model fallback, which compiled code never reaches, and its own
recursion. -/
def Expr.decEqI : (a b : Expr) → Decidable (a = b)
  | .bvar x0, .bvar y0 =>
    if h0 : x0 = y0 then isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .fvar x0, .fvar y0 =>
    if h0 : x0 = y0 then isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .mvar x0, .mvar y0 =>
    if h0 : x0 = y0 then isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .sort x0, .sort y0 =>
    if h0 : x0 = y0 then isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .const x0 x1, .const y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then isTrue (by subst h0; subst h1; rfl)
      else isFalse (fun e => h1 (by injection e <;> assumption))
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .app x0 x1, .app y0 y1 =>
    match Expr.decEqI x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match Expr.decEqI x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 => isTrue (by subst h0; subst h1; rfl)
  | .lam x0 x1 x2 x3, .lam y0 y1 y2 y3 =>
    if h0 : x0 = y0 ∧ x3 = y3 then
      match Expr.decEqI x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        match Expr.decEqI x2 y2 with
        | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
        | isTrue h2 => isTrue (by obtain ⟨rfl, rfl⟩ := h0; subst h1; subst h2; rfl)
    else isFalse (fun e => h0 ⟨(Expr.lam.inj e).1, (Expr.lam.inj e).2.2.2⟩)
  | .forallE x0 x1 x2 x3, .forallE y0 y1 y2 y3 =>
    if h0 : x0 = y0 ∧ x3 = y3 then
      match Expr.decEqI x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        match Expr.decEqI x2 y2 with
        | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
        | isTrue h2 => isTrue (by obtain ⟨rfl, rfl⟩ := h0; subst h1; subst h2; rfl)
    else isFalse (fun e => h0 ⟨(Expr.forallE.inj e).1, (Expr.forallE.inj e).2.2.2⟩)
  | .letE x0 x1 x2 x3 x4, .letE y0 y1 y2 y3 y4 =>
    if h0 : x0 = y0 ∧ x4 = y4 then
      match Expr.decEqI x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        match Expr.decEqI x2 y2 with
        | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
        | isTrue h2 =>
          match Expr.decEqI x3 y3 with
          | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
          | isTrue h3 => isTrue (by obtain ⟨rfl, rfl⟩ := h0; subst h1; subst h2; subst h3; rfl)
    else isFalse (fun e => h0 ⟨(Expr.letE.inj e).1, (Expr.letE.inj e).2.2.2.2⟩)
  | .lit x0, .lit y0 =>
    if h0 : x0 = y0 then isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .mdata x0 x1, .mdata y0 y1 =>
    if h0 : x0 = y0 then
      match Expr.decEqI x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 => isTrue (by subst h0; subst h1; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .proj x0 x1 x2, .proj y0 y1 y2 =>
    if h0 : x0 = y0 ∧ x1 = y1 then
      match Expr.decEqI x2 y2 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h2 => isTrue (by obtain ⟨rfl, rfl⟩ := h0; subst h2; rfl)
    else isFalse (fun e => h0 ⟨(Expr.proj.inj e).1, (Expr.proj.inj e).2.1⟩)
  | .bvar .., .fvar .. | .bvar .., .mvar .. | .bvar .., .sort ..
  | .bvar .., .const .. | .bvar .., .app .. | .bvar .., .lam ..
  | .bvar .., .forallE .. | .bvar .., .letE .. | .bvar .., .lit ..
  | .bvar .., .mdata .. | .bvar .., .proj .. | .fvar .., .bvar ..
  | .fvar .., .mvar .. | .fvar .., .sort .. | .fvar .., .const ..
  | .fvar .., .app .. | .fvar .., .lam .. | .fvar .., .forallE ..
  | .fvar .., .letE .. | .fvar .., .lit .. | .fvar .., .mdata ..
  | .fvar .., .proj .. | .mvar .., .bvar .. | .mvar .., .fvar ..
  | .mvar .., .sort .. | .mvar .., .const .. | .mvar .., .app ..
  | .mvar .., .lam .. | .mvar .., .forallE .. | .mvar .., .letE ..
  | .mvar .., .lit .. | .mvar .., .mdata .. | .mvar .., .proj ..
  | .sort .., .bvar .. | .sort .., .fvar .. | .sort .., .mvar ..
  | .sort .., .const .. | .sort .., .app .. | .sort .., .lam ..
  | .sort .., .forallE .. | .sort .., .letE .. | .sort .., .lit ..
  | .sort .., .mdata .. | .sort .., .proj .. | .const .., .bvar ..
  | .const .., .fvar .. | .const .., .mvar .. | .const .., .sort ..
  | .const .., .app .. | .const .., .lam .. | .const .., .forallE ..
  | .const .., .letE .. | .const .., .lit .. | .const .., .mdata ..
  | .const .., .proj .. | .app .., .bvar .. | .app .., .fvar ..
  | .app .., .mvar .. | .app .., .sort .. | .app .., .const ..
  | .app .., .lam .. | .app .., .forallE .. | .app .., .letE ..
  | .app .., .lit .. | .app .., .mdata .. | .app .., .proj ..
  | .lam .., .bvar .. | .lam .., .fvar .. | .lam .., .mvar ..
  | .lam .., .sort .. | .lam .., .const .. | .lam .., .app ..
  | .lam .., .forallE .. | .lam .., .letE .. | .lam .., .lit ..
  | .lam .., .mdata .. | .lam .., .proj .. | .forallE .., .bvar ..
  | .forallE .., .fvar .. | .forallE .., .mvar .. | .forallE .., .sort ..
  | .forallE .., .const .. | .forallE .., .app .. | .forallE .., .lam ..
  | .forallE .., .letE .. | .forallE .., .lit .. | .forallE .., .mdata ..
  | .forallE .., .proj .. | .letE .., .bvar .. | .letE .., .fvar ..
  | .letE .., .mvar .. | .letE .., .sort .. | .letE .., .const ..
  | .letE .., .app .. | .letE .., .lam .. | .letE .., .forallE ..
  | .letE .., .lit .. | .letE .., .mdata .. | .letE .., .proj ..
  | .lit .., .bvar .. | .lit .., .fvar .. | .lit .., .mvar ..
  | .lit .., .sort .. | .lit .., .const .. | .lit .., .app ..
  | .lit .., .lam .. | .lit .., .forallE .. | .lit .., .letE ..
  | .lit .., .mdata .. | .lit .., .proj .. | .mdata .., .bvar ..
  | .mdata .., .fvar .. | .mdata .., .mvar .. | .mdata .., .sort ..
  | .mdata .., .const .. | .mdata .., .app .. | .mdata .., .lam ..
  | .mdata .., .forallE .. | .mdata .., .letE .. | .mdata .., .lit ..
  | .mdata .., .proj .. | .proj .., .bvar .. | .proj .., .fvar ..
  | .proj .., .mvar .. | .proj .., .sort .. | .proj .., .const ..
  | .proj .., .app .. | .proj .., .lam .. | .proj .., .forallE ..
  | .proj .., .letE .. | .proj .., .lit .. | .proj .., .mdata .. =>
    isFalse (fun e => Expr.noConfusion e)

/-! ## The memoised pointer-first descent (twin of `Expr.beqMemo`) -/

/-- The nodes whose comparison recurses (twin of `beqRecursive`). -/
@[inline] def beqRecursive : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. | .mdata .. => true
  | _ => false

/-- The cached data word, as the `UInt64` it is. -/
@[inline] def dataWord (e : Expr) : UInt64 := e.data

/-- The cached data words differ (Lean's computed field: hash, depth, flags,
range): then the terms do. -/
@[inline] def dataNe (a b : Expr) : Bool := dataWord a != dataWord b

theorem dataNe_self (a : Expr) : dataNe a a = false := by simp [dataNe]

/-- A memo entry: a pair a completed descent proved equal, the addresses
it was seen at, the proof (twin of `EqPair`). -/
structure EqPair where
  fst : Expr
  snd : Expr
  pa : USize
  pb : USize
  eq : fst = snd

def EqPair.dflt : EqPair := ⟨.bvar 0, .bvar 0, 0, 0, rfl⟩

abbrev BeqMap := Std.HashMap Nat EqPair

/-- Twin of `beqKey`. -/
@[inline] def beqKey (pa pb : USize) : Nat :=
  ((pa ^^^ (pb * 0x9E3779B97F4A7C15)) &&& 0x3FFFFFFFFFFFFFFF).toNat

/-- `withIsExclusive` into a subsingleton: the obligation is
`Subsingleton.elim`. -/
@[inline] def withExcl {α : Type u} {β : Type v} [Subsingleton β] (a : @& α)
    (k : Bool → β) : β :=
  withIsExclusive a k (Subsingleton.elim _ _)

/-- Twin of `withAddr`. -/
@[inline] def withAddr {α : Type u} {β : Type v} [Subsingleton β] (a : α) (k : USize → β) : β :=
  withPtrAddr a k (fun _ _ => Subsingleton.elim _ _)

/-- Twin of `ptrDecStruct`: the pointer test, then the structural decision
(`Expr.decEqI`), inside the equality itself, which reaches it on equal
addresses only.  Written
out instead of by `withPtrEqDecEq`, whose signature differs between Lean
v4.35.0 and later toolchains. -/
@[inline] def ptrDecStruct (a b : Expr) : Decidable (a = b) :=
  let k : Decidable (a = b) := Expr.decEqI a b
  match h : withPtrEq a b (fun _ => toBoolUsing k) (toBoolUsing_eq_true k) with
  | true => isTrue (of_toBoolUsing_eq_true (d := k) (by simpa [withPtrEq] using h))
  | false => isFalse (of_toBoolUsing_eq_false (d := k) (by simpa [withPtrEq] using h))

/-- Twin of `probeHit`: not inlined, everything borrowed (the structural
fallback inside `ptrDecStruct` takes its terms owned, and a term that is an
owned argument in `beqGoX` would make the descent's own parameters owned;
see `BeqSt.recordEq`). -/
@[noinline] def probeHit (m : @& BeqMap) (key : Nat) (pa pb : USize) (a b : @& Expr) :
    { h : Bool // h = true → a = b } :=
  let p := m.getD key EqPair.dflt
  if p.pa == pa && p.pb == pb then
    match ptrDecStruct p.fst a, ptrDecStruct p.snd b with
    | isTrue h1, isTrue h2 => ⟨true, fun _ => h1 ▸ h2 ▸ p.eq⟩
    | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
  else ⟨false, fun h => Bool.noConfusion h⟩

/-- Twin of `BeqSt`: the state the descent threads, verdict and memo in one
word — `fail` once a pair proved unequal (the comparison is then aborted),
`empty` before the first recorded pair, `table m` after it.  A node's
comparison allocates nothing but the memo's own growth, as official's
`expr_eq_fn::apply` returns a `bool` beside a member cache. -/
inductive BeqSt where
  | fail
  | empty
  | table (m : BeqMap)

/-- Twin of `BeqSt.ok`. -/
@[inline] def BeqSt.ok : BeqSt → Bool
  | .fail => false
  | _ => true

/-- Twin of `BeqSt.record`: the entry under its key, in the table or in a
fresh one. -/
@[inline] def BeqSt.record (st : BeqSt) (key : Nat) (p : EqPair) : BeqSt :=
  match st with
  | .table m => .table (m.insert key p)
  | _ => .table (({} : BeqMap).insert key p)

theorem BeqSt.record_ok (st : BeqSt) (key : Nat) (p : EqPair) :
    (st.record key p).ok = true := by
  cases st <;> rfl

/-- Twin of `BeqSt.recordEq`: the write-back of a proved-equal pair, the
entry built here from borrowed terms; not inlined, so that no term is an
owned constructor argument in `beqGoX`. -/
@[noinline] def BeqSt.recordEq (st : BeqSt) (a b : @& Expr) (pa pb : USize) (h : a = b) :
    BeqSt :=
  st.record (beqKey pa pb) ⟨a, b, pa, pb, h⟩

/-- Twin of `BeqOk`: a state the descent may enter a node with. -/
abbrev BeqOk := { s : BeqSt // s.ok = true }

/-- Twin of `BeqOutX`: the state, with the proof that it is not `fail`
exactly when the pair is equal, behind a quotient (erased: at runtime the
`BeqSt` itself). -/
abbrev BeqOutX (a b : Expr) := Squash { s : BeqSt // s.ok = true ↔ a = b }

@[inline] def BeqOutX.yes {a b : Expr} (st : BeqOk) (h : a = b) : BeqOutX a b :=
  Quot.mk _ ⟨st.1, fun _ => h, fun _ => st.2⟩

@[inline] def BeqOutX.no {a b : Expr} (h : ¬ a = b) : BeqOutX a b :=
  Quot.mk _ ⟨.fail, fun e => Bool.noConfusion e, fun e => absurd e h⟩

@[inline] def BeqOutX.mk {a b : Expr} (d : Decidable (a = b)) (st : BeqOk) : BeqOutX a b :=
  match d with
  | isTrue h => .yes st h
  | isFalse h => .no h

@[inline] def BeqOutX.cast {a b c d : Expr} (r : BeqOutX a b) (e : (a = b) ↔ (c = d)) :
    BeqOutX c d :=
  Squash.lift r fun r => Quot.mk _ ⟨r.1, r.2.trans e⟩

/-- Twin of `beqIsApp`: the spine test of `beqGoX`. -/
@[inline] def beqIsApp : Expr → Bool
  | .app .. => true
  | _ => false

/-- Twin of `enterBeq`: pointer identity, the cached data word, the leaf
test, then the exclusivity of each side — an exclusive side means the pair
cannot recur and the descent runs with the memo untouched; a shared/shared
pair is probed, and recorded on a completed `true`. -/
@[inline] def enterBeq (st : BeqOk) (a b : @& Expr) (rec : BeqOk → BeqOutX a b) :
    BeqOutX a b :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then .mk (ptrDecStruct a b) st
  else if h : dataNe a b then
    .no (fun e => by subst e; simp [dataNe_self] at h)
  else if !beqRecursive a then rec st
  else withExcl a fun ea =>
    if ea then rec st
    else withExcl b fun eb =>
    if eb then rec st
    else
    let hit : { h : Bool // h = true → a = b } :=
      match st.1 with
      | .table m => probeHit m (beqKey pa pb) pa pb a b
      | _ => ⟨false, fun h => Bool.noConfusion h⟩
    if hh : hit.1 then .yes st (hit.2 hh)
    else Squash.lift (rec st) fun r =>
      if h : r.1.ok then
        .yes ⟨r.1.recordEq a b pa pb (r.2.mp h), BeqSt.record_ok ..⟩ (r.2.mp h)
      else Quot.mk _ r

/-- Twin of `beqGoX` over `Lean.Expr` (official `expr_eq_fn::apply`): the
constructor cases, each child through `enterBeq`; leaves decided by their
components' equality.  An application compares its last argument first and
then walks down the spine: where both functions are applications again the
descent continues on them directly (a partial application is neither
probed, recorded nor word-tested), and the heads go through the child
step.  A `false` aborts the comparison at every level (`fail`). -/
def beqGoX (st : BeqOk) (a b : @& Expr) : BeqOutX a b :=
  match a, b with
  | .bvar i, .bvar j =>
    .mk (if h : i = j then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.bvar.inj e))) st
  | .fvar i, .fvar j =>
    .mk (if h : i = j then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.fvar.inj e))) st
  | .mvar i, .mvar j =>
    .mk (if h : i = j then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.mvar.inj e))) st
  | .sort u, .sort v =>
    .mk (if h : u = v then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.sort.inj e))) st
  | .const n us, .const m vs =>
    .mk (if h : n = m ∧ us = vs then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
         else isFalse (fun e => h ⟨(Expr.const.inj e).1, (Expr.const.inj e).2⟩)) st
  | .lit l, .lit l' =>
    .mk (if h : l = l' then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.lit.inj e))) st
  | .app f x, .app g y =>
    Squash.lift (enterBeq st x y fun s => beqGoX s x y) fun r₁ =>
      if h₁ : r₁.1.ok then
        have hx : x = y := r₁.2.mp h₁
        let rf : BeqOutX f g :=
          if hf : beqIsApp f then
            if hg : beqIsApp g then beqGoX ⟨r₁.1, h₁⟩ f g
            else .no (fun e => by subst e; exact hg hf)
          else enterBeq ⟨r₁.1, h₁⟩ f g fun s => beqGoX s f g
        rf.cast ⟨fun h' => by subst hx; subst h'; rfl, fun e => (Expr.app.inj e).1⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.app.inj e).2))
  | .lam n t b bi, .lam n' t' b' bi' =>
    if hn : n = n' ∧ bi = bi' then
      Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
        if h₁ : r₁.1.ok then
          have ht : t = t' := r₁.2.mp h₁
          (enterBeq ⟨r₁.1, h₁⟩ b b' fun s => beqGoX s b b').cast
            ⟨fun h' => by obtain ⟨rfl, rfl⟩ := hn; subst ht; subst h'; rfl,
             fun e => (Expr.lam.inj e).2.2.1⟩
        else .no (fun e => h₁ (r₁.2.mpr (Expr.lam.inj e).2.1))
    else .no (fun e => hn ⟨(Expr.lam.inj e).1, (Expr.lam.inj e).2.2.2⟩)
  | .forallE n t b bi, .forallE n' t' b' bi' =>
    if hn : n = n' ∧ bi = bi' then
      Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
        if h₁ : r₁.1.ok then
          have ht : t = t' := r₁.2.mp h₁
          (enterBeq ⟨r₁.1, h₁⟩ b b' fun s => beqGoX s b b').cast
            ⟨fun h' => by obtain ⟨rfl, rfl⟩ := hn; subst ht; subst h'; rfl,
             fun e => (Expr.forallE.inj e).2.2.1⟩
        else .no (fun e => h₁ (r₁.2.mpr (Expr.forallE.inj e).2.1))
    else .no (fun e => hn ⟨(Expr.forallE.inj e).1, (Expr.forallE.inj e).2.2.2⟩)
  | .letE n t v b nd, .letE n' t' v' b' nd' =>
    if hn : n = n' ∧ nd = nd' then
      Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
        if h₁ : r₁.1.ok then
          have ht : t = t' := r₁.2.mp h₁
          Squash.lift (enterBeq ⟨r₁.1, h₁⟩ v v' fun s => beqGoX s v v') fun r₂ =>
            if h₂ : r₂.1.ok then
              have hv : v = v' := r₂.2.mp h₂
              (enterBeq ⟨r₂.1, h₂⟩ b b' fun s => beqGoX s b b').cast
                ⟨fun h' => by obtain ⟨rfl, rfl⟩ := hn; subst ht; subst hv; subst h'; rfl,
                 fun e => (Expr.letE.inj e).2.2.2.1⟩
            else .no (fun e => h₂ (r₂.2.mpr (Expr.letE.inj e).2.2.1))
        else .no (fun e => h₁ (r₁.2.mpr (Expr.letE.inj e).2.1))
    else .no (fun e => hn ⟨(Expr.letE.inj e).1, (Expr.letE.inj e).2.2.2.2⟩)
  | .proj s i x, .proj s' i' x' =>
    if hs : s = s' ∧ i = i' then
      (enterBeq st x x' fun r => beqGoX r x x').cast
        ⟨fun h => by obtain ⟨rfl, rfl⟩ := hs; subst h; rfl, fun e => (Expr.proj.inj e).2.2⟩
    else .no (fun e => hs ⟨(Expr.proj.inj e).1, (Expr.proj.inj e).2.1⟩)
  | .mdata d x, .mdata d' x' =>
    if hd : d = d' then
      (enterBeq st x x' fun r => beqGoX r x x').cast
        ⟨fun h => by subst hd; subst h; rfl, fun e => (Expr.mdata.inj e).2⟩
    else .no (fun e => hd (Expr.mdata.inj e).1)
  | .bvar .., .fvar .. | .bvar .., .mvar .. | .bvar .., .sort ..
  | .bvar .., .const .. | .bvar .., .app .. | .bvar .., .lam ..
  | .bvar .., .forallE .. | .bvar .., .letE .. | .bvar .., .lit ..
  | .bvar .., .mdata .. | .bvar .., .proj .. | .fvar .., .bvar ..
  | .fvar .., .mvar .. | .fvar .., .sort .. | .fvar .., .const ..
  | .fvar .., .app .. | .fvar .., .lam .. | .fvar .., .forallE ..
  | .fvar .., .letE .. | .fvar .., .lit .. | .fvar .., .mdata ..
  | .fvar .., .proj .. | .mvar .., .bvar .. | .mvar .., .fvar ..
  | .mvar .., .sort .. | .mvar .., .const .. | .mvar .., .app ..
  | .mvar .., .lam .. | .mvar .., .forallE .. | .mvar .., .letE ..
  | .mvar .., .lit .. | .mvar .., .mdata .. | .mvar .., .proj ..
  | .sort .., .bvar .. | .sort .., .fvar .. | .sort .., .mvar ..
  | .sort .., .const .. | .sort .., .app .. | .sort .., .lam ..
  | .sort .., .forallE .. | .sort .., .letE .. | .sort .., .lit ..
  | .sort .., .mdata .. | .sort .., .proj .. | .const .., .bvar ..
  | .const .., .fvar .. | .const .., .mvar .. | .const .., .sort ..
  | .const .., .app .. | .const .., .lam .. | .const .., .forallE ..
  | .const .., .letE .. | .const .., .lit .. | .const .., .mdata ..
  | .const .., .proj .. | .app .., .bvar .. | .app .., .fvar ..
  | .app .., .mvar .. | .app .., .sort .. | .app .., .const ..
  | .app .., .lam .. | .app .., .forallE .. | .app .., .letE ..
  | .app .., .lit .. | .app .., .mdata .. | .app .., .proj ..
  | .lam .., .bvar .. | .lam .., .fvar .. | .lam .., .mvar ..
  | .lam .., .sort .. | .lam .., .const .. | .lam .., .app ..
  | .lam .., .forallE .. | .lam .., .letE .. | .lam .., .lit ..
  | .lam .., .mdata .. | .lam .., .proj .. | .forallE .., .bvar ..
  | .forallE .., .fvar .. | .forallE .., .mvar .. | .forallE .., .sort ..
  | .forallE .., .const .. | .forallE .., .app .. | .forallE .., .lam ..
  | .forallE .., .letE .. | .forallE .., .lit .. | .forallE .., .mdata ..
  | .forallE .., .proj .. | .letE .., .bvar .. | .letE .., .fvar ..
  | .letE .., .mvar .. | .letE .., .sort .. | .letE .., .const ..
  | .letE .., .app .. | .letE .., .lam .. | .letE .., .forallE ..
  | .letE .., .lit .. | .letE .., .mdata .. | .letE .., .proj ..
  | .lit .., .bvar .. | .lit .., .fvar .. | .lit .., .mvar ..
  | .lit .., .sort .. | .lit .., .const .. | .lit .., .app ..
  | .lit .., .lam .. | .lit .., .forallE .. | .lit .., .letE ..
  | .lit .., .mdata .. | .lit .., .proj .. | .mdata .., .bvar ..
  | .mdata .., .fvar .. | .mdata .., .mvar .. | .mdata .., .sort ..
  | .mdata .., .const .. | .mdata .., .app .. | .mdata .., .lam ..
  | .mdata .., .forallE .. | .mdata .., .letE .. | .mdata .., .lit ..
  | .mdata .., .proj .. | .proj .., .bvar .. | .proj .., .fvar ..
  | .proj .., .mvar .. | .proj .., .sort .. | .proj .., .const ..
  | .proj .., .app .. | .proj .., .lam .. | .proj .., .forallE ..
  | .proj .., .letE .. | .proj .., .lit .. | .proj .., .mdata .. =>
    .no (fun e => Expr.noConfusion e)

/-- Twin of `Expr.beqMemo`: the pointer test, the cached data word, then the
memoised descent. -/
def Expr.beqMemo (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => if !dataNe a b then
      @decide (a = b) (Squash.lift (beqGoX ⟨.empty, rfl⟩ a b) (fun r => decidable_of_iff _ r.2))
    else false)
    (fun h => by subst h; simp [dataNe_self])

/-- Twin of `Expr.beqMemo_iff`: the executed equality decides `a = b`. -/
theorem Expr.beqMemo_iff (a b : Expr) : Expr.beqMemo a b = true ↔ a = b := by
  unfold Expr.beqMemo withPtrEq
  by_cases h : a = b
  · subst h; simp [dataNe_self]
  · simp [h]

/-- Twin of `Expr.decEqPtr`: expression equality as it runs, the decision
read off the pointer-first, memoised `Expr.beqMemo`, as `Level.decEqPtrI` and
`Literal.decEqPtrI` are for theirs. -/
@[inline] def Expr.decEqPtrI (a b : Expr) : Decidable (a = b) :=
  decidable_of_iff (Expr.beqMemo a b = true) (Expr.beqMemo_iff a b)

/-- Twin of `Expr.decEq_eq_decEqPtr`: `@[csimp]` on `Decidable`'s
subsingleton property. -/
@[csimp] theorem Expr.decEqI_eq_decEqPtrI : @Expr.decEqI = @Expr.decEqPtrI := by
  funext a b; exact Subsingleton.elim _ _

/-- Every expression equality (`=` in an `if`, a derived instance of a type
with an `Expr` field) runs `Expr.decEqPtrI`: the instance is declared after
the `@[csimp]` lemma, so its compiled body is the substituted one. -/
instance instDecidableEqExprI : DecidableEq Expr := Expr.decEqI

/-- Twin of `ptrDec`: the pointer test, then the instance; for the memo
tables' hit validation (`Lean.Kernel.InLean.ExprOps`), where a fallback compiled code
would run is `Expr.decEqPtrI`, never the structural walk.  Written out as
`ptrDecStruct` is. -/
@[inline] def ptrDec (a b : Expr) : Decidable (a = b) :=
  let k : Decidable (a = b) := (inferInstance : DecidableEq Expr) a b
  match h : withPtrEq a b (fun _ => toBoolUsing k) (toBoolUsing_eq_true k) with
  | true => isTrue (of_toBoolUsing_eq_true (d := k) (by simpa [withPtrEq] using h))
  | false => isFalse (of_toBoolUsing_eq_false (d := k) (by simpa [withPtrEq] using h))

/-- **InLean's executed expression equality**: decidable equality,
substituted by the memoised descent. -/
def Expr.beqI (a b : Expr) : Bool := decide (a = b)

/-- Twin of `Expr.beq_eq_beqMemo`. -/
@[csimp] theorem Expr.beqI_eq_beqMemo : @Expr.beqI = @Expr.beqMemo := by
  funext a b
  unfold Expr.beqI Expr.beqMemo withPtrEq
  split
  · congr 1
  · rename_i h
    exact decide_eq_false (fun e => by subst e; simp [dataNe_self] at h)

/-- **Exact equality** as an instance, for the walks' memos and the
generator (`Lean.Kernel.InLean.ExprOps`, `Lean.Kernel.InLean.IndGen`), whose results
keep binder names. -/
@[reducible] def instBEqExprExact : BEq Expr := ⟨Expr.beqI⟩

theorem instBEqExprExact_lawful : @LawfulBEq Expr instBEqExprExact := by
  letI := instBEqExprExact
  exact { eq_of_beq := fun h => of_decide_eq_true h, rfl := by simp [BEq.beq, Expr.beqI] }

/-! ## Equality up to what con-leche's terms do not have

con-leche's expressions carry no binder names, no binder infos, no `let`'s
`nonDep` flag and no `mdata`; its checker compares them by decidable
equality.  InLean has two equalities:

* **`Expr.clEq`, the checker's comparison** (the scoped `==`): equal after
  erasing all four (`erase`), each pair of nodes it meets first tested on
  the part of the cached data word `mdata` keeps (flags and loose-variable
  range).  It answers `true` only on `erase`-equal terms; on terms C can
  build, `erase`-equal terms have those parts equal, so two of its terms
  compare equal exactly when the con-leche terms they stand for do.
* **`Expr.keyEq`, the memo maps' key equality** (`EKey`): equal after
  erasing binder names and infos but neither `nonDep` nor `mdata`
  (`eraseK`).  Lean's cached hash reads no binder name or info, so the maps
  are lawful; it reads `nonDep` after Lean v4.35.0, so `eraseK` keeps it.
  Two keys that differ only in `nonDep` or `mdata` are two entries: InLean
  may miss where con-leche hits, never the converse.
-/

/-- Binder names, binder infos, `nonDep` and `mdata` erased, hereditarily:
what `toCL` keeps. -/
def erase : Expr → Expr
  | .app f a => .app (erase f) (erase a)
  | .lam _ t b _ => .lam .anonymous (erase t) (erase b) .default
  | .forallE _ t b _ => .forallE .anonymous (erase t) (erase b) .default
  | .letE _ t v b _ => .letE .anonymous (erase t) (erase v) (erase b) false
  | .mdata _ e => erase e
  | .proj s i e => .proj s i (erase e)
  | e => e

/-- Binder names and binder infos erased, `nonDep` and `mdata` kept. -/
def eraseK : Expr → Expr
  | .app f a => .app (eraseK f) (eraseK a)
  | .lam _ t b _ => .lam .anonymous (eraseK t) (eraseK b) .default
  | .forallE _ t b _ => .forallE .anonymous (eraseK t) (eraseK b) .default
  | .letE _ t v b nd => .letE .anonymous (eraseK t) (eraseK v) (eraseK b) nd
  | .mdata m e => .mdata m (eraseK e)
  | .proj s i e => .proj s i (eraseK e)
  | e => e

/-- `e` with its top-level `mdata` wrappers peeled (O(wrappers)): how the
checker reads a node, as the official kernel's `whnf_core`/`infer` do,
never rebuilding a term. -/
def EO.stripTop : Expr → Expr
  | .mdata _ x => EO.stripTop x
  | e => e

theorem erase_stripTop (e : Expr) : erase (EO.stripTop e) = erase e := by
  induction e <;> simp_all [EO.stripTop, erase]

/-- The constructor of a node. -/
def ctorTag : Expr → Nat
  | .bvar .. => 0 | .fvar .. => 1 | .mvar .. => 2 | .sort .. => 3 | .const .. => 4
  | .app .. => 5 | .lam .. => 6 | .forallE .. => 7 | .letE .. => 8 | .lit .. => 9
  | .mdata .. => 10 | .proj .. => 11

theorem ctorTag_eraseK (e : Expr) : ctorTag (eraseK e) = ctorTag e := by
  cases e <;> rfl

/-- A memo entry of a comparison `R`: a pair a completed descent proved
related, the addresses it was seen at, the proof. -/
structure ClPair (R : Expr → Expr → Prop) where
  fst : Expr
  snd : Expr
  pa : USize
  pb : USize
  rel : R fst snd

abbrev ClMap (R : Expr → Expr → Prop) := Std.HashMap Nat (ClPair R)

/-- `probeHit` for a relation `R`: not inlined, everything borrowed. -/
@[noinline] def clProbeHit {R : Expr → Expr → Prop} (m : @& ClMap R) (key : Nat) (pa pb : USize)
    (a b : @& Expr) : { h : Bool // h = true → R a b } :=
  match m.get? key with
  | some p =>
    if p.pa == pa && p.pb == pb then
      match ptrDecStruct p.fst a, ptrDecStruct p.snd b with
      | isTrue h1, isTrue h2 => ⟨true, fun _ => h1 ▸ h2 ▸ p.rel⟩
      | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
    else ⟨false, fun h => Bool.noConfusion h⟩
  | none => ⟨false, fun h => Bool.noConfusion h⟩

/-- `BeqSt` for a relation `R`: `fail`, or the memo of `R`-related pairs. -/
inductive ClSt (R : Expr → Expr → Prop) where
  | fail
  | empty
  | table (m : ClMap R)

@[inline] def ClSt.ok {R : Expr → Expr → Prop} : ClSt R → Bool
  | .fail => false
  | _ => true

@[inline] def ClSt.record {R : Expr → Expr → Prop} (st : ClSt R) (key : Nat) (p : ClPair R) :
    ClSt R :=
  match st with
  | .table m => .table (m.insert key p)
  | _ => .table ((Std.HashMap.emptyWithCapacity (key % 8 + 8) : ClMap R).insert key p)

theorem ClSt.record_ok {R : Expr → Expr → Prop} (st : ClSt R) (key : Nat) (p : ClPair R) :
    (st.record key p).ok = true := by
  cases st <;> rfl

/-- `BeqSt.recordEq` for `R`: not inlined, the terms borrowed. -/
@[noinline] def ClSt.recordRel {R : Expr → Expr → Prop} (st : ClSt R) (a b : @& Expr)
    (pa pb : USize) (h : R a b) : ClSt R :=
  st.record (beqKey pa pb) ⟨a, b, pa, pb, h⟩

abbrev ClOk (R : Expr → Expr → Prop) := { s : ClSt R // s.ok = true }

/-- A descent's answer for `P`: the state, not `fail` exactly when `P`. -/
abbrev ClOutX (R : Expr → Expr → Prop) (P : Prop) := Squash { s : ClSt R // s.ok = true ↔ P }

@[inline] def ClOutX.yes {R : Expr → Expr → Prop} {P : Prop} (st : ClOk R) (h : P) :
    ClOutX R P :=
  Quot.mk _ ⟨st.1, fun _ => h, fun _ => st.2⟩

@[inline] def ClOutX.no {R : Expr → Expr → Prop} {P : Prop} (h : ¬ P) : ClOutX R P :=
  Quot.mk _ ⟨.fail, fun e => Bool.noConfusion e, fun e => absurd e h⟩

@[inline] def ClOutX.mk {R : Expr → Expr → Prop} {P : Prop} (d : Decidable P) (st : ClOk R) :
    ClOutX R P :=
  match d with
  | isTrue h => .yes st h
  | isFalse h => .no h

@[inline] def ClOutX.cast {R : Expr → Expr → Prop} {P Q : Prop} (r : ClOutX R P) (e : P ↔ Q) :
    ClOutX R Q :=
  Squash.lift r fun r => Quot.mk _ ⟨r.1, r.2.trans e⟩

/-- Twin of `enterBeq` for a reflexive comparison `R`: `rej` is the O(1)
test that rejects a pair (the data word, or the part of it `R` keeps), and
the descent `rec` runs on a pair `rej` let through. -/
@[inline] def enterCl {R : Expr → Expr → Prop} (hrefl : ∀ a, R a a) (rej : Expr → Expr → Bool)
    (hrej : ∀ a b, rej a b = true → ¬ R a b) (st : ClOk R) (a b : @& Expr)
    (rec : rej a b = false → ClOk R → ClOutX R (R a b)) : ClOutX R (R a b) :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then
    match ptrDec a b with
    | isTrue h => .yes st (h ▸ hrefl a)
    | isFalse _ =>
      if h : rej a b then .no (hrej a b h)
      else rec (Bool.of_not_eq_true h) st
  else if h : rej a b then .no (hrej a b h)
  else
  have h := Bool.of_not_eq_true h
  if !beqRecursive a then rec h st
  else withExcl a fun ea =>
    if ea then rec h st
    else withExcl b fun eb =>
    if eb then rec h st
    else
    let hit : { h : Bool // h = true → R a b } :=
      match st.1 with
      | .table m => clProbeHit m (beqKey pa pb) pa pb a b
      | _ => ⟨false, fun h => Bool.noConfusion h⟩
    if hh : hit.1 then .yes st (hit.2 hh)
    else Squash.lift (rec h st) fun r =>
      if hr : r.1.ok then
        .yes ⟨r.1.recordRel a b pa pb (r.2.mp hr), ClSt.record_ok ..⟩ (r.2.mp hr)
      else Quot.mk _ r

/-- Lean's cached data reads no binder name or binder info. -/
theorem data_eraseK : ∀ e : Expr, (eraseK e).data = e.data := by
  intro e
  induction e <;> simp_all [eraseK, Expr.data]

theorem dataNe_eraseK (a b : Expr) (h : dataNe a b = true) : eraseK a ≠ eraseK b := by
  intro e
  have : dataWord a = dataWord b := by
    simp only [dataWord]; rw [← data_eraseK a, e, data_eraseK]
  simp [dataNe, this] at h

/-- The key comparison's relation. -/
abbrev KeyR (a b : Expr) : Prop := eraseK a = eraseK b

/-- A child pair of the key comparison: the pointers, the data word, the
memo, the descent `go`. -/
@[inline] def keyChild (st : ClOk KeyR) (a b : @& Expr)
    (go : ClOk KeyR → ClOutX KeyR (KeyR a b)) : ClOutX KeyR (KeyR a b) :=
  enterCl (R := KeyR) (fun _ => rfl) dataNe dataNe_eraseK st a b fun _ => go

/-- The key comparison's descent (`eraseK`): names and infos not compared,
`nonDep` and `mdata` compared; a pair of different constructors is unequal, a
pair of leaves decided by their equality.  An application compares its last
argument first, then walks down the spine as `beqGoX` does. -/
def keyGoX (st : ClOk KeyR) (a b : @& Expr) : ClOutX KeyR (KeyR a b) :=
  match a, b with
  | .app f x, .app g y =>
    Squash.lift (keyChild st x y fun s => keyGoX s x y) fun r₁ =>
      if h₁ : r₁.1.ok then
        have hx : KeyR x y := r₁.2.mp h₁
        let rf : ClOutX KeyR (KeyR f g) :=
          if hf : beqIsApp f then
            if hg : beqIsApp g then keyGoX ⟨r₁.1, h₁⟩ f g
            else .no (fun e => hg (by
              cases f <;> cases g <;> simp_all [beqIsApp, KeyR, eraseK]))
          else keyChild ⟨r₁.1, h₁⟩ f g fun s => keyGoX s f g
        rf.cast ⟨fun h' => by simp only [KeyR, eraseK] at *; simp only [hx, h'],
          fun e => (Expr.app.inj e).1⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.app.inj e).2))
  | .lam _ t b _, .lam _ t' b' _ =>
    Squash.lift (keyChild st t t' fun s => keyGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : KeyR t t' := r₁.2.mp h₁
        (keyChild ⟨r₁.1, h₁⟩ b b' fun s => keyGoX s b b').cast
          ⟨fun h₂ => by simp only [KeyR, eraseK] at *; simp only [ht, h₂],
           fun e => (Expr.lam.inj e).2.2.1⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.lam.inj e).2.1))
  | .forallE _ t b _, .forallE _ t' b' _ =>
    Squash.lift (keyChild st t t' fun s => keyGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : KeyR t t' := r₁.2.mp h₁
        (keyChild ⟨r₁.1, h₁⟩ b b' fun s => keyGoX s b b').cast
          ⟨fun h₂ => by simp only [KeyR, eraseK] at *; simp only [ht, h₂],
           fun e => (Expr.forallE.inj e).2.2.1⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.forallE.inj e).2.1))
  | .letE _ t v b nd, .letE _ t' v' b' nd' =>
    if hn : nd = nd' then
    Squash.lift (keyChild st t t' fun s => keyGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : KeyR t t' := r₁.2.mp h₁
        Squash.lift (keyChild ⟨r₁.1, h₁⟩ v v' fun s => keyGoX s v v') fun r₂ =>
          if h₂ : r₂.1.ok then
            have hv : KeyR v v' := r₂.2.mp h₂
            (keyChild ⟨r₂.1, h₂⟩ b b' fun s => keyGoX s b b').cast
              ⟨fun h₃ => by subst hn; simp only [KeyR, eraseK] at *; simp only [ht, hv, h₃],
               fun e => (Expr.letE.inj e).2.2.2.1⟩
          else .no (fun e => h₂ (r₂.2.mpr (Expr.letE.inj e).2.2.1))
      else .no (fun e => h₁ (r₁.2.mpr (Expr.letE.inj e).2.1))
    else .no (fun e => hn (Expr.letE.inj e).2.2.2.2)
  | .proj s i x, .proj s' i' x' =>
    if hs : s = s' ∧ i = i' then
      (keyChild st x x' fun r => keyGoX r x x').cast
        ⟨fun h => by obtain ⟨rfl, rfl⟩ := hs; simp only [KeyR, eraseK] at *; simp only [h],
         fun e => (Expr.proj.inj e).2.2⟩
    else .no (fun e => hs ⟨(Expr.proj.inj e).1, (Expr.proj.inj e).2.1⟩)
  | .mdata d x, .mdata d' x' =>
    if hd : d = d' then
      (keyChild st x x' fun r => keyGoX r x x').cast
        ⟨fun h => by subst hd; simp only [KeyR, eraseK] at *; simp only [h],
         fun e => (Expr.mdata.inj e).2⟩
    else .no (fun e => hd (Expr.mdata.inj e).1)
  | a, b =>
    if hc : ctorTag a = ctorTag b then
      -- same constructor, not one the arms above take: two leaves (O(1) `eraseK`)
      .mk ((inferInstance : DecidableEq Expr) (eraseK a) (eraseK b)) st
    else .no (fun e => hc (by rw [← ctorTag_eraseK a, ← ctorTag_eraseK b, e]))

theorem erase_mdata (m : MData) (x : Expr) : erase (.mdata m x) = erase x := rfl

theorem ctorTag_erase_of_ne (e : Expr) (h : ctorTag e ≠ 10) : ctorTag (erase e) = ctorTag e := by
  cases e <;> first | rfl | exact absurd rfl h

/-- The part of the cached data word that `mdata` copies from its body: the
four flags and the loose-variable range (bits 40 to 63), not the hash or
the depth. -/
@[inline] def dataInv (e : Expr) : UInt64 := dataWord e >>> 40

/-- The words' `mdata`-invariant parts differ. -/
@[inline] def clDataNe (a b : Expr) : Bool := dataInv a != dataInv b

theorem clDataNe_self (a : Expr) : clDataNe a a = false := by simp [clDataNe]

/-- **The checker's comparison, as a plain descent**: `mdata` read through,
each pair of children first by `clDataNe`, then the constructor cases as
`keyGoX`'s; two leaves by their equality after `erase`.  `Expr.clEq` is its
memoised execution. -/
def clB : Expr → Expr → Bool
  | .mdata _ x, b => clB x b
  | a, .mdata _ y => clB a y
  | .app f x, .app g y => (!clDataNe f g && clB f g) && (!clDataNe x y && clB x y)
  | .lam _ t b _, .lam _ t' b' _ => (!clDataNe t t' && clB t t') && (!clDataNe b b' && clB b b')
  | .forallE _ t b _, .forallE _ t' b' _ =>
    (!clDataNe t t' && clB t t') && (!clDataNe b b' && clB b b')
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    (!clDataNe t t' && clB t t') && (!clDataNe v v' && clB v v') && (!clDataNe b b' && clB b b')
  | .proj s i x, .proj s' i' x' => decide (s = s' ∧ i = i') && (!clDataNe x x' && clB x x')
  | a, b =>
    if ctorTag a ≠ ctorTag b ∧ ctorTag a ≠ 10 ∧ ctorTag b ≠ 10 then false
    else decide (erase a = erase b)
termination_by a b => sizeOf a + sizeOf b

/-- A child pair: the data word's invariant part, then the descent. -/
def clStep (a b : Expr) : Bool := !clDataNe a b && clB a b

theorem clStep_of {a b : Expr} (h : clDataNe a b = false) : clStep a b = clB a b := by
  simp [clStep, h]

theorem clB_app (f x g y : Expr) : clB (.app f x) (.app g y) = (clStep f g && clStep x y) := by
  rw [clB]; rfl
theorem clB_lam (n n' : Name) (t b t' b' : Expr) (bi bi' : BinderInfo) :
    clB (.lam n t b bi) (.lam n' t' b' bi') = (clStep t t' && clStep b b') := by
  rw [clB]; rfl
theorem clB_forallE (n n' : Name) (t b t' b' : Expr) (bi bi' : BinderInfo) :
    clB (.forallE n t b bi) (.forallE n' t' b' bi') = (clStep t t' && clStep b b') := by
  rw [clB]; rfl
theorem clB_letE (n n' : Name) (t v b t' v' b' : Expr) (nd nd' : Bool) :
    clB (.letE n t v b nd) (.letE n' t' v' b' nd') =
      (clStep t t' && clStep v v' && clStep b b') := by
  rw [clB]; rfl
theorem clB_proj (s s' : Name) (i i' : Nat) (x x' : Expr) :
    clB (.proj s i x) (.proj s' i' x') = (decide (s = s' ∧ i = i') && clStep x x') := by
  rw [clB]; rfl
theorem clB_mdata_l (m : MData) (x b : Expr) : clB (.mdata m x) b = clB x b := by
  rw [clB]

theorem clB_mdata_r (m : MData) (y : Expr) : ∀ a, clB a (.mdata m y) = clB a y
  | .mdata m' x => by rw [clB_mdata_l, clB_mdata_l, clB_mdata_r m y x]
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .app .. | .lam .. | .forallE ..
  | .letE .. | .lit .. | .proj .. => by rw [clB]; intro _ _ h; nomatch h

theorem clB_refl : ∀ a, clB a a = true
  | .mdata m x => by rw [clB_mdata_l, clB_mdata_r, clB_refl x]
  | .app f x => by simp [clB_app, clStep, clDataNe_self, clB_refl f, clB_refl x]
  | .lam _ t b _ => by simp [clB_lam, clStep, clDataNe_self, clB_refl t, clB_refl b]
  | .forallE _ t b _ => by simp [clB_forallE, clStep, clDataNe_self, clB_refl t, clB_refl b]
  | .letE _ t v b _ => by
    simp [clB_letE, clStep, clDataNe_self, clB_refl t, clB_refl v, clB_refl b]
  | .proj _ _ x => by simp [clB_proj, clStep, clDataNe_self, clB_refl x]
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => by simp [clB, ctorTag]

/-- `clB` on a pair neither of which is `mdata` and which is not one
compound constructor twice: the constructors, then `erase` (O(1) there). -/
theorem clB_other (a b : Expr) (ha : ctorTag a ≠ 10) (hb : ctorTag b ≠ 10)
    (hs : ctorTag a = ctorTag b → beqRecursive a = false) :
    clB a b = (ctorTag a == ctorTag b && decide (erase a = erase b)) := by
  cases a <;> cases b <;> simp_all [clB, ctorTag, beqRecursive]

theorem clStep_refl (a : Expr) : clStep a a = true := by
  simp [clStep, clDataNe_self, clB_refl]

/-- `clB` answers `true` only on terms equal after `erase`. -/
theorem clB_sound : ∀ a b, clB a b = true → erase a = erase b := by
  intro a b
  fun_induction clB a b <;> simp_all [erase]

theorem clStep_sound {a b : Expr} (h : clStep a b = true) : erase a = erase b := by
  simp only [clStep, Bool.and_eq_true] at h; exact clB_sound a b h.2

/-- The comparison's relation on a pair of children. -/
abbrev ClR (a b : Expr) : Prop := clStep a b = true

theorem clDataNe_rej (a b : Expr) (h : clDataNe a b = true) : ¬ ClR a b := by
  simp [ClR, clStep, h]

/-- A child pair of the checker's comparison: the pointers, the invariant
part of the data word, the memo, the descent `go`. -/
@[inline] def clChild (st : ClOk ClR) (a b : @& Expr)
    (go : ClOk ClR → ClOutX ClR (clB a b = true)) : ClOutX ClR (ClR a b) :=
  enterCl clStep_refl clDataNe clDataNe_rej st a b fun h s =>
    (go s).cast (by simp only [ClR, clStep_of h])

/-- The checker comparison's descent (`clB`): a `mdata` node is read
through (no rebuilt term), then the constructor cases, each child through
`clChild`.  An application compares its last argument first, then walks
down the spine: where both functions are applications the descent continues
on them directly, past the invariant part of their data words (`clStep`'s
own test), with no pointer, exclusivity or memo step. -/
def clGoX (st : ClOk ClR) (a b : @& Expr) : ClOutX ClR (clB a b = true) :=
  match a, b with
  | .mdata m x, b => (clGoX st x b).cast (by rw [clB_mdata_l])
  | a, .mdata m y => (clGoX st a y).cast (by rw [clB_mdata_r])
  | .app f x, .app g y =>
    Squash.lift (clChild st x y fun s => clGoX s x y) fun r₁ =>
      if h₁ : r₁.1.ok then
        have hx : ClR x y := r₁.2.mp h₁
        let rf : ClOutX ClR (ClR f g) :=
          if beqIsApp f && beqIsApp g then
            if hd : clDataNe f g then .no (clDataNe_rej f g hd)
            else (clGoX ⟨r₁.1, h₁⟩ f g).cast
              (by simp only [ClR, clStep_of (Bool.of_not_eq_true hd)])
          else clChild ⟨r₁.1, h₁⟩ f g fun s => clGoX s f g
        rf.cast (by simp_all [clB_app])
      else .no (by have := r₁.2; simp_all [clB_app])
  | .lam _ t b _, .lam _ t' b' _ =>
    Squash.lift (clChild st t t' fun s => clGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : ClR t t' := r₁.2.mp h₁
        (clChild ⟨r₁.1, h₁⟩ b b' fun s => clGoX s b b').cast (by simp_all [clB_lam])
      else .no (by have := r₁.2; simp_all [clB_lam])
  | .forallE _ t b _, .forallE _ t' b' _ =>
    Squash.lift (clChild st t t' fun s => clGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : ClR t t' := r₁.2.mp h₁
        (clChild ⟨r₁.1, h₁⟩ b b' fun s => clGoX s b b').cast (by simp_all [clB_forallE])
      else .no (by have := r₁.2; simp_all [clB_forallE])
  | .letE _ t v b _, .letE _ t' v' b' _ =>
    Squash.lift (clChild st t t' fun s => clGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : ClR t t' := r₁.2.mp h₁
        Squash.lift (clChild ⟨r₁.1, h₁⟩ v v' fun s => clGoX s v v') fun r₂ =>
          if h₂ : r₂.1.ok then
            have hv : ClR v v' := r₂.2.mp h₂
            (clChild ⟨r₂.1, h₂⟩ b b' fun s => clGoX s b b').cast (by simp_all [clB_letE])
          else .no (by have := r₂.2; simp_all [clB_letE])
      else .no (by have := r₁.2; simp_all [clB_letE])
  | .proj s i x, .proj s' i' x' =>
    if hs : s = s' ∧ i = i' then
      (clChild st x x' fun r => clGoX r x x').cast (by simp_all [clB_proj])
    else .no (by simp_all [clB_proj])
  | a, b =>
    if h : ctorTag a ≠ 10 ∧ ctorTag b ≠ 10 ∧ (ctorTag a = ctorTag b → beqRecursive a = false) then
      -- two leaves of one constructor, or different constructors
      if hc : ctorTag a = ctorTag b then
        .mk (decidable_of_iff (erase a = erase b)
          (by rw [clB_other a b h.1 h.2.1 h.2.2]; simp [hc])) st
      else .no (by rw [clB_other a b h.1 h.2.1 h.2.2]; simp [hc])
    else .mk (instDecidableEqBool (clB a b) true) st
termination_by (sizeOf a + sizeOf b)

/-- **The memo maps' key equality**: equal after `eraseK`. -/
def Expr.keyEq (a b : Expr) : Bool := decide (eraseK a = eraseK b)

/-- The pointer test, the cached data word, then the memoised descent. -/
def Expr.keyEqMemo (a b : Expr) : Bool :=
  withPtrEq a b
    (fun _ => if !dataNe a b then
        @decide (eraseK a = eraseK b)
          (Squash.lift (keyGoX ⟨.empty, rfl⟩ a b) (fun r => decidable_of_iff _ r.2))
      else false)
    (fun h => by subst h; simp [dataNe_self])

@[csimp] theorem Expr.keyEq_eq_keyEqMemo : @Expr.keyEq = @Expr.keyEqMemo := by
  funext a b
  unfold Expr.keyEq Expr.keyEqMemo withPtrEq
  split
  · congr 1
  · rename_i h
    exact decide_eq_false (dataNe_eraseK a b (by simpa using h))

/-- **InLean's checker equality**: the pointer test, the invariant part of
the cached data word, then the memoised descent (`clB`, executed by
`clGoX`).  It answers `true` only on terms equal after `erase`
(`Expr.clEq_sound`). -/
def Expr.clEq (a b : Expr) : Bool :=
  withPtrEq a b
    (fun _ => !clDataNe a b &&
      @decide (clB a b = true)
        (Squash.lift (clGoX ⟨.empty, rfl⟩ a b) (fun r => decidable_of_iff _ r.2)))
    (fun h => by subst h; simp [clDataNe_self, clB_refl])

/-- `Expr.clEq` is the plain descent's answer on the pair. -/
theorem Expr.clEq_eq (a b : Expr) : Expr.clEq a b = clStep a b := by
  unfold Expr.clEq withPtrEq clStep
  cases clDataNe a b <;> simp

theorem Expr.clEq_sound {a b : Expr} (h : Expr.clEq a b = true) : erase a = erase b :=
  clStep_sound (by rwa [Expr.clEq_eq] at h)

/-- **The scoped equality of expressions in InLean's checker**: `Expr.clEq`. -/
scoped instance instBEqExprI : BEq Expr := ⟨Expr.clEq⟩

/-- **A memo key**: an expression compared by `Expr.keyEq`, hashed by Lean's
cached hash (which reads no binder name or info). -/
structure EKey where
  e : Expr

instance : BEq EKey := ⟨fun a b => Expr.keyEq a.e b.e⟩
instance : Hashable EKey := ⟨fun a => hash a.e⟩

instance : EquivBEq EKey where
  rfl := by simp [BEq.beq, Expr.keyEq]
  symm h := by simp only [BEq.beq, Expr.keyEq, decide_eq_true_eq] at *; exact h.symm
  trans h₁ h₂ := by
    simp only [BEq.beq, Expr.keyEq, decide_eq_true_eq] at *; exact h₁.trans h₂

/-- The bulk-instantiation memo's key: a term and the values, each by
`keyEq`. -/
structure InstKey where
  e : Expr
  vs : List Expr

def keyEqList : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => Expr.keyEq a b && keyEqList as bs
  | _, _ => false

instance : BEq InstKey := ⟨fun a b => Expr.keyEq a.e b.e && keyEqList a.vs b.vs⟩
instance : Hashable InstKey := ⟨fun a => mixHash (hash a.e) (hash a.vs)⟩

end Lean.Kernel.InLean
