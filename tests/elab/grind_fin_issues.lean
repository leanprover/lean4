/-!
# `grind` regressions in leanprover/lean4#14473 (`ToInt` => `[grind hom]`)

* **Baseline** `leanprover/lean4-nightly:nightly-2026-08-06`
* **Under test** `leanprover/lean4-pr-releases:pr-release-14473-62dd332` (includes #14709).
-/

/-! ## Mechanism A — a derived `Fin` equality is not lifted back for congruence

Sites: `Algebra/BigOperators/Intervals.lean` ×2, `Geometry/Euclidean/Incenter.lean` ×6,
`RingTheory/FormalGroup/Basic.lean` ×2, `Topology/EMetricSpace/BoundedVariation.lean` ×1,
`Order/Interval/Finset/Gaps.lean:77` ×1, `AlgebraicTopology/…/HornColimits.lean:220` ×1. -/

namespace A

-- ok: the `Fin` equality from the `val` equality
example (n : Nat) (a b : Fin n) (h : (a : Nat) = (b : Nat)) : a = b := by grind

-- ok: congruence from the `Fin` equality
example (n : Nat) (a b : Fin n) (f : Fin n → Nat) (h : a = b) : f a = f b := by grind

-- ok
example (n : Nat) (a b : Fin n) (f : Fin n → Nat) (h : (a : Nat) = (b : Nat)) :
    f a = f b := by grind

-- ok
example (n : Nat) (a : Fin n) (f : Fin (n + 1) → Nat) :
    f a.succ = if h : (a : Nat) + 1 < n + 1 then f ⟨(a : Nat) + 1, h⟩ else 0 := by grind

-- ok
example (n : Nat) (i : Fin n) (f : Fin n → Nat) (h : min (i : Nat) (n - 1) < n) :
    f ⟨min (i : Nat) (n - 1), h⟩ = f i := by grind

-- ok
example (k j : Nat) (hj : j < k) (x : Fin (k + 1)) (hx : x ≠ 0)
    (h : x = (⟨j, by omega⟩ : Fin k).succ) (g : Fin k → Nat) :
    g (x.pred hx) = g ⟨j, hj⟩ := by grind

-- ok
example (d : Fin 2 → Nat) (_h0 : d 0 = 1) (h1 : d 1 = 0) (w : Fin 2) (hw : w ≠ 0) :
    d w = 0 := by grind

-- ok
example (i₁ i₂ i₃ : Fin 3) (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (p : Fin 3 → Prop) (hp : ∀ x, p x ↔ x ≠ i₁) (f : Fin 3 → Nat) (w : Fin 3) (hw : p w) :
    f w = f i₂ ∨ f w = f i₃ := by grind

end A

/-! ## Mechanism B — `grind` splits its own atoms with an inconsistent `nestedProof` wrapper

Site: `Archive/Imo/Imo2024Q5.lean` ×4.

`grind` *does* assert the range fact. Its trace shows both `N + 1 ≤ ↑(m r)` (negated goal)
and `↑(m r) ≤ N` (range fact), and lists both under "True propositions" — yet `lia` reports
the linear constraints satisfiable (`[assign] N := 0`) and fails, because the two are not the
same atom. Under `pp.explicit` *and* `pp.proofs`, the `Fin.mk` bound inside the bundled
function's domain type carries its proof raw in one and wrapped in the other:

    Fin.mk … N (@_example._proof_1 N)
    Fin.mk … N (@Lean.Grind.nestedProof … (@_example._proof_1 N))

Proof-irrelevant and defeq, syntactically distinct. (`pp.explicit` alone hides this: it
prints both proofs as `⋯`.) `generalize m r = z; lia` succeeds; `omega` succeeds throughout.

All three ingredients below are necessary — dropping any one makes it pass. Injectivity and
`DFunLike` are *not* involved. In Mathlib these are `Set`'s reducible coe-sort, `Set.Icc`'s
`Fin.mk` bound, and `↪`. -/

namespace B

def Set (α : Type u) := α → Prop
@[reducible] def Set.Elem (s : Set α) := {x // s x}
instance : CoeSort (Set α) (Type _) := ⟨Set.Elem⟩
def Set.Icc [LE α] (a b : α) : Set α := fun x => a ≤ x ∧ x ≤ b

structure Embedding (α : Sort u) (β : Sort v) where
  toFun : α → β
  inj' : Function.Injective toFun
infixr:25 " ↪ " => Embedding
instance : CoeFun (α ↪ β) (fun _ => α → β) := ⟨Embedding.toFun⟩

-- ok
example {N : Nat} (a : Fin (N + 2))
    (m : Set.Icc a ⟨N, by lia⟩ ↪ Fin (N + 1))
    (r : Set.Icc a ⟨N, by lia⟩) : (m r : Nat) < N + 1 := by lia

-- ok: `Fin.mk` bound replaced by a variable
example {N : Nat} (a b : Fin (N + 2))
    (m : Set.Icc a b ↪ Fin (N + 1)) (r : Set.Icc a b) : (m r : Nat) < N + 1 := by lia

-- ok: bundled function replaced by a plain one
example {N : Nat} (a : Fin (N + 2))
    (m : Set.Icc a ⟨N, by lia⟩ → Fin (N + 1))
    (r : Set.Icc a ⟨N, by lia⟩) : (m r : Nat) < N + 1 := by lia

-- ok: the reducible coe-sort layer replaced by a bare `Subtype`
example {N : Nat} (a : Fin (N + 2))
    (m : Subtype (fun x : Fin (N + 2) => a ≤ x ∧ x ≤ ⟨N, by lia⟩) ↪ Fin (N + 1))
    (r : Subtype (fun x : Fin (N + 2) => a ≤ x ∧ x ≤ ⟨N, by lia⟩)) :
    (m r : Nat) < N + 1 := by lia

end B

/-! ## Mechanism C — `Fin` comparisons are never enqueued as case-split candidates

Site: `GroupTheory/Perm/Fin.lean:462` (`Fin.cycleIcc_comp_succAbove`).

`grind` decides which propositions to case-split in `checkAndAddSplitCandidate`
(`src/Lean/Meta/Tactic/Grind/Internalize.lean`), where anything `isMorallyIff` — i.e. an
equality whose carrier is `Prop` — is unconditionally enqueued.

`Fin.lt_def` and `Fin.le_def` are `[grind hom]` rules in this PR
(`src/Init/Grind/Homo/Fin.lean`). Hom rules are applied as out-of-E-graph rewrites followed
by `pushEq`; they never put an `Eq Prop _ _` term in the E-graph. So no `Fin` comparison is
ever morally-iff, and none is ever enqueued. `trace.grind.split.candidate` on the example
below: **baseline offers the comparisons as candidates, the PR offers none at all.**

Passing `= Fin.lt_def` *additionally* registers the lemma as an E-matching equation, whose
instances are genuine `Eq Prop _ _` terms — `(x < p) = (↑x + 1 ≤ ↑p)` — which are
morally-iff and do get enqueued. Hence either hint repairing it, and hence
`(splitImp := true)` repairing it too.

Nesting is what exposes this: choosing the outer rewrite requires deciding which side of `p`
the opaque term `T p x` lies on, while reducing `T p x` needs the inner rewrite. The baseline
breaks that cycle with a propositional split; the PR has no candidate to split on. -/

namespace C

axiom T {n : Nat} : Fin n → Fin n → Fin n
axiom T_lt {n : Nat} (p x : Fin n) (h : x < p) : T p x = x
axiom T_ge {n : Nat} (p x : Fin n) (h : p ≤ x) : T p x = x

-- ok
example {n : Nat} (p x : Fin n) : T p (T p x) = x := by grind [T_lt, T_ge]

-- ok: single level, no nesting
example {n : Nat} (p x : Fin n) : T p x = x := by grind [T_lt, T_ge]

-- ok: `= Fin.lt_def` supplies the missing morally-iff equations
example {n : Nat} (p x : Fin n) : T p (T p x) = x := by grind [T_lt, T_ge, = Fin.lt_def]

-- ok: so does splitting implications
example {n : Nat} (p x : Fin n) : T p (T p x) = x := by
  grind (splitImp := true) [T_lt, T_ge]

end C
