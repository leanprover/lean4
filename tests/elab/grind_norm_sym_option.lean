/-!
`grind` with the `Sym.simp`-based normalizer, selected by `set_option backward.grind.normalizer
false`. The goals exercise the entry points of the normalizer: hypotheses and the target
(`preprocess`), E-matching instances, generalized patterns (`dsimp`), and pattern normalization
at attribute time.
-/

set_option backward.grind.normalizer false

-- Propositional and arithmetic normalization of hypotheses and target
example (p q : Prop) (h : ¬(p ∨ q)) : ¬p := by grind
example (a b : Nat) (h : ¬(a ≤ b)) : b < a := by grind
example (a b : Nat) (h : a + 0 = b) : b = a := by grind
example (i j : Int) (h : 2 * i = 4 * j) : i = 2 * j := by grind
example (x y : Fin 5) (h : 3 * x + 1 = 0) : x = 3 := by grind
example (a : Nat) (h : (3 : Fin 5).val = a) : a = 3 := by grind

-- `let`/`have` and `match`
example (f : Nat → Nat) (a : Nat) (h : (let x := a + 0; f x) = 1) : f a = 1 := by grind
example (o : Option Nat) (h : (match o with | some x => x + 0 | none => 0) = 1) : o ≠ none := by grind
example (a b : Nat) (h : (if a < b then a + 0 else 0 + b) = 7) : a = 7 ∨ b = 7 := by grind

-- Ground evaluation
example (c : Char) (h : c = 'a') : c.toNat = 97 := by grind
example (s : String) (h : s = "ab" ++ "c") : s = "abc" := by grind
example (x : BitVec 8) (h : x = 3#8 + 5#8) : x = 8 := by grind

-- E-matching with theorems whose patterns are normalized at attribute time
def f (n : Nat) : Nat := n + 1

@[grind =] theorem f_succ (n : Nat) : f (n.succ) = n + 2 := by simp [f]
example (n : Nat) : f (n + 1) = n + 2 := by grind
example (n : Nat) (h : f (n + 1) = 5) : n = 3 := by grind

-- Generalized patterns (the `dsimp` path of the normalizer)
example (xs : List Nat) (h : xs.length = 3) : xs ≠ [] := by grind
example (a : Array Nat) (i : Nat) (h : i < a.size) (h' : a[i] = 7) : a.toList[i]? = some 7 := by grind

-- `[grind norm]` and `[grind unfold]` rules are shared with the legacy normalizer
opaque g : Nat → Nat
@[grind norm] axiom g_ax (x : Nat) : g (x + 1) = g x + 1
example (a : Nat) : g (a + 1) = g a + 1 := by grind
-- `g (a + 2)` needs offset unification against the pattern `g (x + 1)`, which the `Sym.simp`
-- rewriter does not do; see the `p (a + 2)` probe in `grind_norm_1.lean`.

@[grind unfold] def h (x : Nat) := 2 * x
example (a : Nat) (ha : h a = 6) : a = 3 := by grind

-- Hypotheses introduced with `intro` go through the target normalization
example (p q r : Prop) : (p → q) → (q → r) → p → r := by grind
example : ∀ n : Nat, n + 0 = n := by grind
example (a : Nat) : ∀ b, a ≤ b → ¬(b < a) := by grind
