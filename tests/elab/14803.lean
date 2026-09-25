/-!
Regression test for #14803: the kernel used to try eta-expansion only after
delta-reduction, so checking `f a =?= fun x => f a x` symbolically normalized
`f a` instead of eta-expanding it. That normalization is exponential in the
tree's depth when `f` is a structural recursion over the tree, and it made the
kernel time out on the proof terms `simp` produces for goals whose two sides
differ only by eta.
-/

inductive T where
  | leaf
  | node (l r : T)

/-- Complete binary tree of depth `n` with structurally distinct subtrees, so
pointer-equality caching cannot collapse the comparison. -/
def mkT : Nat → Nat → T
  | 0, _ => .leaf
  | n+1, i => .node (mkT n (2*i)) (mkT n (2*i+1))

/-- Function-valued structural recursion, expensive to normalize symbolically. -/
def interp : T → Nat → Nat
  | .leaf => Nat.succ
  | .node l r => interp l ∘ interp r

/-- The defeq check the kernel has to perform, without `simp` in the picture. -/
theorem kernelEta : (fun x => interp (mkT 10 0) x) = interp (mkT 10 0) :=
  @rfl _ (fun x => interp (mkT 10 0) x)

def wrap (f : Nat → Nat) : Nat → Nat := f

theorem wrap_eq (f : Nat → Nat) : wrap f = fun x => f x := rfl

/-- `simp` closes this instantly and emits a proof whose `Eq.trans` forces the
kernel to check `interp (mkT 10 0) =?= fun x => interp (mkT 10 0) x`. -/
theorem viaSimp : wrap (interp (mkT 10 0)) = interp (mkT 10 0) := by
  simp -implicitDefEqProofs only [wrap_eq]
