import tools.super

section
open super tactic
example (i : Type) (a b : i) (p : i → Prop) (H : a = b) (Hpa : p a) : true := by do
H ← get_local `H >>= clause.of_classical_proof,
Hpa ← get_local `Hpa >>= clause.of_classical_proof,
a ← get_local `a,
try_sup (λx y, ff) H Hpa 0 0 [0] tt ff ``super.sup_ltr >>= clause.validate,
to_expr ``(trivial) >>= apply

example (i : Type) (a b : i) (p : i → Prop) (H : a = b) (Hpa : p a → false) (Hpb : p b → false) : true := by do
H ← get_local `H >>= clause.of_classical_proof,
Hpa ← get_local `Hpa >>= clause.of_classical_proof,
Hpb ← get_local `Hpb >>= clause.of_classical_proof,
try_sup (λx y, ff) H Hpa 0 0 [0] tt ff ``super.sup_ltr >>= clause.validate,
try_sup (λx y, ff) H Hpb 0 0 [0] ff ff ``super.sup_rtl >>= clause.validate,
to_expr ``(trivial) >>= apply

example (i : Type) (p q : i → Prop) (H : ∀x y, p x → q y → false) : true := by do
h ← get_local `H >>= clause.of_classical_proof,
(op, lcs) ← h^.open_constn h^.num_binders,
guard $ (get_components lcs)^.length = 2,
triv

example (i : Type) (p : i → i → Prop) (H : ∀x y z, p x y → p y z → false) : true := by do
h ← get_local `H >>= clause.of_classical_proof,
(op, lcs) ← h^.open_constn h^.num_binders,
guard $ (get_components lcs)^.length = 1,
triv

example (i : Type) (p : i → i → Type) (c : i) (h : ∀ (x : i), p x c → p x c) : true := by do
h ← get_local `h, hcls ← clause.of_classical_proof h,
taut ← is_taut hcls,
when (¬taut) failed,
to_expr ``(trivial) >>= apply

open tactic
example (m n : ℕ) : true := by do
e₁ ← to_expr ```((0 + (m : ℕ)) + 0),
e₂ ← to_expr ```(0 + (0 + (m : ℕ))),
e₃ ← to_expr ```(0 + (m : ℕ)),
prec ← return (contained_funsyms e₁)^.keys,
prec_gt ← return $ prec_gt_of_name_list prec,
guard $ lpo prec_gt e₁ e₃,
guard $ lpo prec_gt e₂ e₃,
to_expr ``(trivial) >>= apply

/-
open tactic
example (i : Type) (f : i → i) (c d x : i) : true := by do
ef ← get_local `f, ec ← get_local `c, ed ← get_local `d,
syms ← return [ef,ec,ed],
prec_gt ← return $ prec_gt_of_name_list (list.map local_uniq_name [ef, ec, ed]),
sequence' (do s1 ← syms, s2 ← syms, return (do
  s1_fmt ← pp s1, s2_fmt ← pp s2,
  trace (s1_fmt ++ to_fmt " > " ++ s2_fmt ++ to_fmt ": " ++ to_fmt (prec_gt s1 s2))
)),

exprs ← @mapM tactic _ _ _ to_expr [`(f c), `(f (f c)), `(f d), `(f x), `(f (f x))],
sequence' (do e1 ← exprs, e2 ← exprs, return (do
  e1_fmt ← pp e1, e2_fmt ← pp e2,
  trace (e1_fmt ++ to_fmt" > " ++ e2_fmt ++ to_fmt": " ++ to_fmt (lpo prec_gt e1 e2))
)),

mk_const ``true.intro >>= apply
-/
open monad
example (x y : ℕ) (h : nat.zero = nat.succ nat.zero) (h2 : nat.succ x = nat.succ y) : true := by do
h ← get_local `h >>= clause.of_classical_proof,
h2 ← get_local `h2 >>= clause.of_classical_proof,
cs ← try_no_confusion_eq_r h 0,
for' cs clause.validate,
cs ← try_no_confusion_eq_r h2 0,
for' cs clause.validate,
to_expr ``(trivial) >>= exact
end
