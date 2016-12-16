-- Polytime version of lexicographic path order as described in:
-- Things to know when implementing LPO, Bernd Löchner, ESFOR 2004
import .utils
open expr decidable monad

def lex {T} [decidable_eq T] (gt : T → T → bool) : list T → list T → bool
| (s::ss) (t::ts) := if s = t then lex ss ts else gt s t
| _ _ := ff

def majo {T} (gt : T → T → bool) (s : T) : list T → bool
| [] := tt
| (t::ts) := gt s t && majo ts

meta def alpha (lpo : expr → expr → bool) : list expr → expr → bool
| [] _ := ff
| (s::ss) t := to_bool (s = t) || lpo s t || alpha ss t

meta def lex_ma (lpo : expr → expr → bool) (s t : expr) : list expr → list expr → bool
| (si::ss) (ti::ts) :=
  if si = ti then lex_ma ss ts
  else if lpo si ti then majo lpo s ts
  else alpha lpo (si::ss) t
| _ _ := ff

meta def lpo (prec_gt : expr → expr → bool) : expr → expr → bool | s t :=
if prec_gt (get_app_fn s) (get_app_fn t) then majo lpo s (get_app_args t)
else if get_app_fn s = get_app_fn t then lex_ma lpo s t (get_app_args s) (get_app_args t)
else alpha lpo (get_app_args s) t

meta def prec_gt_of_name_list (ns : list name) : expr → expr → bool :=
let nis := rb_map.of_list (list.zip_with_index ns) in
λs t, match (rb_map.find nis (name_of_funsym s), rb_map.find nis (name_of_funsym t)) with
| (some si, some ti) := to_bool (si > ti)
| _ := ff
end

open tactic
example (m n : ℕ) : true := by do
e₁ ← to_expr `((0 + (m : ℕ)) + 0),
e₂ ← to_expr `(0 + (0 + (m : ℕ))),
e₃ ← to_expr `(0 + (m : ℕ)),
prec ← return (contained_funsyms e₁)↣keys,
prec_gt ← return $ prec_gt_of_name_list prec,
guard $ lpo prec_gt e₁ e₃,
guard $ lpo prec_gt e₂ e₃,
to_expr `(trivial) >>= apply

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
