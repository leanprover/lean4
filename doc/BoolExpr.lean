open Std
open Lean

inductive BoolExpr where
  | var (name : String)
  | val (b : Bool)
  | or  (p q : BoolExpr)
  | not (p : BoolExpr)
  deriving Repr, BEq, DecidableEq

def BoolExpr.isValue : BoolExpr → Bool
  | val _ => true
  | _     => false

instance : Inhabited BoolExpr where
  default := BoolExpr.val false

namespace BoolExpr

deriving instance DecidableEq for BoolExpr

#eval decide (BoolExpr.val true = BoolExpr.val false)

#check (a b : BoolExpr) → Decidable (a = b)

abbrev Context := AssocList String Bool

def denote (ctx : Context) : BoolExpr → Bool
  | BoolExpr.or p q => denote ctx p || denote ctx q
  | BoolExpr.not p  => !denote ctx p
  | BoolExpr.val b => b
  | BoolExpr.var x => if let some b := ctx.find? x then b else false

def simplify : BoolExpr → BoolExpr
  | or p q => mkOr (simplify p) (simplify q)
  | not p  => mkNot (simplify p)
  | e      => e
where
  mkOr : BoolExpr → BoolExpr → BoolExpr
    | p, val true   => val true
    | p, val false  => p
    | val true, p   => val true
    | val false, p  => p
    | p, q          => or p q

  mkNot : BoolExpr → BoolExpr
    | val b => val (!b)
    | p     => not p

@[simp] theorem denote_not_Eq (ctx : Context) (p : BoolExpr) : denote ctx (not p) = !denote ctx p := rfl
@[simp] theorem denote_or_Eq (ctx : Context) (p q : BoolExpr) : denote ctx (or p q) = (denote ctx p || denote ctx q) := rfl
@[simp] theorem denote_val_Eq (ctx : Context) (b : Bool) : denote ctx (val b) = b := rfl

@[simp] theorem denote_mkNot_Eq (ctx : Context) (p : BoolExpr) : denote ctx (simplify.mkNot p) = denote ctx (not p) := by
  cases p <;> rfl
@[simp] theorem mkOr_p_true (p : BoolExpr) : simplify.mkOr p (val true) = val true := by
  cases p with
  | val x => cases x <;> rfl
  | _     => rfl
@[simp] theorem mkOr_p_false (p : BoolExpr) : simplify.mkOr p (val false) = p := by
  cases p with
  | val x => cases x <;> rfl
  | _     => rfl
@[simp] theorem mkOr_true_p (p : BoolExpr) : simplify.mkOr (val true) p = val true := by
  cases p with
  | val x => cases x <;> rfl
  | _     => rfl
@[simp] theorem mkOr_false_p (p : BoolExpr) : simplify.mkOr (val false) p = p := by
  cases p with
  | val x => cases x <;> rfl
  | _     => rfl

@[simp] theorem denote_mkOr (ctx : Context) (p q : BoolExpr) : denote ctx (simplify.mkOr p q) = denote ctx (or p q) := by
  cases p with
  | val x => cases q with
    | val y => cases x <;> cases y <;> simp
    | _     => cases x <;> simp
  | _ => cases q with
    | val y => cases y <;> simp
    | _     => rfl

@[simp] theorem simplify_not (p : BoolExpr) : simplify (not p) = simplify.mkNot (simplify p) := rfl
@[simp] theorem simplify_or (p q : BoolExpr) : simplify (or p q) = simplify.mkOr (simplify p) (simplify q) := rfl

def denote_simplify_eq (ctx : Context) (b : BoolExpr) : denote ctx (simplify b) = denote ctx b :=
  by induction b with
  | or p q ih₁ ih₂ => simp [ih₁, ih₂]
  | not p ih       => simp [ih]
  | _              => rfl

syntax "`[BExpr|" term "]" : term

macro_rules
 | `(`[BExpr| true])     => `(val true)
 | `(`[BExpr| false])    => `(val false)
 | `(`[BExpr| $x:ident]) => `(var $(quote x.getId.toString))
 | `(`[BExpr| $p ∨ $q])  => `(or `[BExpr| $p] `[BExpr| $q])
 | `(`[BExpr| ¬ $p])     => `(not `[BExpr| $p])

#check `[BExpr| ¬ p ∨ q]

syntax entry := ident " ↦ " term:max
syntax entry,* "⊢" term : term

macro_rules
  | `( $[$xs ↦ $vs],* ⊢ $p) =>
    let xs := xs.map fun x => quote x.getId.toString
    `(denote (List.toAssocList [$[($xs, $vs)],*]) `[BExpr| $p])

#check b ↦ true ⊢ b ∨ b
#eval  a ↦ false, b ↦ false ⊢ b ∨ a
