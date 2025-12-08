inductive Ty where
| star: Ty
notation " ✶ " => Ty.star

abbrev Context : Type := List Ty

inductive Lookup : Context → Ty → Type where
| z : Lookup (t :: Γ) t

inductive Term : Context → Ty → Type where
| var : Lookup Γ a → Term Γ a
| lam : Term (✶ :: Γ) ✶ → Term Γ ✶
| ap : Term Γ ✶ → Term Γ ✶ → Term Γ ✶

-- set_option trace.Meta.Match.matchEqs true

abbrev plus : Term Γ a → Term Γ a
| .var i => .var i
| .lam n => .lam (plus n)
| .ap (.lam _) m => plus m -- This case takes precedence over the next one.
| .ap l m => (plus l).ap (plus m)

/--
info: plus.match_1.{u_1} {Γ : Context} {a : Ty} (motive : Term Γ a → Sort u_1) (x✝ : Term Γ a)
  (h_1 : (i : Lookup Γ a) → motive (Term.var i)) (h_2 : (n : Term ( ✶ :: Γ) ✶ ) → motive n.lam)
  (h_3 : (a : Term ( ✶ :: Γ) ✶ ) → (m : Term Γ ✶ ) → motive (a.lam.ap m)) (h_4 : (l m : Term Γ ✶ ) → motive (l.ap m)) :
  motive x✝
-/
#guard_msgs(pass trace, all) in
#check plus.match_1

/--
error: failed to generate equational theorem for `plus`
  Application type mismatch: The argument
    l.ap m
  has type
    Term Γ ✶
  but is expected to have type
    Term Γ a
  in the application
    @HEq (Term Γ a) (l.ap m)
-/
#guard_msgs(pass trace, all) in
#print equations plus


/--
error: Failed to realize constant plus.match_1.eq_1:
  Application type mismatch: The argument
    l.ap m
  has type
    Term Γ ✶
  but is expected to have type
    Term Γ a
  in the application
    @HEq (Term Γ a) (l.ap m)
---
error: Unknown constant `plus.match_1.eq_1`
-/
#guard_msgs(pass trace, all) in
#print sig plus.match_1.eq_1

/--
error: Failed to realize constant plus.match_1.congr_eq_1:
  Tactic `subst` failed: did not find equation for eliminating 'heq✝'
  ⏎
  Γ : Context
  a : Ty
  x✝ : Term Γ a
  l m : Term Γ ✶
  heq✝ : x✝ ≍ l.ap m
  ⊢ (∀ (a_1 : Term ( ✶ :: Γ) ✶ ) (m_1 : Term Γ ✶ ), l.ap m ≍ a_1.lam.ap m_1 → False) →
      ∀ (a_1 : Term ( ✶ :: Γ) ✶ ) (m : Term Γ ✶ ), x✝ ≍ a_1.lam.ap m → False
---
error: Unknown constant `plus.match_1.congr_eq_1`
-/
#guard_msgs(pass trace, all) in
#print sig plus.match_1.congr_eq_1

-- Work-around: include the index in pattern matching directly

def plus' (t : Term Γ a) : Term Γ a := match a, t with
| _, .var i => .var i
| _, .lam n => .lam (plus n)
| _, .ap (.lam _) m => plus m -- This case takes precedence over the next one.
| _, .ap l m => (plus l).ap (plus m)

/--
info: equations:
@[defeq] theorem plus'.eq_1 : ∀ {Γ : Context} {a : Ty} (i : Lookup Γ a), plus' (Term.var i) = Term.var i
@[defeq] theorem plus'.eq_2 : ∀ {Γ : Context} (n : Term ( ✶ :: Γ) ✶ ), plus' n.lam = (plus n).lam
@[defeq] theorem plus'.eq_3 : ∀ {Γ : Context} (a_2 : Term ( ✶ :: Γ) ✶ ) (m : Term Γ ✶ ), plus' (a_2.lam.ap m) = plus m
theorem plus'.eq_4 : ∀ {Γ : Context} (l m : Term Γ ✶ ),
  (∀ (a : Term ( ✶ :: Γ) ✶ ), l = a.lam → False) → plus' (l.ap m) = (plus l).ap (plus m)
-/
#guard_msgs(pass trace, all) in
#print equations plus'


/--
info: private theorem plus'.match_1.congr_eq_4.{u_1} : ∀ {Γ : Context} (motive : (a : Ty) → Term Γ a → Sort u_1) (a : Ty)
  (t : Term Γ a) (h_1 : (x : Ty) → (i : Lookup Γ x) → motive x (Term.var i))
  (h_2 : (n : Term ( ✶ :: Γ) ✶ ) → motive ✶ n.lam)
  (h_3 : (a : Term ( ✶ :: Γ) ✶ ) → (m : Term Γ ✶ ) → motive ✶ (a.lam.ap m))
  (h_4 : (l m : Term Γ ✶ ) → motive ✶ (l.ap m)) (l m : Term Γ ✶ ),
  a = ✶ →
    t ≍ l.ap m →
      (∀ (a : Term ( ✶ :: Γ) ✶ ) (m_1 : Term Γ ✶ ), ✶ = ✶ → l.ap m ≍ a.lam.ap m_1 → False) →
        (match a, t with
          | x, Term.var i => h_1 x i
          | .( ✶ ), n.lam => h_2 n
          | .( ✶ ), a.lam.ap m => h_3 a m
          | .( ✶ ), l.ap m => h_4 l m) ≍
          h_4 l m
-/
#guard_msgs(pass trace, all) in
#print sig plus'.match_1.congr_eq_4
