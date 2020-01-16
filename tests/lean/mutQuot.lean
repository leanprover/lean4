import Init.Data.MutQuot
import Init.Lean.Util.Trace

universes u v w

namespace Examples

variables {α : Type u}

inductive Perm : List α → List α → Prop
| nil : Perm [] []
| trans {xs ys zs : List α} : Perm xs ys → Perm ys zs → Perm xs zs
| swap {x x'} {xs : List α} : Perm (x :: x' :: xs) (x' :: x :: xs)
| skip {x} {xs xs' : List α} : Perm xs xs' → Perm (x :: xs) (x :: xs')

namespace Perm

theorem refl : ∀ {xs : List α}, Perm xs xs :=
@List.rec _ (fun xs => Perm xs xs) Perm.nil
  (fun x xs IH => Perm.skip IH)

theorem of_Eq : ∀ {xs ys : List α}, xs = ys → Perm xs ys
| _, _, Eq.refl _ => Perm.refl

theorem symm : ∀ {xs ys : List α}, Perm xs ys → Perm ys xs :=
@Perm.rec _ (fun xs ys H => Perm ys xs) Perm.nil
  (fun xs ys zs H₀₁ H₁₂ H₁₀ H₂₁ => Perm.trans H₂₁ H₁₀)
  (fun x x' xs => Perm.swap)
  (fun x xs xs' H IH => Perm.skip IH)

variables {ys : List α} {x y : α}

theorem rotate : ∀ {xs : List α} {x}, Perm (x :: xs) (xs ++ [x]) :=
@List.rec _ (fun (xs : List α) => ∀ x, Perm (x :: xs) (xs ++ [x]))
  (fun x => Perm.refl)
  (fun y ys IH x => Perm.trans Perm.swap $ Perm.trans (Perm.skip $ IH _)
                               (Perm.of_Eq (List.consAppend _ _ _).symm))

-- theorem Perm_append_right {ys ys' : List α} (h : Perm ys ys') :
--   ∀ {xs : List α}, Perm (xs ++ ys) (xs ++ ys') :=
-- @List.rec _ (fun (xs : List α) => Perm (xs ++ ys) (xs ++ ys')) h
--   (fun x xs IH =>
--     show Perm _ _ from
--     @Eq.subst _ (fun zs => Perm zs (x :: xs ++ ys')) _ _ (List.consAppend x xs ys) _)

-- #check @Perm.rec
-- #check @Eq.subst
-- #check @List.rec _

-- theorem flip {x xs} : ∀ {ys : List α}, Perm (x :: xs ++ ys) (xs ++ x :: ys) :=
-- let h := @Eq.subst _ (λ ys => Perm ys (xs ++ [x])) (x :: xs) (x :: xs ++ []) (List.append_nil (x :: xs)).symm;
-- -- _
-- @List.rec _ (λ ys => Perm (x :: xs ++ ys) (xs ++ x :: ys))
--   (show Perm (x :: xs ++ []) (xs ++ [x]) from h Perm.swap )
--   _

end Perm

def MRU (α : Type u) := Mutable.Quot $ @Perm α

namespace MRU

def ofList (xs : List α) : MRU α := Mutable.Quot.mk _ xs

variables [DecidableEq α] [HasToString α]

open Lean

def findAux' (x : α) : List α → List α → PProd (Option α) (List α)
| [], xs => dbgTrace "not found" $ fun _ => ⟨none,xs.reverse⟩
| (y :: ys), zs =>
  if x = y then dbgTrace "found" $ fun _ => ⟨some y, y :: List.reverseAux zs ys⟩
           else dbgTrace "loop"  $ fun _ => findAux' ys (y :: zs)

def findAux (x : α) (xs : List α) : PProd (Option α) (List α) :=
let ⟨r,xs'⟩ := findAux' x xs [];
dbgTrace (toString xs') $ fun _ => ⟨r,xs'⟩

theorem foo (x : α) : ∀ (a b : List α), Perm a b → (findAux x a).fst = (findAux x b).fst := sorry

theorem bar' (x : α) : ∀ (a b : List α), Perm (a ++ b.reverse) ((findAux' x a b).snd) := sorry
-- | [], zs => sorry
-- | y :: ys, zs => sorry
  -- Perm.trans (Perm.of_Eq (List.consAppend y ys _)) $
  -- if h : x = y then sorry else sorry
-- Perm.trans (@Eq.subst _ (Perm _) _ _ (ifNeg h).symm (Perm.skip $ bar _ _)) Perm.refl

theorem bar (x : α) (a : List α) : Perm a ((findAux x a).snd) :=
Perm.trans (Perm.of_Eq (List.appendNil a).symm) $
show Perm (a ++ List.nil) ((findAux x a).snd)
from sorry

def find (ls : MRU α) (x : α) : Option α :=
Mutable.Quot.mutate (findAux x) (foo x) (bar x) ls

#eval
let xs : MRU _ := Mutable.Quot.mk _ [1,2,3,4,5,6,7,8,9,10];
let ys := [10,10,10,10,9,10,10,5,10,10,10,9,10];
(ys.map (fun x => dbgTrace (toString x) $ fun _ => find xs x), dbgTrace "> 9" $ fun _ => find xs 9)

end MRU

end Examples
