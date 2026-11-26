import Std.WP
import Std.Tactic.Do
open Std.WP Lean.Order

/-! `vcgen +jp` over assertions `Prop ×' Prop`, whose order is no lattice projection. `+jp` synthesizes
the lattice, so the program yields one VC instead of one per path. -/

set_option sym.debug true
set_option experimental.vcgen true

def M (α : Type) := Id α
instance : Monad M := inferInstanceAs (Monad Id)

instance {α : Type} : WP (M α) α (Prop ×' Prop) EStack⟨⟩ where
  trans x := PredTrans.mk (fun post _epost => post x) fun hpost _ => hpost x

instance : MonadicWP M (Prop ×' Prop) EStack⟨⟩ := ⟨fun _ => inferInstance⟩

theorem M.wp_apply_eq {α : Type} (x : M α) (post : α → Prop ×' Prop) (eposts : EStack⟨⟩) :
    wp x post eposts = post x := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

instance : MonadicWP.IsDistrib M where
  trans_pure x := PredTrans.ext fun _ _ => by
    simp only [WP.trans_apply_eq, PredTrans.apply_Pure_pure, M.wp_apply_eq]; rfl
  trans_bind _ _ := PredTrans.ext fun _ _ => by
    simp only [WP.trans_apply_eq, PredTrans.apply_Bind_bind, M.wp_apply_eq]; rfl

def ifs (n : Nat) : M Nat := do
  let mut x := 0
  if n > 0 then x := x + 1 else x := x + 2
  if n > 1 then x := x + 3 else x := x + 4
  if n > 2 then x := x + 1 else x := x + 2
  return x

example (n : Nat) : ⦃ ⊤ ⦄ ifs n ⦃ fun _ => ⟨True, True⟩ ⦄ := by
  vcgen +jp [ifs]
  case vc1 => exact ⟨fun _ => trivial, fun _ => trivial⟩
  done
