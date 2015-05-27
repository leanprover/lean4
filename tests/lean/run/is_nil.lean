import logic
open tactic

inductive list (A : Type) : Type :=
| nil {} : list A
| cons   : A → list A → list A
namespace list end list open list
open eq

definition is_nil {A : Type} (l : list A) : Prop
:= list.rec true (fun h t r, false) l

theorem is_nil_nil (A : Type) : is_nil (@nil A)
:= of_eq_true (refl true)

theorem cons_ne_nil {A : Type} (a : A) (l : list A) : ¬ cons a l = nil
:= not.intro (assume H : cons a l = nil,
     absurd
       (calc true = is_nil (@nil A)   : refl _
              ... = is_nil (cons a l) : { symm H }
              ... = false             : refl _)
       true_ne_false)

theorem T : is_nil (@nil Prop)
:= by apply is_nil_nil
