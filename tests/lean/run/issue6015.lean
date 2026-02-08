private axiom test_sorry : ∀ {α}, α

inductive Tyₛ (l : List Unit): Type
| U : Tyₛ l
open Tyₛ

inductive Varₚ (d : Unit): List Unit → Type
| vz : Varₚ d [d']
| vs : Varₚ d l → Varₚ d (Bₛ :: l)

inductive Tmₛ {l : List Unit}: Tyₛ l → Unit → Type 1
| arr   : (T : Type) → Tmₛ A d → Tmₛ A d
| param : Varₚ d l → Tmₛ A d → Tmₛ (@U l) d

def TmₛA {l : List Unit} {d : Unit} (nonIndex : Bool) {Aₛ : Tyₛ l} (t : Tmₛ Aₛ d): Type :=
match t with
  | .arr dom cd =>
    let cd := TmₛA nonIndex cd
    dom → cd
  | _ => test_sorry
termination_by structural t
