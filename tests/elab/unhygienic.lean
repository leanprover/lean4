set_option hygiene false in
notation "X" => x

def x : Bool := true
#check X
#check fun (x : Nat) => X

notation "Y" => fun (x : Nat) => X
#check fun (x : Int) => Y


variable (Com State : Type)
variable (skip : Com)

set_option hygiene false in
notation:60 cs " ⇓ " σ' " : " steps:60 => Bigstep cs σ' steps

inductive Bigstep : Com × State → State → Nat → Prop where
  | skip {σ} : ⟨skip, σ⟩ ⇓ σ : 1
