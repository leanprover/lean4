open is_trunc
namespace hide
inductive trunc (n : trunc_index) (A : Type) : Type :=
tr {} : A → trunc n A

axiom is_trunc_tr (n : trunc_index) (A : Type) : is_trunc n (trunc n A)

attribute is_trunc_tr [instance]

namespace trunc
  definition trunc_rec_on {n : trunc_index} {A : Type} {P : trunc n A → Type} (aa : trunc n A)
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) : P aa :=
  trunc.rec_on aa H

  definition trunc_functor1 {X Y : Type} (n : trunc_index) (f : X → Y) : trunc n X → trunc n Y :=
  begin
    intro xx,
    apply (trunc_rec_on xx),
    intro x,
    exact (tr (f x))
  end

  definition trunc_functor2 {X Y : Type} (n : trunc_index) (f : X → Y) : trunc n X → trunc n Y :=
  by intro xx; exact (trunc_rec_on xx (λx, (tr (f x))))

  definition trunc_functor3 {X Y : Type} (n : trunc_index) (f : X → Y) : trunc n X → trunc n Y :=
  by exact (λxx, trunc_rec_on xx (λx, tr (f x)))

  definition trunc_functor4 {X Y : Type} (n : trunc_index) (f : X → Y) : trunc n X → trunc n Y :=
  by intro xx; apply (trunc_rec_on xx); intro x; exact (tr (f x))

end trunc
end hide
