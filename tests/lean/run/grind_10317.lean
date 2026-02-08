axiom Finset (α : Type u) : Type u

@[instance]
axiom memFinset : Membership α (Finset α)

axiom finsetProd {ι : Type u} {M : Type v} (s : Finset ι) (f : ι → M) : M

axiom toFinset (l : List α) : Finset α

axiom finsetProdCongr {ι : Type u} {M : Type v} {s₁ s₂ : Finset ι}
  {f g : ι → M} (hs : s₁ = s₂) (hf : ∀ x ∈ s₂, f x = g x) : finsetProd s₁ f = finsetProd s₂ g

example [Mul M] [Std.Associative (HMul.hMul (α := M))] [Pow M Nat] [DecidableEq ι]
    (f : ι → M) (a : ι) (s : List ι) (has : a ∉ toFinset s) :
    f a * finsetProd (toFinset s) (fun m => f m ^ List.count m s) = f a * finsetProd (toFinset s) (fun x => f x ^ List.count x (a :: s)) := by
  grind [finsetProdCongr]

example [Mul M] [Std.Associative (HMul.hMul (α := M))] [Pow M Nat] [DecidableEq ι]
    (f : ι → M) (a : ι) (s : List ι) (has : a ∉ toFinset s) :
    f a * finsetProd (toFinset s) (fun m => f m ^ List.count m s) = f a * finsetProd (toFinset s) (fun x => f x ^ List.count x (a :: s)) := by
  grind -ac [finsetProdCongr]
