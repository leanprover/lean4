module
def List.Disjoint (l₁ l₂ : List α) : Prop :=
  ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False


/--
error: `grind` failed
case grind
i n : Nat
f : Nat → List (List Nat)
l : List Nat
h :
  ¬List.Pairwise
      (fun x y =>
        (if x ^ i ≤ n then List.map (fun m => x :: m) (f x) else []).Disjoint
          (if y ^ i ≤ n then List.map (fun m => y :: m) (f y) else []))
      l
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬List.Pairwise
            (fun x y =>
              (if x ^ i ≤ n then List.map (fun m => x :: m) (f x) else []).Disjoint
                (if y ^ i ≤ n then List.map (fun m => y :: m) (f y) else []))
            l
  [eqc] False propositions
    [prop] List.Pairwise
          (fun x y =>
            (if x ^ i ≤ n then List.map (fun m => x :: m) (f x) else []).Disjoint
              (if y ^ i ≤ n then List.map (fun m => y :: m) (f y) else []))
          l
-/
#guard_msgs in
theorem test (f : Nat → List (List Nat)) {l : List Nat} :
    l.Pairwise
      (fun x y ↦
        (if x ^ i ≤ n then List.map (fun m ↦ x :: m) (f x) else []).Disjoint
        (if y ^ i ≤ n then List.map (fun m ↦ y :: m) (f y) else [])) := by
  grind
