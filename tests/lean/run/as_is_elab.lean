open function

variable x : list nat

check x^.map (+1)

check x^.foldl (+) 0

def f (l : list (nat × nat)) : list nat :=
l^.map (λ ⟨a, b⟩, a + b)

example : [(1,2), (3,4)]^.map (uncurry (+)) = [3, 7] :=
rfl

example : [(1,2), (3,4)]^.map (λ ⟨a, b⟩, a + b) = [3, 7] :=
rfl

instance decidable_uncurry_pred{α} (p : α → α → Prop) [decidable_rel p] : decidable_pred (uncurry p) :=
λ a, by { cases a; dsimp [uncurry]; apply_instance }

example : [(1,2), (4,3), (3, 2), (0, 2), (5, 4)]^.filter (uncurry (>)) = [(4,3), (3,2), (5, 4)] :=
rfl

example : [(1,2), (4,3)]^.foldl (λ v ⟨a, b⟩, v + a) 0 = 5 :=
rfl
