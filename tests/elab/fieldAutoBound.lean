namespace Test

open Function

class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  map_const : (Functor.mapConst : α → f β → f α) = Functor.map ∘ const β
  id_map (x : f α) : id <$> x = x
  comp_map (g : α → β) (h : β → γ) (x : f α) : (h ∘ g) <$> x = h <$> g <$> x

end Test
