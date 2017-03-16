namespace repro1
  structure s :=
  (obj : Type)
  (fn  : ∀ {o : obj}, true)

  #check λ t, s.fn t
end repro1

namespace repro2
  constant s : Type
  constant f : s → Type
  constant mfn : Π (t : s) (o : f t), true
  set_option pp.all true
  #check λ t, mfn t _
end repro2
