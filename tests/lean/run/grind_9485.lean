module
variable (G : Type)

structure G' where p : G

@[ext, grind ext]
theorem ext_ {f g : G' G} (h : f.p = g.p) : f = g := by
  cases f
  subst h
  rfl

variable [Lean.Grind.IntModule G]

instance : Add (G' G) where add f g := ⟨f.p + g.p⟩
@[grind] theorem add_p (f g : G' G) : (f + g).p = f.p + g.p := rfl

instance : Zero (G' G) where zero := ⟨0⟩
@[grind] theorem zero_p : (0 : G' G).p = 0 := rfl

instance : Neg (G' G) where neg x := ⟨-x.p⟩
@[grind] theorem neg_p (f : G' G) : (-f).p = -(f.p) := rfl

example (f g h : G' G) :
    f + g + h = f + (g + h) := by
  grind -- should work without extra options

example (f g h : G' G) :
    f + g + h = f + (g + h) := by
  grind [Lean.Grind.AddCommMonoid.add_assoc] -- should work too

example (f g h : G' G) :
    f + g + h = f + (g + h) := by
  grind -linarith [Lean.Grind.AddCommMonoid.add_assoc] -- should work too
