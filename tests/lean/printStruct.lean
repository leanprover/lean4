/-!
  Test #print command for structures and classes
-/

/- Structure -/
#print Prod

/- Class -/
#print Inhabited

/- Structure with private field -/
#print Thunk

/- Extended class -/
#print Alternative

/- Multiply extended class -/
#print Applicative

/- Structure-like inductive -/
inductive Fake (α : Type _) where
  | mk : (x : α) → Fake α
#print Fake
