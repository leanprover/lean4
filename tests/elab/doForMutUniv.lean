import Std.Data.HashSet

/-!
Test that `for` loops with `mut` variables whose type spans multiple implicit universes
do not get stuck on `max (?u+1) (?v+1) =?= ?u+1`. This is solved by instead solving the decremented
constraint `max ?u ?v =?= ?u` eagerly, which solves by `solveSelfMax`.
-/

-- Works with explicit universe variables
example {α : Type (max u v)} {β : Type v} [Inhabited α] [Inhabited β] (as : Array α) : Array α := Id.run do
  let mut m : α × β := default
  for a in as do
    m := (a, m.2)
  return #[m.1]

-- Works with legacy do elaborator
set_option backward.do.legacy true in
example [Inhabited α] [Inhabited β] (as : Array α) : Array α := Id.run do
  let mut m : α × β := default
  for a in as do
    m := (a, m.2)
  return #[m.1]

-- Also works with implicit universe variables (the actual regression case)
example [Inhabited α] [Inhabited β] (as : Array α) : Array α := Id.run do
  let mut m : α × β := default
  for a in as do
    m := (a, m.2)
  return #[m.1]

-- Closer to the real world reproducer from aesop's UnionFind data structure:
def cluster [BEq α] [Hashable α] [BEq β] [Hashable β] (f : α → Array β)
    (as : Array α) : Array (Array α) := Id.run do
  let mut clusters := Std.HashSet.ofArray as
  let mut aOccs : Std.HashMap β (Array α) := {}
  for a in as do
    for b in f a do
      match aOccs[b]? with
      | some as' =>
        for a' in as' do
          clusters := clusters.insert a'
        aOccs := aOccs.insert b (as'.push a)
      | none =>
        aOccs := aOccs.insert b #[a]
  return #[clusters.toArray]
