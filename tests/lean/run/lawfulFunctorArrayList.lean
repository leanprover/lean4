import Lean
open Lean Elab Term

-- Helper lemmas for proving seq_assoc
section SeqAssocHelpers

/-- Our seq operation is equivalent to flatMap with the appropriate function -/
@[simp]
theorem Array.seq_eq_flatMap {α β : Type u} (fns : Array (α → β)) (xs : Array α) :
    fns.foldl (fun acc f => acc ++ xs.map f) #[] = fns.flatMap (fun f => xs.map f) := by
  rw [Array.flatMap.eq_1]
  rfl

end SeqAssocHelpers

section LocalInstances

local instance : Applicative List where
  pure := List.singleton
  seq {α β} (fns : List (α → β)) (fn : Unit → List α) : List β :=
    fns.foldl (fun acc f => acc ++ (fn ()).map f) []

local instance : Applicative Array where
  pure := Array.singleton
  seq {α β} (fns : Array (α → β)) (fn : Unit → Array α) : Array β :=
    fns.foldl (fun acc f => acc ++ (fn ()).map f) #[]

local instance: Monad Array where
  bind xs f := xs.flatMap f

local instance : Monad List where
  bind xs f := xs.flatMap f

local instance: LawfulApplicative Array where
  seqLeft_eq := by intros; simp only [SeqLeft.seqLeft, Seq.seq]
  seqRight_eq := by intros; simp only [SeqRight.seqRight, Seq.seq]
  seq_pure := by intros; simp only [Seq.seq, pure, Array.singleton_def, List.map_toArray,
    List.map_cons, List.map_nil, Array.append_singleton, Array.foldl_push_eq_append,
    Array.empty_append, Functor.map]
  pure_seq := by intros; simp [pure,Seq.seq,Functor.map]
  map_pure := by intros; simp [Functor.map,pure]
  seq_assoc := by
    intros
    simp only [Seq.seq, Functor.map,Array.seq_eq_flatMap,Array.flatMap_map,Array.flatMap_assoc]
    simp [Array.map_flatMap]


local instance: LawfulApplicative List where
  seqLeft_eq := by intros; simp [SeqLeft.seqLeft, Seq.seq]
  seqRight_eq := by intros; simp [SeqRight.seqRight, Seq.seq]
  seq_pure := by
    intros α β g x
    simp  [Seq.seq, pure, Functor.map,List.singleton]
    -- We need to prove: g <*> pure x = (fun h => h x) <$> g
    -- Which means: g.foldl (fun acc f => acc ++ [x].map f) [] = g.map (fun h => h x)
    induction g with
    | nil => simp
    | cons f fs ih =>
      simp [ih]
  pure_seq := by
    intros
    simp [pure, Seq.seq, Functor.map,List.singleton,List.foldl_cons,List.foldl_nil,Functor.map]

  map_pure := by
    intros
    simp only [Functor.map, pure, List.singleton,List.map_cons,List.map_nil]
  seq_assoc := by
    intros
    simp only [Seq.seq, Functor.map]

    -- Key lemma: our seq operation is equivalent to flatMap
    have foldl_eq_flatMap : ∀ {α β : Type u_1} (fs : List (α → β)) (xs : List α),
      fs.foldl (fun acc f => acc ++ xs.map f) [] = fs.flatMap (fun f => xs.map f) := by
      intros _ _ fs _
      induction fs with
      | nil => simp
      | cons f fs ih =>
        simp  [List.foldl_cons, List.flatMap]

    simp [foldl_eq_flatMap]
    simp [List.map_eq_flatMap,List.flatMap_assoc]

local instance : LawfulMonad Array where
  bind_pure_comp := by intros; simp [pure,Functor.map,bind]; exact Eq.symm Array.map_eq_flatMap
  pure_bind := by intros; simp [bind, pure]
  bind_assoc := by intros; simp [bind]; exact Array.flatMap_assoc
  pure_seq := by intros; simp [pure, Seq.seq, Functor.map]
  bind_map := by intros; rfl
  seqLeft_eq := by simp [LawfulApplicative.seqLeft_eq]
  seqRight_eq := by simp [LawfulApplicative.seqRight_eq]


local instance : LawfulMonad List where
  bind_pure_comp := by intros; simp [pure, Functor.map,bind]; exact Eq.symm List.map_eq_flatMap
  pure_bind := by intros; simp [bind, pure, List.singleton]
  bind_assoc := by intros; simp [bind, List.flatMap_assoc]
  pure_seq := by
    intros
    simp [pure, Seq.seq, Functor.map, List.singleton]

  bind_map := by intros; simp [Seq.seq]; rfl
  seqLeft_eq := by simp [LawfulApplicative.seqLeft_eq]
  seqRight_eq := by simp [LawfulApplicative.seqRight_eq]

-- Test that the instances work
example : LawfulFunctor List := inferInstance
example : LawfulFunctor Array := inferInstance
example : LawfulFunctor (Vector · 5) := inferInstance

-- Test the local instances
example : LawfulApplicative Array := inferInstance
example : LawfulApplicative List := inferInstance
example : LawfulMonad Array := inferInstance
example : LawfulMonad List := inferInstance

end LocalInstances