inductive Foo where
  | text : String → Foo
  | element : List Foo → Foo

namespace Foo

mutual
  @[simp] def textLengthList : List Foo → Nat
    | [] => 0
    | f::fs => textLength f + textLengthList fs

  @[simp] def textLength : Foo → Nat
    | text s => s.length
    | element children => textLengthList children
end

def concat (f₁ f₂ : Foo) : Foo :=
  Foo.element [f₁, f₂]

theorem textLength_concat (f₁ f₂ : Foo) : textLength (concat f₁ f₂) = textLength f₁ + textLength f₂ := by
  simp [concat]

mutual
  @[simp] def flatList : List Foo → List String
    | [] => []
    | f :: fs => flat f ++ flatList fs

  @[simp] def flat : Foo → List String
    | text s => [s]
    | element children => flatList children
end

def listStringLen (xs : List String) : Nat :=
  xs.foldl (init := 0) fun sum s => sum + s.length

attribute [simp] List.foldl

theorem foldl_init (s : Nat) (xs : List String) :  (xs.foldl (init := s) fun sum s => sum + s.length) = s + (xs.foldl (init := 0) fun sum s => sum + s.length) := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp_arith [ih x.length, ih (s + x.length)]

theorem listStringLen_append (xs ys : List String) : listStringLen (xs ++ ys) = listStringLen xs + listStringLen ys := by
  simp [listStringLen]
  induction xs with
  | nil => simp
  | cons x xs ih => simp_arith [foldl_init x.length, ih]

mutual
  theorem listStringLen_flat (f : Foo) : listStringLen (flat f) = textLength f := by
    match f with
    | text s => simp [listStringLen]
    | element cs => simp [listStringLen_flatList cs]

  theorem listStringLen_flatList (cs : List Foo) : listStringLen (flatList cs) = textLengthList cs := by
    match cs with
    | [] => simp [listStringLen]
    | f :: fs => simp [listStringLen_append, listStringLen_flatList fs, listStringLen_flat f]
end

end Foo
