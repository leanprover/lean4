def List.insert (p : α → α → Bool) (a : α) (bs : List α) : List α :=
  match bs with
  | [] => [a]
  | b :: bs' => if p a b then a :: bs else b :: bs'.insert p a

def List.merge (p : α → α → Bool) (as bs : List α) : List α :=
  match as with
  | [] => bs
  | a :: as' => insert p a (merge p as' bs)

def List.split (as : List α) : List α × List α :=
  match as with
  | []  => ([], [])
  | [a] => ([a], [])
  | a :: b :: as =>
    let (as, bs) := split as
    (a :: as, b :: bs)

@[simp] def List.atLeast2 (as : List α) : Bool :=
  match as with
  | []      => false
  | [_]     => false
  | _::_::_ => true

theorem List.length_split_of_atLeast2 {as : List α} (h : as.atLeast2) : as.split.1.length < as.length ∧ as.split.2.length < as.length := by
  match as with
  | []  => simp at h
  | [_] => simp at h
  | [_, _] => simp (config := { decide := true }) [split]
  | [_, _, _] => simp (config := { decide := true }) [split]
  | a::b::c::d::as =>
    -- TODO: simplify using linear arith and more automation
    have : (c::d::as).atLeast2 := by simp_arith
    have ih := length_split_of_atLeast2 this
    simp_arith [split] at ih |-
    have ⟨ih₁, ih₂⟩ := ih
    exact ⟨Nat.le_trans ih₁ (by simp_arith), Nat.le_trans ih₂ (by simp_arith)⟩

def List.mergeSort (p : α → α → Bool) (as : List α) : List α :=
  if h : as.atLeast2 then
    match he:as.split with
    | (as', bs') =>
      -- TODO: simplify using more automation
      have ⟨h₁, h₂⟩ := length_split_of_atLeast2 h
      have : as'.length < as.length := by simp [he] at h₁; assumption
      have : bs'.length < as.length := by simp [he] at h₂; assumption
      merge p (mergeSort p as') (mergeSort p bs')
  else
    as
termination_by _ as => as.length
