namespace Stream

variable [Stream ρ τ] (s : ρ)

def take (s : ρ) : Nat → List τ × ρ
| 0 => ([], s)
| n+1 =>
  match next? s with
  | none => ([], s)
  | some (x,rest) =>
    let (L,rest) := take rest n
    (x::L, rest)

def isEmpty : Bool :=
  Option.isNone (next? s)

def lengthBoundedBy (n : Nat) : Prop :=
  isEmpty (take s n).2

def hasNext : ρ → ρ → Prop
  := λ s1 s2 => ∃ x, next? s1 = some ⟨x,s2⟩

def isFinite : Prop :=
  ∃ n, lengthBoundedBy s n

instance hasNextWF : WellFoundedRelation {s : ρ // isFinite s} where
  rel := λ s1 s2 => hasNext s2.val s1.val
  wf := ⟨λ ⟨s,h⟩ => ⟨⟨s,h⟩, by
    simp only [Subtype.forall]
    cases h; case intro w h =>
    induction w generalizing s
    case zero =>
      intro s' h' h_next
      simp [hasNext] at h_next
      cases h_next; case intro x h_next =>
      simp [lengthBoundedBy, isEmpty, Option.isNone, take, h_next] at h
    case succ n ih =>
      intro s' h' h_next
      simp [hasNext] at h_next
      cases h_next; case intro x h_next =>
      simp [lengthBoundedBy, take, h_next] at h
      have := ih s' h
      exact Acc.intro (⟨s',h'⟩ : {s : ρ // isFinite s}) (by simpa only [Subtype.forall])
  ⟩⟩

def mwe [Stream ρ τ] (acc : α) : {l : ρ // isFinite l} → α
  | ⟨l,h⟩ =>
    match h:next? l with
    | none => acc
    | some (x,xs) =>
      have h_next : hasNext l xs := by exists x
      mwe acc ⟨xs, by sorry⟩
  termination_by l => l

end Stream
