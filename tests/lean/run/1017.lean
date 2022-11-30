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

def LengthBoundedBy (n : Nat) : Prop :=
  isEmpty (take s n).2

def HasNext : ρ → ρ → Prop
  := λ s1 s2 => ∃ x, next? s1 = some ⟨x,s2⟩

def IsFinite : Prop :=
  ∃ n, LengthBoundedBy s n

instance hasNextWF : WellFoundedRelation {s : ρ // IsFinite s} where
  Rel := λ s1 s2 => HasNext s2.val s1.val
  wf := ⟨λ ⟨s,h⟩ => ⟨⟨s,h⟩, by
    simp
    cases h; case intro w h =>
    induction w generalizing s
    case zero =>
      intro ⟨s',h'⟩ h_next
      simp [HasNext] at h_next
      cases h_next; case intro x h_next =>
      simp [LengthBoundedBy, isEmpty, Option.isNone, take, h_next] at h
    case succ n ih =>
      intro ⟨s',h'⟩ h_next
      simp [HasNext] at h_next
      cases h_next; case intro x h_next =>
      simp [LengthBoundedBy, take, h_next] at h
      have := ih s' h
      exact Acc.intro (⟨s',h'⟩ : {s : ρ // IsFinite s}) this
  ⟩⟩

def mwe [Stream ρ τ] (acc : α) : {l : ρ // IsFinite l} → α
  | ⟨l,h⟩ =>
    match h:next? l with
    | none => acc
    | some (x,xs) =>
      have h_next : HasNext l xs := by exists x
      mwe acc ⟨xs, by sorry⟩
  termination_by _ l => l

end Stream
