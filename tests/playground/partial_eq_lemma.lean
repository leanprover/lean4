universes u

inductive Partial (α : Type u)
| val (a : α) : Partial
| bot {} : Partial

def terminates {α : Type u} (p : Partial α) : Prop := p ≠ Partial.bot

def fooAux (s : String) (c : Char) : Nat → String.Pos → Partial String.Pos
| 0            i := Partial.bot
| (Nat.succ k) i :=
  if s.atEnd i then Partial.val i
  else if s.get i == c then Partial.val i
  else fooAux k (s.next i)

theorem fooAuxEqSucc (s : String) (c : Char) : ∀ (k : Nat) (i : String.Pos), terminates (fooAux s c k i) → fooAux s c k.succ i = fooAux s c k i
| 0            i ht := absurd rfl ht
| (Nat.succ k) i ht :=
  show (fooAux s c k.succ.succ i = fooAux s c k.succ i), from
  Decidable.byCases
    (λ h : s.atEnd i,
      have h₁ : fooAux s c (k.succ.succ) i = Partial.val i, from ifPos h,
      have h₂ : fooAux s c k.succ i = Partial.val i, from ifPos h,
      Eq.trans h₁ h₂.symm)
    (λ h : ¬ s.atEnd i,
      Decidable.byCases
        (λ h' : s.get i == c,
           have h₁ : fooAux s c (k.succ.succ) i = Partial.val i, from Eq.trans (ifNeg h) (ifPos h'),
           have h₂ : fooAux s c k.succ i = Partial.val i, from Eq.trans (ifNeg h) (ifPos h'),
           Eq.trans h₁ h₂.symm)
        (λ h' : ¬ s.get i == c,
           have h₁ : fooAux s c (k.succ.succ) i   = fooAux s c k.succ (s.next i), from Eq.trans (ifNeg h) (ifNeg h'),
           have h₂ : fooAux s c k.succ i          = fooAux s c k (s.next i), from Eq.trans (ifNeg h) (ifNeg h'),
           have h₃ : fooAux s c k (s.next i) ≠ Partial.bot, from h₂ ▸ ht,
           have ih : fooAux s c k.succ (s.next i) = fooAux s c k (s.next i), from fooAuxEqSucc k _ h₃,
           Eq.trans h₁ (Eq.trans ih h₂.symm)))

theorem fooAuxTermSucc (s : String) (c : Char) (k : Nat) (i : String.Pos)
                       (h₁ : terminates (fooAux s c k.succ i)) (h₂ : ¬ (s.atEnd i)) (h₃ : ¬ (s.get i == c)) : terminates (fooAux s c k (s.next i)) :=
have (fooAux s c k.succ i) = fooAux s c k (s.next i), from Eq.trans (ifNeg h₂) (ifNeg h₃),
this ▸ h₁

constant bigNat : Nat := 1000000

def foo (s : String) (c : Char) (i : String.Pos) : Partial String.Pos :=
fooAux s c bigNat i

theorem fooEq (s : String) (c : Char) (i : String.Pos) :
     terminates (foo s c i) →
     foo s c i =  if s.atEnd i then Partial.val i
                  else if s.get i == c then Partial.val i
                  else foo s c (s.next i) :=
show terminates (fooAux s c bigNat i) → fooAux s c bigNat i =  (if s.atEnd i then Partial.val i
                                          else if s.get i == c then Partial.val i
                                          else fooAux s c bigNat (s.next i)), from
Nat.casesOn bigNat
  (λ h : fooAux s c 0 i ≠ Partial.bot, absurd rfl h)
  (λ N h,
    have h₁ : fooAux s c N.succ i = (if s.atEnd i then Partial.val i
                                     else if s.get i == c then Partial.val i
                                     else fooAux s c N (s.next i)), from rfl,
    Decidable.byCases
     (λ c₁ : s.atEnd i,
       have aux₁ : fooAux s c N.succ i = Partial.val i, from ifPos c₁,
       have aux₂ : ite (String.atEnd s i) (Partial.val i)
                       (ite (String.get s i == c) (Partial.val i) (fooAux s c (Nat.succ N) (String.next s i))) = Partial.val i, from ifPos c₁,
       Eq.trans aux₁ aux₂.symm)
     (λ c₁ : ¬ s.atEnd i,
       Decidable.byCases
         (λ c₂ : s.get i == c,
            have aux₁ : fooAux s c N.succ i = Partial.val i, from Eq.trans (ifNeg c₁) (ifPos c₂),
            have aux₂ : ite (String.atEnd s i) (Partial.val i)
                          (ite (String.get s i == c) (Partial.val i) (fooAux s c (Nat.succ N) (String.next s i))) = Partial.val i, from Eq.trans (ifNeg c₁) (ifPos c₂),
            Eq.trans aux₁ aux₂.symm)
         (λ c₂ : ¬ s.get i == c,
            have h₂ : terminates (fooAux s c N (s.next i)), from fooAuxTermSucc _ _ _ _ h c₁ c₂,
            have h₃ : fooAux s c N (s.next i) = fooAux s c N.succ (s.next i), from (fooAuxEqSucc _ _ _ _ h₂).symm,
            h₃ ▸ h₁)))
