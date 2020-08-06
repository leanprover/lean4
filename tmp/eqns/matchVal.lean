universes v
/-
matcher for the following patterns
```
| "hello" => _
| "world" => _
| a       => _
``` -/
def matchString (C : String → Sort v) (s : String)
    (h₁ : Unit → C "hello")
    (h₂ : Unit → C "world")
    (h₃ : ∀ s,   C s)
    : C s :=
dite (s = "hello")
  (fun h => @Eq.ndrec _ _ (fun x => C x) (h₁ ()) _ h.symm)
  (fun _ => dite (s = "world")
    (fun h => @Eq.ndrec _ _ (fun x => C x) (h₂ ()) _ h.symm)
    (fun _ => h₃ s))

theorem matchString.Eq1 (C : String → Sort v)
    (h₁ : Unit → C "hello")
    (h₂ : Unit → C "world")
    (h₃ : ∀ s,   C s)
    : matchString C "hello" h₁ h₂ h₃ = h₁ () :=
difPos rfl

axiom neg1 : "world" ≠ "hello"

theorem matchString.Eq2 (C : String → Sort v)
    (h₁ : Unit → C "hello")
    (h₂ : Unit → C "world")
    (h₃ : ∀ s,   C s)
    : matchString C "world" h₁ h₂ h₃ = h₂ () :=
have aux₁ : matchString C "world" h₁ h₂ h₃ = if h : "world" = "world" then @Eq.rec _ _ (fun x _ => C x) (h₂ ()) _ h.symm else h₃ "world" from difNeg neg1;
have aux₂ : (if h : "world" = "world" then @Eq.rec _ _ (fun x _ => C x) (h₂ ()) _ h.symm else h₃ "world" : C "world") = h₂ () from difPos rfl;
Eq.trans aux₁ aux₂

theorem matchString.Eq3 (C : String → Sort v)
    (h₁ : Unit → C "hello")
    (h₂ : Unit → C "world")
    (h₃ : ∀ s,   C s)
    (s : String) (n₁ : s ≠ "hello") (n₂ : s ≠ "world")
    : matchString C s h₁ h₂ h₃ = h₃ s :=
have aux₁ : matchString C s h₁ h₂ h₃ = if h : s = "world" then @Eq.rec _ _ (fun x _ => C x) (h₂ ()) _ h.symm else h₃ s from difNeg n₁;
have aux₂ : (if h : s = "world" then @Eq.rec _ _ (fun x _ => C x) (h₂ ()) _ h.symm else h₃ s : C s) = h₃ s from difNeg n₂;
Eq.trans aux₁ aux₂
