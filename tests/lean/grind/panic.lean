-- A larger code example, where `issue3` leads to panic. Upon removing irrelevant lemmas `grind` immediately fails, rather than panicing.

@[grind] inductive star (R : α → α → Prop) : α → α → Prop where
  | star_refl : ∀ x : α, star R x x
  | star_step : ∀ x y z, R x y → star R y z → star R x z

set_option grind.debug true
set_option grind.warning false

def ident := String deriving BEq, Repr

inductive aexp : Type where
  | CONST (n : Int)
  | VAR (x : ident)
  | PLUS (a1 : aexp) (a2 : aexp)
  | MINUS (a1 : aexp) (s2 : aexp)

def store : Type := ident → Int

@[grind] def aeval (s : store) (a : aexp) : Int :=
  match a with
  | .CONST n => n
  | .VAR x => s x
  | .PLUS a1 a2 => aeval s a1 + aeval s a2
  | .MINUS a1 a2 => aeval s a1 - aeval s a2

#eval aeval (λ _ => 2) (.PLUS (.VAR "x") (.MINUS (.VAR "x") (.CONST 1)))

theorem aeval_xplus1 : ∀ s x, aeval s (.PLUS (.VAR x) (.CONST 1)) > aeval s (.VAR x) := by
  grind

@[grind] def free_in_aexp (x : ident) (a : aexp) : Prop :=
  match a with
  | .CONST _ => False
  | .VAR y => y = x
  | .PLUS a1 a2 | .MINUS a1 a2 => free_in_aexp x a1 ∨ free_in_aexp x a2

theorem aeval_free :
  ∀ s1 s2 a,
  (∀ x, free_in_aexp x a → s1 x = s2 x) →
  aeval s1 a = aeval s2 a := by
    intro s1 _ a _
    fun_induction aeval s1 a <;> grind

inductive bexp : Type where
  | TRUE                              -- always true
  | FALSE                             -- always false
  | EQUAL (a1: aexp) (a2: aexp)       -- whether [a1 = a2]
  | LESSEQUAL (a1: aexp) (a2: aexp)   -- whether [a1 <= a2]
  | NOT (b1: bexp)                    -- Boolean negation
  | AND (b1: bexp) (b2: bexp)       -- Boolean conjunction

def NOTEQUAL (a1 a2: aexp) : bexp := .NOT (.EQUAL a1 a2)

def GREATEREQUAL (a1 a2: aexp) : bexp := .LESSEQUAL a2 a1

def GREATER (a1 a2: aexp) : bexp := .NOT (.LESSEQUAL a1 a2)

def LESS (a1 a2: aexp) : bexp := GREATER a2 a1

@[grind] def OR (b1 b2: bexp) : bexp := .NOT (.AND (.NOT b1) (.NOT b2))

@[grind] def beval (s: store) (b: bexp) : Bool :=
  match b with
  | .TRUE => true
  | .FALSE => false
  | .EQUAL a1 a2 => aeval s a1 = aeval s a2
  | .LESSEQUAL a1 a2 => aeval s a1 <= aeval s a2
  | .NOT b1 =>  !(beval s b1)
  | .AND b1 b2 => beval s b1 && beval s b2

theorem beval_OR:
  ∀ s b1 b2, beval s (OR b1 b2) = beval s b1 ∨ beval s b2 := by grind

inductive com: Type where
  | SKIP                                     -- do nothing
  | ASSIGN (x : ident) (a: aexp)              -- assignment: [v := a]
  | SEQ (c1: com) (c2: com)                  -- sequence: [c1; c2]
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) -- conditional: [if b then c1 else c2]
  | WHILE (b: bexp) (c1: com)               --loop: [while b do c1 done]

notation:10 l:10 " ;; " r:11 => com.SEQ l r

#check .SKIP ;; .SKIP

def Euclidean_division :=
  .ASSIGN "r" (.VAR "a") ;;
  .ASSIGN "q" (.CONST 0) ;;
  .WHILE (.LESSEQUAL (.VAR "b") (.VAR "r"))
    (.ASSIGN "r" (.MINUS (.VAR "r") (.VAR "b")) ;;
     .ASSIGN "q" (.PLUS (.VAR "q") (.CONST 1)))

@[grind] def update (x: ident) (v: Int) (s: store) : store :=
  fun y => if x == y then v else s y

@[grind] inductive cexec: store → com → store → Prop where
  | cexec_skip:
      cexec s .SKIP s
  | cexec_assign:
      cexec s (.ASSIGN x a) (update x (aeval s a) s)
  | cexec_seq:
      cexec s c1 s' -> cexec s' c2 s'' ->
      cexec s (.SEQ c1 c2) s''
  | cexec_ifthenelse:
      cexec s (if beval s b then c1 else c2) s' ->
      cexec s (.IFTHENELSE b c1 c2) s'
  | cexec_while_done:
      beval s b = false ->
      cexec s (.WHILE b c) s
  | cexec_while_loop:
      beval s b = true -> cexec s c s' -> cexec s' (.WHILE b c) s'' ->
      cexec s (.WHILE b c) s''

-- Hit 2
theorem cexec_infinite_loop:
  ∀ s, ¬ ∃ s', cexec s (.WHILE .TRUE .SKIP) s' := by
  intro _ h
  apply Exists.elim h
  intro s'
  generalize heq : (com.WHILE .TRUE .SKIP) = c
  intro h₂
  induction h₂
  all_goals grind

@[grind] def cexec_bounded (fuel : Nat) (s : store) (c : com) : Option store :=
  match fuel with
  | .zero => .none
  | .succ fuel' =>
    match c with
    | .SKIP => .some s
    | .ASSIGN x a => .some (update x (aeval s a) s)
    | .SEQ c1 c2 =>
      match cexec_bounded fuel' s c1 with
      | .none => .none
      | .some s' => cexec_bounded fuel' s' c2
    | .IFTHENELSE b c1 c2 =>
      if beval s b then cexec_bounded fuel' s c1 else cexec_bounded fuel' s c2
    | .WHILE b c1 =>
      if beval s b then
        match cexec_bounded fuel' s c1 with
        | .none => .none
        | .some s' => cexec_bounded fuel' s' (.WHILE b c1)
      else
        .some s

theorem cexec_bounded_sound : ∀ fuel s c s',
    cexec_bounded fuel s c = .some s'
  → cexec s c s' := by
  intro fuel
  induction fuel
  case succ fuel ih =>
    intros _ c
    cases c
    all_goals grind
  all_goals grind

theorem cexec_bounded_complete (s s' : store) (c : com):
  cexec s c s' →
  ∃ fuel1, ∀ fuel, (fuel ≥ fuel1) → cexec_bounded fuel s c = .some s' := by
    intro h
    induction h
    case cexec_skip =>
      exists 1
      intro fuel' fgt
      induction fgt
      all_goals grind
    case cexec_assign =>
      exists 1
      intro fuel' fgt
      induction fgt
      any_goals grind
    case cexec_seq a_ih1 a_ih2 =>
      apply Exists.elim a_ih1
      intro fuel1 a_ih1
      apply Exists.elim a_ih2
      intro fuel2 a_ih2
      exists (fuel1 + fuel2)
      intro fuel' fgt
      have t : fuel' ≥ fuel1 ∧  fuel' ≥ fuel2 := by grind
      have t1 : fuel1 > 0 := by
        false_or_by_contra
        rename_i hyp
        simp at hyp
        specialize a_ih1 0 (by grind)
        grind
      have t2 : fuel2 > 0 := by
        false_or_by_contra
        rename_i hyp
        simp at hyp
        specialize a_ih2 0 (by grind)
        grind
      induction fuel'
      case zero => grind
      case succ m ih  =>
        specialize a_ih1 m (by grind)
        simp only [cexec_bounded, a_ih1]
        specialize a_ih2 m (by grind)
        exact a_ih2
    case cexec_ifthenelse s b c1 c2 s' a a_ih =>
      apply Exists.elim a_ih
      intro fuel
      intro a_ih
      exists (fuel + 1)
      intro bigger_fuel
      intro gt
      unfold cexec_bounded
      have gt' : bigger_fuel > 0 := by grind
      split
      case h_1 => grind
      case h_2 f =>
        simp
        split
        case isTrue w =>
          specialize a_ih f (by grind)
          simp [w] at a_ih
          exact a_ih
        case isFalse w =>
          specialize a_ih f (by grind)
          simp [w] at a_ih
          exact a_ih
    case cexec_while_done =>
      exists 1
      intro fuel fgt
      induction fgt
      all_goals grind
    case cexec_while_loop a_ih1 a_ih2 =>
      apply Exists.elim a_ih1
      intro fuel1 a_ih1
      apply Exists.elim a_ih2
      intro fuel2 a_ih2
      exists (fuel1 + fuel2)
      intro fuel' fgt
      have t1 : fuel1 > 0 := by
        false_or_by_contra
        rename_i hyp
        specialize a_ih1 0 (by grind)
        dsimp [cexec_bounded] at a_ih1
        contradiction
      have t2 : fuel2 > 0 := by
        false_or_by_contra
        rename_i hyp
        specialize a_ih2 0 (by grind)
        dsimp [cexec_bounded] at a_ih2
        contradiction
      induction fgt
      any_goals grind
      case refl =>
        unfold cexec_bounded
        grind

@[grind] inductive red : com × store → com × store → Prop where
  | red_assign: ∀ x a s,
      red (.ASSIGN x a, s) (.SKIP, update x (aeval s a) s)
  | red_seq_done: ∀ c s,
      red (.SEQ .SKIP c, s) (c, s)
  | red_seq_step: ∀ c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) →
      red (.SEQ c1 c, s1) (.SEQ c2 c, s2)
  | red_ifthenelse: ∀ b c1 c2 s,
      red (.IFTHENELSE b c1 c2, s) ((if beval s b then c1 else c2), s)
  | red_while_done: ∀ b c s,
      beval s b = false →
      red (.WHILE b c, s) (.SKIP, s)
  | red_while_loop: ∀ b c s,
      beval s b = true →
      red (.WHILE b c, s) (.SEQ c (.WHILE b c), s)

theorem red_progress:
  ∀ c s, c = .SKIP ∨ ∃ c', ∃ s', red (c, s) (c', s') := by
    intro c
    induction c
    any_goals grind
    case ASSIGN identifier expression =>
      intro s
      apply Or.intro_right
      exists com.SKIP
      exists (update identifier (aeval s expression) s)
      grind
    case SEQ c1 c2 c1_ih c2_ih =>
      intro s
      apply Or.intro_right
      apply Or.elim (c1_ih s)
      case h.left =>
        intro c1_eq
        rw [c1_eq]
        exists c2
        exists s
        grind
      case h.right =>
        intro h
        apply Exists.elim h
        intro c1' h
        apply Exists.elim h
        intro s' h
        exists (.SEQ c1' c2)
        exists s'
        grind
    case IFTHENELSE b c1 c2 c1_ih c2_ih =>
      intro s
      apply Or.intro_right
      have h : beval s b = true ∨ beval s b = false := by grind
      apply Or.elim h
      case h.left =>
        intro is_true
        apply Or.elim (c1_ih s)
        case left =>
          intro c1_skip
          exists .SKIP
          exists s
          grind
        case right => grind
      case h.right =>
        intro is_false
        apply Or.elim (c2_ih s)
        case left =>
          intro c2_skip
          exists .SKIP
          exists s
          grind
        case right => grind
    case WHILE b c ih =>
      intro s
      apply Or.intro_right
      have h : beval s b = true ∨ beval s b = false := by grind
      apply Or.elim h
      case left =>
        intro _
        apply Or.elim (ih s)
        any_goals grind
        case left =>
          intro _
          exists (.SEQ .SKIP  (.WHILE b c))
          exists s
          grind
      case right =>
        intros
        exists .SKIP
        exists s
        grind

@[grind] theorem red_append_cexec (c1 c2 : com) (s1 s2 : store) :
  red (c1, s1) (c2, s2) →
  ∀ s', cexec s2 c2 s' → cexec s1 c1 s' := by
    intro h s h2
    generalize heq1 : (c1, s1) = h1
    generalize heq2 : (c2, s2) = h2
    rw [heq1, heq2] at h
    induction h generalizing c1 c2 s
    case red_seq_done =>
      simp only [Prod.mk.injEq] at heq1 heq2
      rw [←heq2.1, ←heq2.2] at heq1
      rw [heq1.1, heq1.2]
      apply cexec.cexec_seq
      . apply cexec.cexec_skip
      . exact h2
    all_goals grind

theorem reds_to_cexec (s s' : store) (c : com) :
  star red (c, s) (.SKIP, s') → cexec s c s' := by
    intro h
    generalize heq1 : (c, s) = h1
    generalize heq2 : (com.SKIP, s') = h2
    rw [heq1, heq2] at h
    induction h generalizing s c s'
    case star_refl =>
      grind
    case star_step r _ a_ih =>
      apply red_append_cexec
      . rw [←heq1] at r
        exact r
      . apply a_ih
        all_goals grind
/--
The following theorem causes assertion violation in grind.
We obtain the following:
_private.Lean.Meta.Tactic.Grind.Inv.0.Lean.Meta.Grind.checkEqc Lean.Meta.Tactic.Grind.Inv:29:10: assertion violation: isSameExpr e ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv._hyg.31.0 )
-/
theorem issue3 (s s' : store) (c : com) :
  star red (c, s) (.SKIP, s') → cexec s c s' := by
    intro h
    generalize heq1 : (c, s) = h1
    generalize heq2 : (com.SKIP, s') = h2
    rw [heq1, heq2] at h
    induction h generalizing c s
    case star_refl =>
      grind
    case star_step r _ a_ih =>
      -- this is where the assertion violation happens
      grind
