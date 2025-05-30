-- A simple example, where using induction followed by cases and using `grind` on all goals completes the proof, but using `fun_induction` and then `grind` does not.

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

@[grind] def free_in_aexp (x : ident) (a : aexp) : Prop :=
  match a with
  | .CONST _ => False
  | .VAR y => y = x
  | .PLUS a1 a2 | .MINUS a1 a2 => free_in_aexp x a1 ∨ free_in_aexp x a2

inductive bexp : Type where
  | TRUE                              -- always true
  | FALSE                             -- always false
  | EQUAL (a1: aexp) (a2: aexp)       -- whether [a1 = a2]
  | LESSEQUAL (a1: aexp) (a2: aexp)   -- whether [a1 <= a2]
  | NOT (b1: bexp)                    -- Boolean negation
  | AND (b1: bexp) (b2: bexp)       -- Boolean conjunction

@[grind] def beval (s: store) (b: bexp) : Bool :=
  match b with
  | .TRUE => true
  | .FALSE => false
  | .EQUAL a1 a2 => aeval s a1 = aeval s a2
  | .LESSEQUAL a1 a2 => aeval s a1 <= aeval s a2
  | .NOT b1 =>  !(beval s b1)
  | .AND b1 b2 => beval s b1 && beval s b2

inductive com: Type where
  | SKIP
  | ASSIGN (x : ident) (a: aexp)
  | SEQ (c1: com) (c2: com)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com)
  | WHILE (b: bexp) (c1: com)

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

-- this works
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

-- but this doesn't
/--
error: `grind` failed
case grind.2
s' s : store
fuel' : Nat
c1 c2 : com
s'_1 : store
h : cexec_bounded fuel' s c1 = some s'_1
ih2 : cexec_bounded fuel' s c1 = some s' → cexec s c1 s'
ih1 : cexec_bounded fuel' s'_1 c2 = some s' → cexec s'_1 c2 s'
h_1 : cexec_bounded fuel' s'_1 c2 = some s'
h_2 : ¬cexec s (c1.SEQ c2) s'
s_1 : store
x : ident
a : aexp
h_3 : s'_1 = s_1
h_4 : c2 = com.ASSIGN x a
h_5 : s' = update x (aeval s_1 a) s_1
h_6 : ⋯ ≍ ⋯
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] cexec_bounded fuel' s c1 = some s'_1
    [prop] cexec_bounded fuel' s c1 = some s' → cexec s c1 s'
    [prop] cexec_bounded fuel' s'_1 c2 = some s' → cexec s'_1 c2 s'
    [prop] cexec_bounded fuel' s'_1 c2 = some s'
    [prop] ¬cexec s (c1.SEQ c2) s'
    [prop] cexec s c1 s' → cexec s' c2 s' → cexec s (c1.SEQ c2) s'
    [prop] s'_1 = s_1
    [prop] c2 = com.ASSIGN x a
    [prop] s' = update x (aeval s_1 a) s_1
    [prop] ⋯ ≍ ⋯
    [prop] cexec s_1 (com.ASSIGN x a) (update x (aeval s_1 a) s_1)
  [eqc] True propositions
    [prop] cexec_bounded fuel' s c1 = some s' → cexec s c1 s'
    [prop] cexec_bounded fuel' s'_1 c2 = some s' → cexec s'_1 c2 s'
    [prop] cexec_bounded fuel' s'_1 c2 = some s'
    [prop] cexec s'_1 c2 s'
    [prop] cexec s c1 s' → cexec s' c2 s' → cexec s (c1.SEQ c2) s'
    [prop] cexec s_1 (com.ASSIGN x a) (update x (aeval s_1 a) s_1)
  [eqc] False propositions
    [prop] cexec s (c1.SEQ c2) s'
  [eqc] Equivalence classes
    [eqc] {s', update x (aeval s_1 a) s_1}
    [eqc] {c2, com.ASSIGN x a}
    [eqc] {s'_1, s_1}
    [eqc] {cexec_bounded fuel' s'_1 c2, some s'}
    [eqc] {cexec_bounded fuel' s c1, some s'_1}
  [cases] Case analyses
    [cases] [2/6]: cexec s'_1 c2 s'
  [ematch] E-matching patterns
    [thm] cexec_bounded.eq_2: [cexec_bounded (#0 + 1) #1 `[com.SKIP]]
    [thm] cexec_bounded.eq_1: [cexec_bounded `[0] #1 #0]
    [thm] cexec.cexec_skip: [cexec #0 `[com.SKIP] #0]
    [thm] cexec.cexec_seq: [cexec #6 (com.SEQ #5 #3) #2, cexec #6 #5 #4]
    [thm] cexec_bounded.eq_4: [cexec_bounded (#2 + 1) #3 (com.SEQ #1 #0)]
    [thm] cexec_bounded.eq_3: [cexec_bounded (#2 + 1) #3 (com.ASSIGN #1 #0)]
    [thm] update.eq_1: [update #3 #2 #1 #0]
    [thm] cexec.cexec_assign: [com.ASSIGN #1 #0, aeval #2 #0]
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] cexec.cexec_assign ↦ 1
    [thm] cexec.cexec_seq ↦ 1
---
error: `grind` failed
case grind.6.5.2
s' s : store
fuel' : Nat
b : bexp
c1 : com
h : beval s b = true
s'_1 : store
h_1 : cexec_bounded fuel' s c1 = some s'_1
ih2 : cexec_bounded fuel' s c1 = some s' → cexec s c1 s'
ih1 : cexec_bounded fuel' s'_1 (com.WHILE b c1) = some s' → cexec s'_1 (com.WHILE b c1) s'
h_2 : cexec_bounded fuel' s'_1 (com.WHILE b c1) = some s'
h_3 : ¬cexec s (com.WHILE b c1) s'
s_1 : store
b_1 : bexp
c : com
s'_2 s'' : store
h_4 : beval s_1 b_1 = true
h_5 : cexec s_1 c s'_2
h_6 : cexec s'_2 (com.WHILE b_1 c) s''
h_7 : s'_1 = s_1
h_9 : b = b_1
h_10 : c1 = c
h_11 : s' = s''
h_12 : ⋯ ≍ ⋯
s_2 : store
b_2 : bexp
c_1 : com
h_13 : beval s_2 b_2 = false
h_14 : s'_2 = s_2
h_16 : b_1 = b_2
h_17 : c = c_1
h_18 : s'' = s_2
h_19 : ⋯ ≍ ⋯
s_3 : store
x : ident
a : aexp
h_20 : s_1 = s_3
h_21 : c = com.ASSIGN x a
h_22 : s'_2 = update x (aeval s_3 a) s_3
h_23 : ⋯ ≍ ⋯
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] beval s b = true
    [prop] cexec_bounded fuel' s c1 = some s'_1
    [prop] cexec_bounded fuel' s c1 = some s' → cexec s c1 s'
    [prop] cexec_bounded fuel' s'_1 (com.WHILE b c1) = some s' → cexec s'_1 (com.WHILE b c1) s'
    [prop] cexec_bounded fuel' s'_1 (com.WHILE b c1) = some s'
    [prop] ¬cexec s (com.WHILE b c1) s'
    [prop] beval s b = true → cexec s c1 s' → cexec s' (com.WHILE b c1) s' → cexec s (com.WHILE b c1) s'
    [prop] beval s' b = false → cexec s' (com.WHILE b c1) s'
    [prop] beval s_1 b_1 = true
    [prop] cexec s_1 c s'_2
    [prop] cexec s'_2 (com.WHILE b_1 c) s''
    [prop] s'_1 = s_1
    [prop] b = b_1
    [prop] c1 = c
    [prop] s' = s''
    [prop] ⋯ ≍ ⋯
    [prop] beval s' b_1 = false → cexec s' (com.WHILE b_1 c) s'
    [prop] beval s b_1 = true → cexec s c s' → cexec s' (com.WHILE b_1 c) s' → cexec s (com.WHILE b_1 c) s'
    [prop] beval s'_1 b_1 = true → cexec s'_1 c s'_2 → cexec s'_2 (com.WHILE b_1 c) s' → cexec s'_1 (com.WHILE b_1 c) s'
    [prop] beval s_1 b_1 = true → cexec s_1 c s'_2 → cexec s'_2 (com.WHILE b_1 c) s' → cexec s_1 (com.WHILE b_1 c) s'
    [prop] beval s b_1 = true → cexec s c1 s' → cexec s' (com.WHILE b_1 c1) s' → cexec s (com.WHILE b_1 c1) s'
    [prop] beval s_2 b_2 = false
    [prop] s'_2 = s_2
    [prop] b_1 = b_2
    [prop] c = c_1
    [prop] s'' = s_2
    [prop] ⋯ ≍ ⋯
    [prop] s_1 = s_3
    [prop] c = com.ASSIGN x a
    [prop] s'_2 = update x (aeval s_3 a) s_3
    [prop] ⋯ ≍ ⋯
    [prop] cexec s_3 (com.ASSIGN x a) (update x (aeval s_3 a) s_3)
  [eqc] True propositions
    [prop] cexec_bounded fuel' s c1 = some s' → cexec s c1 s'
    [prop] cexec_bounded fuel' s'_1 (com.WHILE b c1) = some s' → cexec s'_1 (com.WHILE b c1) s'
    [prop] cexec_bounded fuel' s'_1 (com.WHILE b c1) = some s'
    [prop] cexec s'_1 (com.WHILE b c1) s'
    [prop] beval s b = true → cexec s c1 s' → cexec s' (com.WHILE b c1) s' → cexec s (com.WHILE b c1) s'
    [prop] beval s b = true
    [prop] cexec s c1 s' → cexec s' (com.WHILE b c1) s' → cexec s (com.WHILE b c1) s'
    [prop] beval s' b = false → cexec s' (com.WHILE b c1) s'
    [prop] cexec s_1 c s'_2
    [prop] cexec s'_2 (com.WHILE b_1 c) s''
    [prop] cexec s_1 (com.WHILE b_1 c) s''
    [prop] beval s' b_1 = false → cexec s' (com.WHILE b_1 c) s'
    [prop] beval s b_1 = true → cexec s c s' → cexec s' (com.WHILE b_1 c) s' → cexec s (com.WHILE b_1 c) s'
    [prop] cexec s c s' → cexec s' (com.WHILE b_1 c) s' → cexec s (com.WHILE b_1 c) s'
    [prop] beval s b_1 = true
    [prop] beval s'_1 b_1 = true → cexec s'_1 c s'_2 → cexec s'_2 (com.WHILE b_1 c) s' → cexec s'_1 (com.WHILE b_1 c) s'
    [prop] cexec s'_1 (com.WHILE b_1 c) s'
    [prop] cexec s'_2 (com.WHILE b_1 c) s' → cexec s'_1 (com.WHILE b_1 c) s'
    [prop] cexec s'_1 c s'_2 → cexec s'_2 (com.WHILE b_1 c) s' → cexec s'_1 (com.WHILE b_1 c) s'
    [prop] cexec s'_2 (com.WHILE b_1 c) s'
    [prop] cexec s'_1 c s'_2
    [prop] beval s'_1 b_1 = true
    [prop] beval s_1 b_1 = true → cexec s_1 c s'_2 → cexec s'_2 (com.WHILE b_1 c) s' → cexec s_1 (com.WHILE b_1 c) s'
    [prop] cexec s'_2 (com.WHILE b_1 c) s' → cexec s_1 (com.WHILE b_1 c) s'
    [prop] cexec s_1 c s'_2 → cexec s'_2 (com.WHILE b_1 c) s' → cexec s_1 (com.WHILE b_1 c) s'
    [prop] cexec s_1 (com.WHILE b_1 c) s'
    [prop] beval s_1 b_1 = true
    [prop] beval s b_1 = true → cexec s c1 s' → cexec s' (com.WHILE b_1 c1) s' → cexec s (com.WHILE b_1 c1) s'
    [prop] cexec s c1 s' → cexec s' (com.WHILE b_1 c1) s' → cexec s (com.WHILE b_1 c1) s'
    [prop] cexec s' (com.WHILE b c1) s'
    [prop] cexec s' (com.WHILE b_1 c) s'
    [prop] cexec s' (com.WHILE b_1 c1) s'
    [prop] beval s' b = false
    [prop] beval s' b_1 = false
    [prop] cexec s_2 (com.WHILE b_2 c_1) s_2
    [prop] cexec s_3 (com.ASSIGN x a) (update x (aeval s_3 a) s_3)
  [eqc] False propositions
    [prop] cexec s (com.WHILE b c1) s'
    [prop] cexec s (com.WHILE b_1 c) s'
    [prop] cexec s (com.WHILE b_1 c1) s'
    [prop] cexec s' (com.WHILE b c1) s' → cexec s (com.WHILE b c1) s'
    [prop] cexec s' (com.WHILE b_1 c) s' → cexec s (com.WHILE b_1 c) s'
    [prop] cexec s' (com.WHILE b_1 c1) s' → cexec s (com.WHILE b_1 c1) s'
    [prop] cexec s c1 s'
    [prop] cexec s c s'
    [prop] cexec_bounded fuel' s c1 = some s'
  [eqc] Equivalence classes
    [eqc] {c, c1, c_1, com.ASSIGN x a}
    [eqc] {s'_2, s'', s', update x (aeval s_3 a) s_3, s_2}
    [eqc] {com.WHILE b c1, com.WHILE b_1 c1, com.WHILE b_2 c_1, com.WHILE b_1 c}
    [eqc] {b, b_2, b_1}
    [eqc] {s'_1, s_3, s_1}
    [eqc] {cexec_bounded fuel' s'_1 (com.WHILE b c1), some s'}
    [eqc] {cexec_bounded fuel' s c1, some s'_1}
    [eqc] {beval s_2 b_2, beval s' b, beval s' b_1, false}
    [eqc] {beval s b, beval s_1 b_1, beval s b_1, beval s'_1 b_1, true}
  [cases] Case analyses
    [cases] [6/6]: cexec s'_1 (com.WHILE b c1) s'
    [cases] [5/6]: cexec s'_2 (com.WHILE b_1 c) s''
    [cases] [2/6]: cexec s_1 c s'_2
  [ematch] E-matching patterns
    [thm] beval.eq_2: [beval #0 `[bexp.FALSE]]
    [thm] beval.eq_1: [beval #0 `[bexp.TRUE]]
    [thm] cexec_bounded.eq_2: [cexec_bounded (#0 + 1) #1 `[com.SKIP]]
    [thm] cexec_bounded.eq_1: [cexec_bounded `[0] #1 #0]
    [thm] cexec.cexec_skip: [cexec #0 `[com.SKIP] #0]
    [thm] cexec.cexec_while_done: [cexec #3 (com.WHILE #2 #1) #3]
    [thm] cexec.cexec_while_loop: [cexec #7 (com.WHILE #6 #5) #3, cexec #7 #5 #4]
    [thm] cexec_bounded.eq_6: [cexec_bounded (#2 + 1) #3 (com.WHILE #1 #0)]
    [thm] cexec_bounded.eq_3: [cexec_bounded (#2 + 1) #3 (com.ASSIGN #1 #0)]
    [thm] update.eq_1: [update #3 #2 #1 #0]
    [thm] cexec.cexec_assign: [com.ASSIGN #1 #0, aeval #2 #0]
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] cexec.cexec_while_loop ↦ 5
    [thm] cexec.cexec_while_done ↦ 2
    [thm] cexec.cexec_assign ↦ 1
-/
#guard_msgs in
theorem issue4 : ∀ fuel s c s',
    cexec_bounded fuel s c = .some s'
  → cexec s c s' := by
  intros
  fun_induction cexec_bounded
  all_goals grind
