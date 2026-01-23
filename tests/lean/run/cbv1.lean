import Lean

def myFun (n : Nat) : Nat := match n with
| .zero => .zero
| .succ n => (myFun n).succ
termination_by n

set_option maxRecDepth 2000000
set_option trace.Meta.Tactic true
theorem test1 : myFun 3 = 3 := by
  conv =>
    lhs
    cbv



#print test1

abbrev ident := Nat

/-
  The abstract syntax: an arithmetic expression is either...
-/
inductive aexp : Type where
  | CONST (n : Int)               -- a constant, or
  | VAR (x : ident)               -- a variable, or
  | PLUS (a1 : aexp) (a2 : aexp)  -- a sum of two expressions, or
  | MINUS (a1 : aexp) (s2 : aexp) -- a difference of two expressions

/-
  The denotational semantics: an evaluation function that computes the integer value denoted by an expression.  It is parameterized by a store [s] that associates values to variables.
-/

def store : Type := ident → Int

@[grind] def aeval (s : store) (a : aexp) : Int :=
  match a with
  | .CONST n => n
  | .VAR x => s x
  | .PLUS a1 a2 => aeval s a1 + aeval s a2
  | .MINUS a1 a2 => aeval s a1 - aeval s a2


example : aeval (λ _ => 2) (.PLUS (.VAR 1) (.MINUS (.VAR 1) (.CONST 1))) = 3 := by
  conv =>
    lhs
    cbv


/-
  We can prove properties of a given expression.
-/
theorem aeval_xplus1 : ∀ s x, aeval s (.PLUS (.VAR x) (.CONST 1)) > aeval s (.VAR x) := by
  grind

/-
  Finally, we can prove "meta-properties" that hold for all expressions.
  For example: the value of an expression depends only on the values of its free variables.

  Free variables are defined by this recursive predicate:
-/
@[grind] def free_in_aexp (x : ident) (a : aexp) : Prop :=
  match a with
  | .CONST _ => False
  | .VAR y => y = x
  | .PLUS a1 a2
  | .MINUS a1 a2 => free_in_aexp x a1 ∨ free_in_aexp x a2

theorem aeval_free (s1 s2 a) (h : ∀ x, free_in_aexp x a → s1 x = s2 x) :
    aeval s1 a = aeval s2 a := by
  fun_induction aeval s1 a with grind

/-
  1.3 Boolean expressions

  The IMP language has conditional statements (if/then/else) and loops.  They are controlled by expressions that evaluate to Boolean values.  Here is the abstract syntax of Boolean expressions.
-/

inductive bexp : Type where
  | TRUE                              -- always true
  | FALSE                             -- always false
  | EQUAL (a1 : aexp) (a2 : aexp)     -- whether [a1=a]
  | LESSEQUAL (a1 : aexp) (a2 : aexp) -- whether [a1≤a]
  | NOT (b1 : bexp)                   -- Boolean negation
  | AND (b1 : bexp) (b2 : bexp)       -- Boolean conjunction

/-
  There are many useful derived forms.
-/
def NOTEQUAL (a1 a2 : aexp) : bexp := .NOT (.EQUAL a1 a2)

def GREATEREQUAL (a1 a2 : aexp) : bexp := .LESSEQUAL a2 a1

def GREATER (a1 a2 : aexp) : bexp := .NOT (.LESSEQUAL a1 a2)

def LESS (a1 a2 : aexp) : bexp := GREATER a2 a1

@[grind] def OR (b1 b2 : bexp) : bexp := .NOT (.AND (.NOT b1) (.NOT b2))

/-
Just like arithmetic expressions evaluate to integers, Boolean expressions evaluate to Boolean values `true` or `false`.
-/
@[grind] def beval (s : store) (b : bexp) : Bool :=
  match b with
  | .TRUE => true
  | .FALSE => false
  | .EQUAL a1 a2 => aeval s a1 = aeval s a2
  | .LESSEQUAL a1 a2 => aeval s a1 <= aeval s a2
  | .NOT b1 =>  !(beval s b1)
  | .AND b1 b2 => beval s b1 && beval s b2

/-
  We show the expected semantics for the `OR` derived form:
-/
theorem beval_OR : beval s (OR b1 b2) = beval s b1 ∨ beval s b2 := by grind

/-
  1.4 Commands

  To complete the definition of the IMP language, here is the abstract syntax of commands, also known as statements.
-/
inductive com : Type where
  | SKIP                                        -- do nothing
  | ASSIGN (x : ident) (a : aexp)               -- assignment: [v := a]
  | SEQ (c1 : com) (c2 : com)                   -- sequence: [c1; c2]
  | IFTHENELSE (b : bexp) (c1 : com) (c2 : com) -- conditional: [if b then c1 else c2]
  | WHILE (b : bexp) (c1 : com)                 -- loop: [while b do c1 done]

--  We can write `c1 ;; c2` instead of `.SEQ c1 c2`, it is easier on the eyes.
notation:10 l:10 " ;; " r:11 => com.SEQ l r


/-
  A useful operation over stores: `update x v s` is the store that maps `x` to `v` and is equal to `s` for all variables other than `x`.
-/
@[grind] def update (x : ident) (v : Int) (s : store) : store :=
  fun y => if x == y then v else s y

/-
  A naive approach to giving semantics to commands is to write an evaluation function `cexec s c` that runs the command `c` in initial store `s` and returns the final store when `c` terminates.

  def cexec_fail (s: store) (c: com) : store :=
  match c with
  | .SKIP => s
  | .ASSIGN x a => update x (aeval s a) s
  | .SEQ c1 c2 => cexec_fail (cexec_fail s c1) c2
  | .IFTHENELSE b c1 c2 => if beval s b then cexec_fail s c1 else cexec_fail s c2
  | .WHILE b c1 =>
      if beval s b
      then (cexec_fail (cexec_fail s c1) (.WHILE b c1))
      else s

  The definition above is rejected by Lean, and rightly so, because all Lean functions must terminate, yet the `.WHILE` case may not terminate.  Consider for example the infinite loop `.WHILE .TRUE .SKIP`.

  Worse, IMP is Turing-complete, since it has unbounded iteration (`.WHILE`) plus arbitrary-precision integers.  Hence, there is no computable function `cexec s c` that would return `.Some s'` if `c` terminates with store `s'`, and `.none` if `c` does not terminate.

  However, instead of computable functions, we can use a relation `cexec s c s'` that holds iff command `c`, started in state `s`, terminates with state `s'`.  This relation can easily be defined as a Lean inductive predicate:
-/

@[grind] inductive cexec : store → com → store → Prop where
  | cexec_skip :
      cexec s .SKIP s
  | cexec_assign :
      cexec s (.ASSIGN x a) (update x (aeval s a) s)
  | cexec_seq :
      cexec s c1 s' -> cexec s' c2 s'' ->
      cexec s (.SEQ c1 c2) s''
  | cexec_ifthenelse :
      cexec s (if beval s b then c1 else c2) s' ->
      cexec s (.IFTHENELSE b c1 c2) s'
  | cexec_while_done :
      beval s b = false ->
      cexec s (.WHILE b c) s
  | cexec_while_loop :
      beval s b = true -> cexec s c s' -> cexec s' (.WHILE b c) s'' ->
      cexec s (.WHILE b c) s''

attribute [grind] cexec.cexec_skip
attribute [grind <=] cexec.cexec_seq

/-
  This style of semantics is known as natural semantics or big-step operational semantics.  The predicate `cexec s c s'` holds iff there exists a finite derivation of this conclusion, using the axioms and inference rules above.
  The structure of the derivation represents the computations performed by `c` in a tree-like manner.  The finiteness of the derivation guarantees that only terminating
  executions satisfy `cexec`.

  Indeed, `.WHILE .TRUE .SKIP` does not satisfy `cexec`:
-/
theorem cexec_infinite_loop (s : store) : ¬ ∃ s', cexec s (.WHILE .TRUE .SKIP) s' := by
  rintro ⟨s', h₂⟩
  generalize heq : com.WHILE .TRUE .SKIP = c at h₂
  induction h₂ with grind

/-
  Our naive idea of an execution function for commands was not completely off.  We can define an approximation of such a function by bounding a priori the recursion depth, using a `fuel` parameter of type `Nat`.  When the fuel drops to `0`, `.none` is returned, meaning that the final store could not be computed.
-/
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

def cbv_test_instance (n : Nat): com := match n with
  | 0 => .SKIP
  | n + 1 => .SEQ (.SEQ (.ASSIGN 1 (.PLUS (.VAR 1) (.CONST 2))) (.ASSIGN 1 (.MINUS (.VAR 1) (.CONST 1))))  (cbv_test_instance n)

def cbv_test (n : Nat) := cexec_bounded (n + n + 1) (fun _ => 0) (cbv_test_instance n)
def problem_instance (n : Nat) := (cbv_test n).getD (fun _ => 0) 1 = n

set_option trace.Meta.Tactic true

syntax "build_fn_with " num : tactic


theorem leroy_test : problem_instance 10 := by
  unfold problem_instance
  unfold cbv_test
  simp only [cbv_test_instance]
  conv =>
    lhs
    cbv
  rfl
