/-!
A verification condition generator for a small imperative language, written as a `sym =>` script.
The loop `repeat match_goal with …` selects the rule to apply from the target of the main goal,
so the same script verifies every program below.
The language is the one of `tests/bench/sym/add_sub_cancel.lean`, extended with `output`,
`unset`, and `cond`.
-/

abbrev Word := UInt32

def Word.add (a b : Option Word) : Word :=
  match a, b with
  | some a, some b => a+b
  | _, _ => 0

def Word.sub (a b : Option Word) : Word :=
  match a, b with
  | some a, some b => a-b
  | _, _ => 0

theorem Word.add_some (a b : Word) : Word.add (some a) (some b) = a + b := rfl
theorem Word.sub_some (a b : Word) : Word.sub (some a) (some b) = a - b := rfl

structure PartialMap (A B : Type) where
  fn : A → Option B

def PartialMap.get {A B : Type} (m : PartialMap A B) (k : A) : Option B :=
  m.fn k

def PartialMap.put [DecidableEq A] (m : PartialMap A B) (k : A) (v : B) : PartialMap A B :=
  { fn := fun x => if x = k then some v else m.fn x }

def PartialMap.remove [DecidableEq A] (m : PartialMap A B) (k : A) : PartialMap A B :=
  { fn := fun x => if x = k then none else m.fn x }

@[ext] theorem PartialMap.ext (m₁ m₂ : PartialMap A B) (h : ∀ k, m₁.get k = m₂.get k) :
    m₁ = m₂ := by
  cases m₁; cases m₂; congr; funext; apply h

theorem PartialMap.get_put {A B : Type} [DecidableEq A] (m : PartialMap A B) (k : A) (v : B) :
    (m.put k v).get k = some v := by
  simp [PartialMap.get, PartialMap.put]

theorem PartialMap.get_put_diff {A B : Type} [DecidableEq A] (m : PartialMap A B) (k k' : A) (v : B)
    (h : k ≠ k') : (m.put k' v).get k = m.get k :=
  ite_eq_right h

theorem PartialMap.put_put {A B : Type} [DecidableEq A] (m : PartialMap A B) (k : A) (v₁ v₂ : B) :
    (m.put k v₁).put k v₂ = m.put k v₂ := by
  ext k'; simp only [PartialMap.get, PartialMap.put]; split <;> rfl

theorem PartialMap.get_remove {A B : Type} [DecidableEq A] (m : PartialMap A B) (k : A) :
    (m.remove k).get k = none := by
  simp [PartialMap.get, PartialMap.remove]

theorem PartialMap.get_remove_diff {A B : Type} [DecidableEq A] (m : PartialMap A B) (k k' : A)
    (h : k ≠ k') : (m.remove k').get k = m.get k :=
  ite_eq_right h

inductive Binop where
  | add | sub

def Binop.interp (op : Binop) (a b : Option Word) : Word :=
  match op with
  | .add => Word.add a b
  | .sub => Word.sub a b

theorem Binop.interp_add (w1 w2 : Option Word) : Binop.interp .add w1 w2 = Word.add w1 w2 := rfl
theorem Binop.interp_sub (w1 w2 : Option Word) : Binop.interp .sub w1 w2 = Word.sub w1 w2 := rfl

inductive Expr where
  | literal (v : Word)
  | var (x : String)
  | op (bop : Binop) (e1 e2 : Expr)

def Expr.eval (le : PartialMap String Word) (e : Expr) : Option Word :=
  match e with
  | .literal v    => some v
  | .var x        => le.get x
  | .op bop e1 e2 => some (bop.interp (e1.eval le) (e2.eval le))

inductive Cmd where
  | skip : Cmd
  | set : String → Expr → Cmd
  | unset : String → Cmd
  | cond : Expr → Cmd → Cmd → Cmd
  | seq : Cmd → Cmd → Cmd
  | input : String → Cmd
  | output : String → Cmd

inductive IOEvent
  | IN : Word → IOEvent
  | OUT : Word → IOEvent

abbrev Post := List IOEvent → PartialMap String Word → Prop

/-- A weakest-precondition style semantics: `Exec c t l post` holds if every run of `c` from
trace `t` and locals `l` ends in a state satisfying `post`. -/
inductive Exec : Cmd → List IOEvent → PartialMap String Word → Post → Prop
  | skip : post t l → Exec .skip t l post
  | seq : Exec c1 t l mid → (∀ t' l', mid t' l' → Exec c2 t' l' post) → Exec (.seq c1 c2) t l post
  | set : Expr.eval l e = some v → post t (l.put x v) → Exec (.set x e) t l post
  | unset : post t (l.remove x) → Exec (.unset x) t l post
  | input : (∀ v, post (.IN v :: t) (l.put x v)) → Exec (.input x) t l post
  | output : l.get x = some v → post (.OUT v :: t) l → Exec (.output x) t l post
  | cond : Expr.eval l e = some v →
      (v ≠ 0 → Exec c1 t l post) → (v = 0 → Exec c2 t l post) → Exec (.cond e c1 c2) t l post

theorem Exec.seq_cps : Exec c1 t l (fun t' l' => Exec c2 t' l' post) → Exec (.seq c1 c2) t l post :=
  fun h => .seq h fun _ _ h => h

infixr:30 " ;; " => Cmd.seq

register_sym_simp evalExpr where
  post := ground >> rewrite [Expr.eval.eq_1, Expr.eval.eq_2, Expr.eval.eq_3] with self

register_sym_simp evalStep where
  post := ground >> rewrite [PartialMap.get_put_diff, PartialMap.get_put,
    PartialMap.get_remove_diff, Binop.interp_add, Binop.interp_sub, Word.add_some, Word.sub_some,
    PartialMap.put_put, UInt32.add_sub_cancel, Option.some.injEq, not_false_eq_true,
    ne_eq] with self

theorem exists_eq_True (a : α) : (∃ x, a = x) = True := by
  simp

register_sym_simp postStep where
  post := ground >> rewrite [List.cons.injEq, IOEvent.IN.injEq, IOEvent.OUT.injEq,
    PartialMap.put_put, PartialMap.get_put, PartialMap.get_put_diff, PartialMap.get_remove,
    PartialMap.get_remove_diff, Option.some.injEq, UInt32.add_sub_cancel, and_assoc, and_true,
    true_and, and_self, eq_self, exists_and_left, exists_eq_left', exists_eq_True, ne_eq,
    not_false_eq_true] with self

/--
Verification condition generator: applies to each goal the step that matches it, until no step
matches any goal. The remaining goals are the postconditions of the program paths.
-/
macro "exec_vcgen" : grind => `(grind|
  repeat any_goals
    match_goal with
    | Exec (.seq _ _) _ _ _    => apply Exec.seq_cps
    | Exec .skip _ _ _         => apply Exec.skip
    | Exec (.set _ _) _ _ _    => apply Exec.set
    | Exec (.unset _) _ _ _    => apply Exec.unset
    | Exec (.input _) _ _ _    => apply Exec.input; intro~
    | Exec (.output _) _ _ _   => apply Exec.output
    | Exec (.cond _ _ _) _ _ _ => apply Exec.cond
    | Expr.eval _ _ = _        => simp evalExpr; simp evalStep; apply Eq.refl
    | PartialMap.get _ _ = _   => simp evalStep; apply Eq.refl
    | _ → _                    => intro~)

set_option maxRecDepth 10000

/-! `t := t + t; t := t - x` repeated `n` times, preceded by `input x; t := x`. -/

def repeated_cmds (n : Nat) (t x : String) : Cmd :=
  match n with
  | 0 => .skip
  | n + 1 => .set t (.op .add (.var t) (.var t)) ;; .set t (.op .sub (.var t) (.var x)) ;;
      repeated_cmds n t x

def generated_cmd (n : Nat) (t x : String) : Cmd :=
  .input x ;; .set t (.var x) ;; repeated_cmds n t x

register_sym_simp unfoldCmd where
  post := ground >> rewrite [generated_cmd.eq_1, repeated_cmds.eq_1, repeated_cmds.eq_2] with self

example : ∀ l : PartialMap String Word, Exec (generated_cmd 20 "a" "b") [] l fun t' l' =>
    ∃ v, t' = [.IN v] ∧ l'.get "a" = some v := by
  sym =>
    intro~ l
    simp unfoldCmd
    exec_vcgen
    simp postStep

/-! Swap two inputs through a temporary, then output both. -/

def swap : Cmd :=
  .input "x" ;; .input "y" ;;
  .set "t" (.var "x") ;; .set "x" (.var "y") ;; .set "y" (.var "t") ;; .unset "t" ;;
  .output "x" ;; .output "y"

example : ∀ l : PartialMap String Word, Exec swap [] l fun t' l' =>
    ∃ a b, t' = [.OUT a, .OUT b, .IN b, .IN a] ∧ l'.get "t" = none := by
  sym =>
    intro~ l
    simp [swap]
    exec_vcgen
    simp postStep

/-! Arithmetic on literals. Ground evaluation computes the output `z = 3 + 4 - 3`. -/

def arith : Cmd :=
  .set "x" (.literal 3) ;; .set "y" (.op .add (.var "x") (.literal 4)) ;;
  .set "z" (.op .sub (.var "y") (.var "x")) ;; .output "z"

example : ∀ l : PartialMap String Word, Exec arith [] l fun t' _ => t' = [.OUT 4] := by
  sym =>
    intro~ l
    simp [arith]
    exec_vcgen
    simp postStep

/-! Branching on an input: both branches produce a nonzero output. -/

def nonzero : Cmd :=
  .input "x" ;;
  .cond (.var "x") (.set "y" (.var "x")) (.set "y" (.literal 1)) ;;
  .output "y"

example : ∀ l : PartialMap String Word, Exec nonzero [] l fun t' _ =>
    ∃ v w, t' = [.OUT w, .IN v] ∧ w ≠ 0 := by
  sym =>
    intro~ l
    simp [nonzero]
    exec_vcgen
    all_goals simp postStep
    tactic => assumption

/-! Nested branching: three paths, each with a nonzero output. -/

def nested : Cmd :=
  .input "x" ;; .input "y" ;;
  .cond (.var "x") (.cond (.var "y") (.set "z" (.var "y")) (.set "z" (.literal 7)))
    (.set "z" (.literal 1)) ;;
  .output "z"

example : ∀ l : PartialMap String Word, Exec nested [] l fun t' _ =>
    ∃ a b w, t' = [.OUT w, .IN b, .IN a] ∧ w ≠ 0 := by
  sym =>
    intro~ l
    simp [nested]
    exec_vcgen
    all_goals simp postStep
    tactic => assumption
