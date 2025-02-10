# Standard library style

Please take some time to familiarize yourself with the stylistic conventions of
the project and the specific part of the library you are planning to contribute
to. While the Lean compiler may not enforce strict formatting rules,
consistently formatted code is much easier for others to read and maintain.
Attention to formatting is more than a cosmetic concern—it reflects the same
level of precision and care required to meet the deeper standards of the Lean 4
standard library.

Below we will give specific formatting prescriptions for various language constructs. Note that this style guide only applies to the Lean standard library, even though some examples in the guide are taken from other parts of the Lean code base.

## Basic whitespace rules

Syntactic elements (like `:`, `:=`, `|`, `::`) are surrounded by single spaces, with the exception of `,` and `;`, which are followed by a space but not preceded by one. Delimiters (like `()`, `{}`) do not have spaces on the inside, with the exceptions of subtype notation and structure instance notation.

Examples of correctly formatted function parameters:

* `{α : Type u}`
* `[BEq α]`
* `(cmp : α → α → Ordering)`
* `(hab : a = b)`
* `{d : { l : List ((n : Nat) × Vector Nat n) // l.length % 2 = 0 }}`

Examples of correctly formatted terms:

* `1 :: [2, 3]`
* `letI : Ord α := ⟨cmp⟩; True`
* `(⟨2, 3⟩ : Nat × Nat)`
* `((2, 3) : Nat × Nat)`
* `{ x with fst := f (4 + f 0), snd := 4, .. }`
* `match 1 with | 0 => 0 | _ => 0`
* `fun ⟨a, b⟩ _ _ => by cases hab <;> apply id; rw [hbc]`

Configure your editor to remove trailing whitespace. If you have set up Visual Studio Code for Lean development in the recommended way then the correct setting is applied automatically.

## Splitting terms across multiple lines

When splitting a term across multiple lines, increase indentation by two spaces starting from the second line. When splitting a function application, try to split at argument boundaries. If an argument itself needs to be split, increase indentation further as appropriate.

When splitting at an infix operator, the operator goes at the end of the first line, not at the beginning of the second line. When splitting at an infix operator, you may or may not increase indentation depth, depending on what is more readable.

When splitting an `if`-`then`-`else` expression, the `then` keyword wants to stay with the condition and the `else` keyword wants to stay with the alternative term. Otherwise, indent as if the `if` and `else` keywords were arguments to the same function.

When splitting a comma-separated bracketed sequence (i.e., anonymous constructor application, list/array/vector literal, tuple) it is allowed to indent subsequent lines for alignment, but indenting by two spaces is also allowed.

Do not orphan parentheses.

Correct:
```lean
def MacroScopesView.isPrefixOf (v₁ v₂ : MacroScopesView) : Bool :=
  v₁.name.isPrefixOf v₂.name &&
  v₁.scopes == v₂.scopes &&
  v₁.mainModule == v₂.mainModule &&
  v₁.imported == v₂.imported
```

Correct:
```lean
theorem eraseP_eq_iff {p} {l : List α} :
    l.eraseP p = l' ↔
      ((∀ a ∈ l, ¬ p a) ∧ l = l') ∨
        ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧
          l = l₁ ++ a :: l₂ ∧ l' = l₁ ++ l₂ :=
  sorry
```

Correct:
```lean
example : Nat :=
  functionWithAVeryLongNameSoThatSomeArgumentsWillNotFit firstArgument secondArgument
    (firstArgumentWithAnEquallyLongNameAndThatFunctionDoesHaveMoreArguments firstArgument
      secondArgument)
    secondArgument
```

Correct:
```lean
theorem size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).size =
      if m.contains k && (f (m.get? k)).isNone then
        m.size - 1
      else if !m.contains k && (f (m.get? k)).isSome then
        m.size + 1
      else
        m.size := by
 simp_to_raw using Raw₀.size_alter
```

Correct:
```lean
theorem get?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).get? k' =
      if h : k == k' then
        cast (congrArg (Option ∘ β) (eq_of_beq h)) (f (m.get? k))
      else m.get? k' := by
 simp_to_raw using Raw₀.get?_alter
```

Correct:
```lean
example : Nat × Nat :=
  ⟨imagineThisWasALongTerm,
   imagineThisWasAnotherLongTerm⟩
```

Correct:
```lean
example : Nat × Nat :=
  ⟨imagineThisWasALongTerm,
    imagineThisWasAnotherLongTerm⟩
```

Correct:
```lean
example : Vector Nat :=
  #v[imagineThisWasALongTerm,
     imagineThisWasAnotherLongTerm]
```

## Basic file structure

Every file should start with a copyright header, imports (in the standard library, this always includes a `prelude` declaration) and a module documentation string. There should not be a blank line between the copyright header and the imports. There should be a blank line between the imports and the module documentation string.

Correct:
```lean
/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Yury Kudryashov
-/
prelude
import Init.Data.List.Pairwise
import Init.Data.List.Find

/-!
**# Lemmas about `List.eraseP` and `List.erase`.**
-/
```

Syntax that is not supposed to be user-facing must be scoped. New public syntax must always be discussed explicitly in an RFC.

## Top-level commands and declarations

All top-level commands are unindented. Sectioning commands like `section` and `namespace` do not increase the indentation level.

Attributes may be placed on the same line as the rest of the command or on a separate line.

Multi-line declaration headers are indented by four spaces starting from the second line. The colon that indicates the type of a declaration may not be placed at the start of a line or on its own line.

Declaration bodies are indented by two spaces. Short declaration bodies may be placed on the same line as the declaration type.

Correct:
```lean
theorem eraseP_eq_iff {p} {l : List α} :
    l.eraseP p = l' ↔
      ((∀ a ∈ l, ¬ p a) ∧ l = l') ∨
        ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧
          l = l₁ ++ a :: l₂ ∧ l' = l₁ ++ l₂ :=
  sorry
```

Correct:
```lean
@[simp] theorem eraseP_nil : [].eraseP p = [] := rfl
```

Correct:
```lean
@[simp]
theorem eraseP_nil : [].eraseP p = [] := rfl
```

### Documentation comments

Note to external contributors: this is a section where the Lean style and the mathlib style are different.

Declarations should be documented as required by the `docBlame` linter, which may be activated in a file using
`set_option linter.missingDocs true` (we allow these to stay in the file).

Single-line documentation comments should go on the same line as `/--`/`-/`, while multi-line documentation strings
should have these delimiters on their own line, with the documentation comment itself unindented.

Documentation comments must be written in the indicative mood. Use American orthography.

Correct:
```lean
/-- Carries out a monadic action on each mapping in the hash map in some order. -/
@[inline] def forM (f : (a : α) → β a → m PUnit) (b : Raw α β) : m PUnit :=
  b.buckets.forM (AssocList.forM f)
```

Correct:
```lean
/--
Monadically computes a value by folding the given function over the mappings in the hash
map in some order.
-/
@[inline] def foldM (f : δ → (a : α) → β a → m δ) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.foldlM (fun acc l => l.foldlM f acc) init
```

### Where clauses

The `where` keyword should be unindented, and all declarations bound by it should be indented with two spaces.

Blank lines before and after `where` and between declarations bound by `where` are optional and should be chosen
to maximize readability.

Correct:
```lean
@[simp] theorem partition_eq_filter_filter (p : α → Bool) (l : List α) :
    partition p l = (filter p l, filter (not ∘ p) l) := by
  simp [partition, aux]
where
  aux (l) {as bs} : partition.loop p l (as, bs) =
      (as.reverse ++ filter p l, bs.reverse ++ filter (not ∘ p) l) :=
    match l with
    | [] => by simp [partition.loop, filter]
    | a :: l => by cases pa : p a <;> simp [partition.loop, pa, aux, filter, append_assoc]
```

### Termination arguments

The `termination_by`, `decreasing_by`, `partial_fixpoint` keywords should be unindented. The associated terms should be indented like declaration bodies.

Correct:
```lean
@[inline] def multiShortOption (handle : Char → m PUnit) (opt : String) : m PUnit := do
  let rec loop (p : String.Pos) := do
    if h : opt.atEnd p then
      return
    else
      handle (opt.get' p h)
      loop (opt.next' p h)
  termination_by opt.utf8ByteSize - p.byteIdx
  decreasing_by
    simp [String.atEnd] at h
    apply Nat.sub_lt_sub_left h
    simp [String.lt_next opt p]
  loop ⟨1⟩
```

Correct:
```lean
def substrEq (s1 : String) (off1 : String.Pos) (s2 : String) (off2 : String.Pos) (sz : Nat) : Bool :=
  off1.byteIdx + sz ≤ s1.endPos.byteIdx && off2.byteIdx + sz ≤ s2.endPos.byteIdx && loop off1 off2 { byteIdx := off1.byteIdx + sz }
where
  loop (off1 off2 stop1 : Pos) :=
    if _h : off1.byteIdx < stop1.byteIdx then
      let c₁ := s1.get off1
      let c₂ := s2.get off2
      c₁ == c₂ && loop (off1 + c₁) (off2 + c₂) stop1
    else true
  termination_by stop1.1 - off1.1
  decreasing_by
    have := Nat.sub_lt_sub_left _h (Nat.add_lt_add_left c₁.utf8Size_pos off1.1)
    decreasing_tactic
```

Correct:
```lean
theorem div_add_mod (m n : Nat) : n * (m / n) + m % n = m := by
  rw [div_eq, mod_eq]
  have h : Decidable (0 < n ∧ n ≤ m) := inferInstance
  cases h with
  | isFalse h => simp [h]
  | isTrue h =>
    simp [h]
    have ih := div_add_mod (m - n) n
    rw [Nat.left_distrib, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, ih, Nat.add_comm, Nat.sub_add_cancel h.2]
decreasing_by apply div_rec_lemma; assumption
```

### Deriving

The `deriving` clause should be unindented.

Correct:
```lean
structure Iterator where
  array : ByteArray
  idx : Nat
deriving Inhabited
```

## Language constructs

### Pattern matching, induction etc.

Match arms are indented at the indentation level that the match statement would have if it was on its own line. If the match is implicit, then the arms should be indented as if the match was explicitly given. The content of match arms is indented two spaces, so that it appears on the same level as the match pattern.

Correct:
```lean
def alter [BEq α] {β : Type v} (a : α) (f : Option β → Option β) :
    AssocList α (fun _ => β) → AssocList α (fun _ => β)
  | nil => match f none with
    | none => nil
    | some b => AssocList.cons a b nil
  | cons k v l =>
    if k == a then
      match f v with
      | none => l
      | some b => cons a b l
    else
      cons k v (alter a f l)
```

Correct:
```lean
theorem eq_append_cons_of_mem {a : α} {xs : List α} (h : a ∈ xs) :
    ∃ as bs, xs = as ++ a :: bs ∧ a ∉ as := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    simp at h
    cases h with
    | inl h => exact ⟨[], xs, by simp_all⟩
    | inr h =>
      by_cases h' : a = x
      · subst h'
        exact ⟨[], xs, by simp⟩
      · obtain ⟨as, bs, rfl, h⟩ := ih h
        exact ⟨x :: as, bs, rfl, by simp_all⟩
```

Aligning match arms is allowed, but not required.

Correct:
```lean
def mkEqTrans? (h₁? h₂? : Option Expr) : MetaM (Option Expr) :=
  match h₁?, h₂? with
  | none, none       => return none
  | none, some h     => return h
  | some h, none     => return h
  | some h₁, some h₂ => mkEqTrans h₁ h₂
```

Correct:
```lean
def mkEqTrans? (h₁? h₂? : Option Expr) : MetaM (Option Expr) :=
  match h₁?, h₂? with
  | none, none => return none
  | none, some h => return h
  | some h, none => return h
  | some h₁, some h₂ => mkEqTrans h₁ h₂
```

Correct:
```lean
def mkEqTrans? (h₁? h₂? : Option Expr) : MetaM (Option Expr) :=
  match h₁?, h₂? with
  | none,    none    => return none
  | none,    some h  => return h
  | some h,  none    => return h
  | some h₁, some h₂ => mkEqTrans h₁ h₂
```

### Structures

Note to external contributors: this is a section where the Lean style and the mathlib style are different.

When using structure instance syntax over multiple lines, the opening brace should go on the preceding line, while the closing brace should go on its own line. The rest of the syntax should be indented by one level. During structure updates, the `with` clause goes on the same line as the opening brace. Aligning at the assignment symbol is allowed but not required.

Correct:
```lean
def addConstAsync (env : Environment) (constName : Name) (kind : ConstantKind) (reportExts := true) :
    IO AddConstAsyncResult := do
  let sigPromise ← IO.Promise.new
  let infoPromise ← IO.Promise.new
  let extensionsPromise ← IO.Promise.new
  let checkedEnvPromise ← IO.Promise.new
  let asyncConst := {
    constInfo := {
      name := constName
      kind
      sig := sigPromise.result
      constInfo := infoPromise.result
    }
    exts? := guard reportExts *> some extensionsPromise.result
  }
  return {
    constName, kind
    mainEnv := { env with
      asyncConsts := env.asyncConsts.add asyncConst
      checked := checkedEnvPromise.result }
    asyncEnv := { env with
      asyncCtx? := some { declPrefix := privateToUserName constName.eraseMacroScopes }
    }
    sigPromise, infoPromise, extensionsPromise, checkedEnvPromise
  }
```

Correct:
```lean
instance [Inhabited α] : Inhabited (Descr α β σ) where
  default := {
    name         := default
    mkInitial    := default
    ofOLeanEntry := default
    toOLeanEntry := default
    addEntry     := fun s _ => s
  }
```

## Tactic proofs

Tactic proofs are the most common thing to break during any kind of upgrade, so it is important to write them in a way that minimizes the likelihood of proofs breaking and that makes it easy to debug breakages if they do occur.

If there are multiple goals, either use a tactic combinator (like `all_goals`) to operate on all of them or a clearly specified subset, or use focus dots to work on goals one at a time. Using structured proofs (e.g., `induction … with`) is encouraged but not mandatory.

Squeeze non-terminal `simp`s (i.e., calls to `simp` which do not close the goal). Squeezing terminal `simp`s is generally discouraged, although there are exceptions (for example if squeezing yields a noticeable performance improvement).

Do not over-golf proofs in ways that are likely to lead to hard-to-debug breakage. Examples of things to avoid include complex multi-goal manipulation using lots of tactic combinators, complex uses of the substitution operator (`▸`) and clever point-free expressions (possibly involving anonymous function notation for multiple arguments).

Do not under-golf proofs: for routine tasks, use the most powerful tactics available.

Do not use `erw`. Avoid using `rfl` after `simp` or `rw`, as this usually indicates a missing lemma that should be used instead of `rfl`.

Use `(d)simp` or `rw` instead of `delta` or `unfold`. Use `refine` instead of `refine’`. Use `haveI` and `letI` only if they are actually required.

Prefer highly automated tactics (like `grind` and `omega`) over low-level proofs, unless the automated tactic requires unacceptable additional imports or has bad performance. If you decide against using a highly automated tactic, leave a comment explaining the decision.

## `do` notation

The `do` keyword goes on the same line as the corresponding `:=` (or `=>`, or similar). `Id.run do` should be treated as if it was a bare `do`.

Use early `return` statements to reduce nesting depth and make the non-exceptional control flow of a function easier to see.

Alternatives for `let` matches may be placed in the same line or in the next line, indented by two spaces. If the term that is
being matched on is itself more than one line and there is an alternative present, consider breaking immediately after `←` and indent
as far as necessary to ensure readability.

Correct:
```lean
def getFunDecl (fvarId : FVarId) : CompilerM FunDecl := do
  let some decl ← findFunDecl? fvarId | throwError "unknown local function {fvarId.name}"
  return decl
```

Correct:
```lean
def getFunDecl (fvarId : FVarId) : CompilerM FunDecl := do
  let some decl ←
        findFunDecl? fvarId
    | throwError "unknown local function {fvarId.name}"
  return decl
```

Correct:
```lean
def getFunDecl (fvarId : FVarId) : CompilerM FunDecl := do
  let some decl ← findFunDecl?
      fvarId
    | throwError "unknown local function {fvarId.name}"
  return decl
```

Correct:
```lean
def tagUntaggedGoals (parentTag : Name) (newSuffix : Name) (newGoals : List MVarId) : TacticM Unit := do
  let mctx ← getMCtx
  let mut numAnonymous := 0
  for g in newGoals do
    if mctx.isAnonymousMVar g then
      numAnonymous := numAnonymous + 1
  modifyMCtx fun mctx => Id.run do
    let mut mctx := mctx
    let mut idx  := 1
    for g in newGoals do
      if mctx.isAnonymousMVar g then
        if numAnonymous == 1 then
          mctx := mctx.setMVarUserName g parentTag
        else
          mctx := mctx.setMVarUserName g (parentTag ++ newSuffix.appendIndexAfter idx)
        idx := idx + 1
    pure mctx
```

