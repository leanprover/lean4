/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Name
import Lake.Util.Compare

open Lean

namespace Lake

export Lean (Name NameMap)

-- # Name Helpers

namespace Name

@[simp] theorem beq_rfl (n : Name) : (n == n) = true := by
  simp only [BEq.beq]; induction n <;> simp [Name.beq, *]

@[simp] theorem isPrefixOf_self {n : Name} : n.isPrefixOf n = true := by
  cases n <;> simp [Name.isPrefixOf]

@[simp] theorem isPrefixOf_append {n m : Name} : n.isPrefixOf (n ++ m) = true := by
  simp only [HAppend.hAppend, Append.append]
  induction m <;> simp [Name.isPrefixOf, Name.append, *]

/--
The propositional condition of a `Name` being well-formed.
A well-formed name has its has hash computable in the standard manner
(i.e., via the internals of `mkStr` and `mkNum`).
-/
inductive WellFormed : Name → Prop
| anonymousWff : WellFormed Name.anonymous
| strWff {n p s} : WellFormed p → n = Name.mkStr p s → WellFormed n
| numWff {n p v} : WellFormed p → n = Name.mkNum p v → WellFormed n

def WellFormed.elimStr : WellFormed (Name.str p s h) → WellFormed p
| strWff w rfl => w

def WellFormed.elimNum : WellFormed (Name.num p v h) → WellFormed p
| numWff w rfl => w

theorem eq_of_wf_quickCmpAux
(n : Name) (w : WellFormed n) (n' : Name) (w' : WellFormed n')
: Name.quickCmpAux n n' = Ordering.eq → n = n' := by
  revert n'
  induction w with
  | anonymousWff =>
    intro n' w'; cases w' <;> simp [Name.quickCmpAux, *]
  | @strWff n p s _ h ih =>
    intro n' w'
    cases w' with
    | anonymousWff =>
      simp [h, Name.quickCmpAux]
    | @strWff n' p' s' w' h' =>
      simp only [h, h', Name.quickCmpAux]
      intro h_cmp
      split at h_cmp
      next h_cmp_s =>
        let p_eq := ih p' w' h_cmp
        let s_eq := String.eq_of_compare h_cmp_s
        rw [s_eq, p_eq]
      next =>
        contradiction
    | @numWff n' p' v' w' h' =>
      simp [h, h', Name.quickCmpAux]
  | @numWff m p v _ h ih =>
    intro n' w'
    cases w' with
    | anonymousWff =>
      simp [h, Name.quickCmpAux]
    | @strWff n' p' s' w' h' =>
      simp [h, h', Name.quickCmpAux]
    | @numWff n' p' v' w' h' =>
      simp only [h, h', Name.quickCmpAux]
      intro h_cmp
      split at h_cmp
      next h_cmp_v =>
        let p_eq := ih p' w' h_cmp
        let v_eq := Nat.eq_of_compare h_cmp_v
        rw [v_eq, p_eq]
      next =>
        contradiction

theorem wf_of_append {n n' : Name}
(w : WellFormed n) (w' : WellFormed n') : WellFormed (n.append n') :=  by
  induction w' with
  | anonymousWff =>
    simp [w, Name.append]
  | @strWff n' p s w' h' ih =>
    unfold Name.mkStr at h'
    simp only [Name.append, h']
    exact WellFormed.strWff ih rfl
  | @numWff n' p v w' h' ih =>
    unfold Name.mkNum at h'
    simp only [Name.append, h']
    exact WellFormed.numWff ih rfl

end Name

-- # Subtype Helpers

namespace Subtype

theorem val_eq_of_eq {a b : Subtype p} (h : a = b) : a.val = b.val :=
  h ▸ rfl

theorem eq_of_val_eq : ∀ {a b : Subtype p}, a.val = b.val → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem eq_iff_val_eq {a b : Subtype p} : a = b ↔ a.val = b.val :=
  Iff.intro val_eq_of_eq eq_of_val_eq

theorem ne_of_val_ne {a b : Subtype p} (h : a.val ≠ b.val) : a ≠ b :=
  fun h' => absurd (val_eq_of_eq h') h

theorem val_ne_of_ne {a b : Subtype p} (h : a ≠ b) : a.val ≠ b.val :=
  fun h' => absurd (eq_of_val_eq h') h

theorem ne_iff_val_ne {a b : Subtype p} : a ≠ b ↔ a.val ≠ b.val :=
  Iff.intro val_ne_of_ne ne_of_val_ne

end Subtype

-- # Well-formed Names


/--
A `WellFormed` `Name`.
Such a name has its hash provably computed in the standard manner.
This allows us to prove that the `beq` and `quickCmp` functions' equality
corresponds to propositional equality for this subtype.
-/
abbrev WfName :=
  {n : Name // Name.WellFormed n}

namespace WfName

def anonymous : WfName :=
  ⟨Name.anonymous, Name.WellFormed.anonymousWff⟩

instance : Inhabited WfName := ⟨anonymous⟩

def isAnonymous : WfName → Bool
| ⟨.anonymous, _⟩ => true
| _ => false

@[inline] def mkStr : WfName → String → WfName
| ⟨p, h⟩, s => ⟨Name.mkStr p s, Name.WellFormed.strWff h rfl⟩

@[inline] def mkNum : WfName → Nat → WfName
| ⟨p, h⟩, v => ⟨Name.mkNum p v, Name.WellFormed.numWff h rfl⟩

def ofName : Name → WfName
| .anonymous => anonymous
| .str p s _ => mkStr (ofName p) s
| .num p v _ => mkNum (ofName p) v

def ofString (str : String) : WfName :=
  str.splitOn "." |>.foldl (fun n p => mkStr n p.trim) anonymous

instance : Coe String WfName := ⟨ofString⟩

@[inline] protected def toString (escape := true) : WfName → String
| ⟨n, _⟩ => n.toString escape

@[inline] protected def toStringWithSep (sep : String) (escape := true) : WfName → String
| ⟨n, _⟩ => n.toStringWithSep sep escape

instance : ToString WfName := ⟨(·.toString)⟩

def isPrefixOf : WfName → WfName → Bool
| ⟨n, _⟩, ⟨n', _⟩ => n.isPrefixOf n'

protected def append : WfName → WfName → WfName
| ⟨n, w⟩, ⟨n', w'⟩ => ⟨n.append n', Name.wf_of_append w w'⟩

instance : Append WfName := ⟨WfName.append⟩

def appendName (n : WfName) : Name → WfName
| .anonymous => n
| .str p s _ => mkStr (appendName n p) s
| .num p v _ => mkNum (appendName n p) v

instance : HAppend WfName Name WfName := ⟨appendName⟩

@[inline] protected def hash : WfName → UInt64
| ⟨n, _⟩ => n.hash

instance : Hashable WfName := ⟨WfName.hash⟩

@[inline] protected def beq : WfName → WfName → Bool
| ⟨n, _⟩, ⟨n', _⟩ => n.beq n'

instance : BEq WfName := ⟨WfName.beq⟩

theorem eq_of_beq_true : {n n' : WfName} → (n == n') = true → n = n' := by
  intro ⟨n, w⟩
  simp only [BEq.beq, WfName.beq, Subtype.eq_iff_val_eq]
  induction w with
  | anonymousWff =>
    intro ⟨n', w'⟩; cases w' <;> simp [Name.beq, *]
  | @strWff n p s _ h ih =>
    intro ⟨n', w'⟩
    simp only [Subtype.eq_iff_val_eq]
    cases w' with
    | anonymousWff =>
      simp [Name.mkStr, Name.beq, h]
    | @strWff n' p' s' w' h' =>
      simp only [Name.mkStr, Name.beq, h, h']
      simp only [BEq.beq, Bool.and_eq_true, decide_eq_true_eq]
      intro ⟨s_eq, p_beq⟩
      simp [s_eq, @ih ⟨p', w'⟩ p_beq]
    | @numWff n' p' v' w' h' =>
      simp only [Name.mkNum, Name.beq, h, h']
      exact False.elim
  | @numWff n p v _ h ih =>
    intro ⟨n', w'⟩
    simp only [Subtype.eq_iff_val_eq]
    cases w' with
    | anonymousWff =>
      simp [Name.mkNum, Name.beq, h]
    | @strWff n' p' s' w' h' =>
      simp only [Name.mkNum, Name.beq, h, h']
      exact False.elim
    | @numWff n' p' v' w' h' =>
      simp only [Name.mkNum, Name.beq, h, h']
      simp only [BEq.beq, Bool.and_eq_true, decide_eq_true_eq]
      intro ⟨n_beq, p_beq⟩
      simp [Nat.eq_of_beq_eq_true n_beq, @ih ⟨p', w'⟩ p_beq]

instance : LawfulBEq WfName where
  eq_of_beq := WfName.eq_of_beq_true
  rfl {n} := Name.beq_rfl n

theorem ne_of_beq_false {n n' : WfName} : (n == n') = false → n ≠ n' :=
  _root_.ne_of_beq_false

instance : DecidableEq WfName :=
  fun n n' => match h:WfName.beq n n' with
  | true  => isTrue (eq_of_beq_true h)
  | false => isFalse (ne_of_beq_false h)

@[inline] def quickCmp : WfName → WfName → Ordering
| ⟨n, _⟩, ⟨n', _⟩ => n.quickCmp n'

theorem eq_of_quickCmp :
{n n' : WfName} → quickCmp n n' = Ordering.eq → n = n' := by
  intro ⟨n, w⟩ ⟨n', w'⟩
  simp only [quickCmp, Name.quickCmp, Subtype.eq_iff_val_eq]
  intro h_cmp; split at h_cmp
  next => exact Name.eq_of_wf_quickCmpAux n w n' w' h_cmp
  next => contradiction

instance : EqOfCmp WfName WfName.quickCmp where
  eq_of_cmp h := WfName.eq_of_quickCmp h

open Syntax

def quoteNameFrom (ref : Syntax) : Name → Term
| .anonymous => mkCIdentFrom ref ``anonymous
| .str p s _ => mkApp (mkCIdentFrom ref ``mkStr)
  #[quoteNameFrom ref p, quote s]
| .num p v _ => mkApp (mkCIdentFrom ref ``mkNum)
  #[quoteNameFrom ref p, quote v]

protected def quoteFrom (ref : Syntax) : WfName → Term
| ⟨n, _⟩ => quoteNameFrom ref n

instance : Quote WfName := ⟨WfName.quoteFrom Syntax.missing⟩

end WfName

-- ## Notation

/--
A proven well-formed, unchecked name literal.

Lake augments name literals to produce well-formed names (`WfName`)
instead of their plain counterparts. Well-formed names have additional
properties that help ensure certain features of Lake work as intended.
-/
scoped macro:max (name := wfNameLit) "&" noWs stx:name : term =>
  if let some nm := stx.raw.isNameLit? then
    return WfName.quoteNameFrom stx nm
  else
    Macro.throwErrorAt stx "ill-formed name literal"

scoped notation "&`✝" => WfName.anonymous

@[scoped appUnexpander WfName.mkStr]
def unexpandWfNameMkStr : PrettyPrinter.Unexpander
| `($(_) &`✝ $s) => do
  let some s := s.raw.isStrLit? | throw ()
  let qn := quote (k := `term) <| Name.mkStr Name.anonymous s
  `(&$(⟨qn.raw[0]⟩):name)
| `($(_) &$n:name $s) => do
  let some s := s.raw.isStrLit? | throw ()
  let some n := n.raw.isNameLit? | throw ()
  let qn := quote (k := `term) <| Name.mkStr n s
  `(&$(⟨qn.raw[0]⟩):name)
| _ => throw ()
