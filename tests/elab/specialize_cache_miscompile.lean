import Lean
open Lean Parser

/-!
This test accounts for a specialisation cache bug that was discovered in the Zulip thread
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Miscompilation.20.28incorrect.20code.29.20in.20new.20compiler/near/540037917
if the bug is around the eval at the end of the file evaluates to true instead of false.
-/

namespace Veil

inductive Mutability where
  | mutable
  | immutable
  | inherit
deriving Inhabited, BEq, Hashable, Repr

inductive StateComponentType where
  | simple (t : TSyntax ``Command.structSimpleBinder)
  | complex (binders : TSyntaxArray ``Term.bracketedBinder) (dom : Term)
deriving Inhabited, BEq

structure StateComponent where
  mutability : Mutability
  name       : Name
  type       : StateComponentType
deriving Inhabited, BEq

structure Module where
  name : Name
  signature : Array StateComponent
deriving Inhabited

end Veil

section Util
set_option autoImplicit true
def getSimpleBinderType [Monad m] [MonadError m] (sig : TSyntax `Lean.Parser.Command.structSimpleBinder) : m (TSyntax `term) := do
  match sig with
  | `(Lean.Parser.Command.structSimpleBinder| $_:ident : $tp:term) => pure tp
  | _ => throwError s!"getSimpleBinderType: don't know how to handle {sig}"

def mkArrowStx [Monad m] [MonadQuotation m] [MonadError m] (tps : List Term) (terminator : Option $ TSyntax `term := none) : m (TSyntax `term) := do
  match tps with
  | [] => if let some t := terminator then return t else throwError "empty list of types and no terminator"
  | [a] => match terminator with
    | none => `(term| $a)
    | some t => `(term| $a -> $t)
  | a :: as =>
    let cont ← mkArrowStx as terminator
    `(term| $a -> $cont)

def complexBinderToSimpleBinder [Monad m] [MonadQuotation m] [MonadError m] (nm : TSyntax `ident) (br : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (domT : TSyntax `term) : m (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let types ← br.mapM fun m => match m with
    | `(bracketedBinder| ($_arg:ident : $tp:term)) => return tp
    | _ => throwError "Invalid binder syntax {br}"
  let typeStx ← mkArrowStx types.toList domT
  let simple ← `(Lean.Parser.Command.structSimpleBinder| $nm:ident : $typeStx)
  return simple
end Util

open Lean Parser Elab Command Term

namespace Veil

instance : ToString Mutability where
  toString
    | Mutability.mutable => "mutable"
    | Mutability.immutable => "immutable"
    | Mutability.inherit => "inherit"

instance : ToString StateComponentType where
  toString
    | StateComponentType.simple t => toString t
    | StateComponentType.complex b d  => s!"{b} : {d}"

instance : ToString StateComponent where
  toString sc := s!"{sc.mutability} {sc.name} {sc.type}"

def StateComponentType.stx [Monad m] [MonadQuotation m] [MonadError m] (sct : StateComponentType) : m (TSyntax `term) := do
  match sct with
  | .simple t => getSimpleBinderType t
  | .complex b d => getSimpleBinderType $ ← complexBinderToSimpleBinder (mkIdent Name.anonymous) b d

/-- Returns, e.g., `initial_msg : address → address → round → value → Prop` -/
def StateComponent.getSimpleBinder [Monad m] [MonadQuotation m] [MonadError m] (sc : StateComponent) : m (TSyntax ``Command.structSimpleBinder) := do
  match sc.type with
  | .simple t => return t
  | .complex b d => return ← complexBinderToSimpleBinder (mkIdent sc.name) b d

def StateComponent.stx {m} [Monad m] [MonadQuotation m] [MonadError m] (sc : StateComponent) : m Syntax := sc.getSimpleBinder
def StateComponent.typeStx [Monad m] [MonadQuotation m] [MonadError m] (sc : StateComponent) : m Term := sc.type.stx

def Module.getTheoryBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .immutable => return .some $ ← `(bracketedBinder| ($(mkIdent sc.name) : $(← sc.typeStx)))
    | _ => pure .none

def Module.getStateBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let res ← mod.signature.filterMapM fun sc => do
    match sc.mutability with
    | .mutable =>
    return .some $ ← `(bracketedBinder| ($(mkIdent sc.name) : $(← sc.typeStx)))
    | _ =>
    -- NOTE 1: uncommenting this line makes `trigger` work correctly
    pure .none
  return res

-- NOTE 2: commenting out this function (or the `trace` statement) makes `trigger` work correctly
def interference (mod : Module) : CommandElabM Unit := do
  trace[veil.debug] "theory binders: {← mod.getTheoryBinders}"
  return

end Veil

namespace Veil

open Lean Parser Elab Command
def trigger : CommandElabM Bool := do
  let sig : Array StateComponent := #[
    { mutability := .mutable, name := `leader, «type» := .simple $ ← `(Command.structSimpleBinder| x : Nat → Bool)},
    { mutability := .mutable, name := `pending, «type» := .simple $ ← `(Command.structSimpleBinder| pending : Nat → Nat → Bool)}
  ]
  let emptyMod : Module := default
  let mod := { emptyMod with signature := sig}
  let binders ← mod.getStateBinders
  return binders.isEmpty

/-- info: false -/
#guard_msgs in
#eval trigger

end Veil

