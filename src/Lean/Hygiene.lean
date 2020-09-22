/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Syntax

namespace Lean
/- Remark: `MonadQuotation` class is part of the `Init` package and loaded by default since it is used in the builtin command `macro`. -/

/-- Simplistic MonadQuotation that does not guarantee globally fresh names, that
    is, between different runs of this or other MonadQuotation implementations.
    It is only safe if the syntax quotations do not introduce bindings around
    antiquotations, and if references to globals are prefixed with `_root_.`
    (which is not allowed to refer to a local variable).

    `Unhygienic` can also be seen as a model implementation of `MonadQuotation`
    (since it is completely hygienic as long as it is "run" only once and can
    assume that there are no other implentations in use, as is the case for the
    elaboration monads that carry their macro scope state through the entire
    processing of a file). It uses the state monad to query and allocate the
    next macro scope, and uses the reader monad to store the stack of scopes
    corresponding to `withFreshMacroScope` calls. -/
abbrev Unhygienic := ReaderT MacroScope $ StateM MacroScope
namespace Unhygienic
instance MonadQuotation : MonadQuotation Unhygienic := {
  getCurrMacroScope   := read,
  getMainModule       := pure `UnhygienicMain,
  withFreshMacroScope := fun α x => do
    fresh ← modifyGet (fun n => (n, n + 1));
    adaptReader (fun _ => fresh) x
}
protected def run {α : Type} (x : Unhygienic α) : α := run x firstFrontendMacroScope (firstFrontendMacroScope+1)
end Unhygienic

private def mkInaccessibleUserNameAux (unicode : Bool) (name : Name) (idx : Nat) : Name :=
if unicode then
  if idx == 0 then
    name.appendAfter "✝"
  else
    name.appendAfter ("✝" ++ idx.toSuperscriptString)
else
  name ++ mkNameNum "_inaccessible" idx

private def mkInaccessibleUserName (unicode : Bool) : Name → Name
| Name.num p@(Name.str _ _ _) idx _ =>
  mkInaccessibleUserNameAux unicode p idx
| Name.num Name.anonymous idx _     =>
  mkInaccessibleUserNameAux unicode Name.anonymous idx
| Name.num p idx _ =>
  if unicode then
    (mkInaccessibleUserName p).appendAfter ("⁻" ++ idx.toSuperscriptString)
  else
    mkNameNum (mkInaccessibleUserName p) idx
| n => n

@[export lean_is_inaccessible_user_name]
def isInaccessibleUserName : Name → Bool
| Name.str _ s _   => s.contains '✝' || s == "_inaccessible"
| Name.num p idx _ => isInaccessibleUserName p
| _                => false

def sanitizeNamesDefault := true
@[init] def sanitizeNamesOption : IO Unit :=
registerOption `pp.sanitizeNames { defValue := sanitizeNamesDefault, group := "pp", descr := "add suffix '_{<idx>}' to shadowed/inaccessible variables when pretty printing" }
def getSanitizeNames (o : Options) : Bool:= o.get `pp.sanitizeNames sanitizeNamesDefault

structure NameSanitizerState :=
(options            : Options)
-- `x` ~> 2 if we're already using `x✝`, `x✝¹`
(nameStem2Idx       : NameMap Nat := {})
-- `x._hyg...` ~> `x✝`
(userName2Sanitized : NameMap Name := {})

private partial def mkFreshInaccessibleUserName (userName : Name) : Nat → StateM NameSanitizerState Name
| idx => do
  st ← get;
  let userNameNew := mkInaccessibleUserName (Format.getUnicode st.options) (mkNameNum userName idx);
  if st.nameStem2Idx.contains userNameNew then
    mkFreshInaccessibleUserName (idx+1)
  else do
    modify fun st => { st with nameStem2Idx := st.nameStem2Idx.insert userName (idx+1) };
    pure userNameNew

def sanitizeName (userName : Name) : StateM NameSanitizerState Name := do
st ← get;
let stem := userName.eraseMacroScopes;
let idx  := (st.nameStem2Idx.find? stem).getD 0;
san ← mkFreshInaccessibleUserName stem idx;
modify fun st => { st with userName2Sanitized := st.userName2Sanitized.insert userName san };
pure san

private partial def sanitizeSyntaxAux : Syntax → StateM NameSanitizerState Syntax
| Syntax.ident _ _ n _ => do
  st ← get;
  mkIdent <$> match st.userName2Sanitized.find? n with
  | some n' => pure n'
  | none    => if n.hasMacroScopes then sanitizeName n else pure n
| Syntax.node k args => Syntax.node k <$> args.mapM sanitizeSyntaxAux
| stx => pure stx

def sanitizeSyntax (stx : Syntax) : StateM NameSanitizerState Syntax := do
st ← get;
if getSanitizeNames st.options then
  sanitizeSyntaxAux stx
else
  pure stx

end Lean
