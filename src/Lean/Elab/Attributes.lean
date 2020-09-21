/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Basic
import Lean.Attributes
import Lean.MonadEnv

namespace Lean
namespace Elab

structure Attribute :=
(name : Name) (args : Syntax := Syntax.missing)

instance Attribute.hasFormat : HasFormat Attribute :=
⟨fun attr => Format.bracket "@[" (toString attr.name ++ (if attr.args.isMissing then "" else toString attr.args)) "]"⟩

instance Attribute.inhabited : Inhabited Attribute := ⟨{ name := arbitrary _ }⟩

def elabAttr {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (stx : Syntax) : m Attribute := do
-- rawIdent >> many attrArg
let nameStx := stx.getArg 0;
attrName ← match nameStx.isIdOrAtom? with
  | none     => withRef nameStx $ throwError "identifier expected"
  | some str => pure $ mkNameSimple str;
env ← getEnv;
unless (isAttribute env attrName) $
  throwError ("unknown attribute [" ++ attrName ++ "]");
let args := stx.getArg 1;
-- the old frontend passes Syntax.missing for empty args, for reasons
let args := if args.getNumArgs == 0 then Syntax.missing else args;
pure { name := attrName, args := args }

-- sepBy1 attrInstance ", "
def elabAttrs {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (stx : Syntax) : m (Array Attribute) :=
stx.foldSepArgsM
  (fun stx attrs => do
    attr ← elabAttr stx;
    pure $ attrs.push attr)
  #[]

-- parser! "@[" >> sepBy1 attrInstance ", " >> "]"
def elabDeclAttrs {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (stx : Syntax) : m (Array Attribute) :=
elabAttrs (stx.getArg 1)

end Elab
end Lean
