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

def elabAttr {m} [Monad m] [MonadEnv m] [MonadError m] (stx : Syntax) : m Attribute := do
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

def elabAttrs {m} [Monad m] [MonadEnv m] [MonadError m] (stx : Syntax) : m (Array Attribute) :=
(stx.getArg 1).foldSepArgsM
  (fun stx attrs => do
    attr ← elabAttr stx;
    pure $ attrs.push attr)
  #[]

def applyAttributesImp (declName : Name) (attrs : Array Attribute) (applicationTime : AttributeApplicationTime) : CoreM Unit :=
attrs.forM $ fun attr => do
 env ← getEnv;
 match getAttributeImpl env attr.name with
 | Except.error errMsg => throwError errMsg
 | Except.ok attrImpl  =>
   when (attrImpl.applicationTime == applicationTime) do
     attrImpl.add declName attr.args true

def applyAttributes {m} [MonadLiftT CoreM m] (declName : Name) (attrs : Array Attribute) (applicationTime : AttributeApplicationTime) : m Unit :=
liftM $ applyAttributesImp declName attrs applicationTime

end Elab
end Lean
