module

public meta import Lean

open Lean Doc Elab Command
open scoped Lean.Doc.Syntax

public section

/-! Defines a docstring role that includes another declaration's docstring at render time. -/

/-- A request to include another declaration's docstring. -/
meta structure IncludeDoc where
  /-- The declaration whose docstring should be included. -/
  target : Name
deriving TypeName

/-- Reads a single code inline and resolves it to a global constant. -/
meta def codeTargetName (xs : TSyntaxArray `inline) : DocM Name :=
  match xs with
  | #[stx] => match stx with
    | `(inline|code($s)) => realizeGlobalConstNoOverloadWithInfo (mkIdentFrom s s.getString.toName)
    | _ => throwErrorAt stx "expected a code argument"
  | _ => throwError "expected one code argument"

/-- Includes another declaration's docstring. The target is looked up when rendering to Markdown. -/
@[doc_role]
meta def include_docstring (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .other { val := .mk (IncludeDoc.mk (← codeTargetName xs)) } #[]

/-- The renderer looks up and renders the target's docstring when the including docstring is shown. -/
@[doc_inline_md]
meta def includeRender : InlineMdRendererOf IncludeDoc := fun _go data _content => do
  match (← (findInternalDocString? (← (getEnv : CoreM _)) data.target : IO _)) with
  | some (.inl str) => return ((str.split '\n').map (·.copy)).toArray
  | some (.inr verso) => ToMarkdown.toMarkdown verso
  | none => return #[]
