/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean.Meta

namespace SortLocalDecls

structure Context where
  localDecls : NameMap LocalDecl := {}

structure State where
  visited : NameSet := {}
  result  : Array LocalDecl := #[]

abbrev M := ReaderT Context $ StateRefT State MetaM

mutual
  partial def visitExpr (e : Expr) : M Unit := do
    match e with
    | Expr.proj _ _ e _    => visitExpr e
    | Expr.forallE _ d b _ => visitExpr d; visitExpr b
    | Expr.lam _ d b _     => visitExpr d; visitExpr b
    | Expr.letE _ t v b _  => visitExpr t; visitExpr v; visitExpr b
    | Expr.app f a _       => visitExpr f; visitExpr a
    | Expr.mdata _ b _     => visitExpr b
    | Expr.mvar _ _        => let v ← instantiateMVars e; unless v.isMVar do visitExpr v
    | Expr.fvar fvarId _   => if let some localDecl := (← read).localDecls.find? fvarId.name then visitLocalDecl localDecl
    | _                    => return ()

  partial def visitLocalDecl (localDecl : LocalDecl) : M Unit := do
    unless (← get).visited.contains localDecl.fvarId.name do
      modify fun s => { s with visited := s.visited.insert localDecl.fvarId.name }
      visitExpr localDecl.type
      if let some val := localDecl.value? then
        visitExpr val
      modify fun s => { s with result := s.result.push localDecl }
end

end SortLocalDecls

open SortLocalDecls in
def sortLocalDecls (localDecls : Array LocalDecl) : MetaM (Array LocalDecl) :=
  let aux : M (Array LocalDecl) := do localDecls.forM visitLocalDecl; return (← get).result
  aux.run { localDecls := localDecls.foldl (init := {}) fun s d => s.insert d.fvarId.name d } |>.run' {}

end Lean.Meta
