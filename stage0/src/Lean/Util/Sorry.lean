/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Message
import Lean.Exception
import Lean.Util.FindExpr

namespace Lean

def Expr.isSorry : Expr → Bool
  | app (app (.const ``sorryAx ..) ..) .. => true
  | _ => false

def Expr.isSyntheticSorry : Expr → Bool
  | app (app (const ``sorryAx ..) ..) (const ``Bool.true ..) _ => true
  | _ => false

def Expr.isNonSyntheticSorry : Expr → Bool
  | app (app (const ``sorryAx ..) ..) (const ``Bool.false ..) _ => true
  | _ => false

def Expr.hasSorry (e : Expr) : Bool :=
  Option.isSome <| e.find? (·.isConstOf ``sorryAx)

def Expr.hasSyntheticSorry (e : Expr) : Bool :=
  Option.isSome <| e.find? (·.isSyntheticSorry)

def Expr.hasNonSyntheticSorry (e : Expr) : Bool :=
  Option.isSome <| e.find? (·.isNonSyntheticSorry)

partial def MessageData.hasSorry : MessageData → Bool
  | ofExpr e          => e.hasSorry
  | withContext _ msg => msg.hasSorry
  | nest _ msg        => msg.hasSorry
  | group msg         => msg.hasSorry
  | compose msg₁ msg₂ => msg₁.hasSorry || msg₂.hasSorry
  | tagged _ msg      => msg.hasSorry
  | node msgs         => msgs.any hasSorry
  | _                 => false

partial def MessageData.hasSyntheticSorry (msg : MessageData) : Bool :=
  visit msg.instantiateMVars
where
  visit : MessageData → Bool
  | ofExpr e                => e.hasSyntheticSorry
  | withContext _ msg       => visit msg
  | withNamingContext _ msg => visit msg
  | nest _ msg              => visit msg
  | group msg               => visit msg
  | compose msg₁ msg₂       => visit msg₁ || visit msg₂
  | tagged _ msg            => visit msg
  | node msgs               => msgs.any hasSyntheticSorry
  | _                       => false

def Exception.hasSyntheticSorry : Exception → Bool
  | Exception.error _ msg => msg.hasSyntheticSorry
  | _                     => false

def Declaration.hasSorry (d : Declaration) : Bool := Id.run do
  d.foldExprM (fun r e => r || e.hasSorry) false

def Declaration.hasNonSyntheticSorry (d : Declaration) : Bool := Id.run do
  d.foldExprM (fun r e => r || e.hasNonSyntheticSorry) false

end Lean
