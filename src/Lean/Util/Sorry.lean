/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Message
import Lean.Exception

namespace Lean

def Expr.isSorry : Expr → Bool
  | Expr.app (Expr.app (Expr.const `sorryAx _ _) _ _) _ _ => true
  | _ => false

def Expr.isSyntheticSorry : Expr → Bool
  | Expr.app (Expr.app (Expr.const `sorryAx _ _) _ _) (Expr.const `Bool.true _ _) _ => true
  | _ => false

def Expr.hasSorry : Expr → Bool
  | Expr.const c _ _     => c == `sorryAx
  | Expr.app f a _       => f.hasSorry || a.hasSorry
  | Expr.letE _ t v b _  => t.hasSorry || v.hasSorry || b.hasSorry
  | Expr.forallE _ d b _ => d.hasSorry || b.hasSorry
  | Expr.lam _ d b _     => d.hasSorry || b.hasSorry
  | Expr.mdata _ e _     => e.hasSorry
  | Expr.proj _ _ e _    => e.hasSorry
  | _                    => false

def Expr.hasSyntheticSorry : Expr → Bool
  | e@(Expr.app f a _)   => e.isSyntheticSorry  || f.hasSyntheticSorry || a.hasSyntheticSorry
  | Expr.letE _ t v b _  => t.hasSyntheticSorry || v.hasSyntheticSorry || b.hasSyntheticSorry
  | Expr.forallE _ d b _ => d.hasSyntheticSorry || b.hasSyntheticSorry
  | Expr.lam _ d b _     => d.hasSyntheticSorry || b.hasSyntheticSorry
  | Expr.mdata _ e _     => e.hasSyntheticSorry
  | Expr.proj _ _ e _    => e.hasSyntheticSorry
  | _                    => false

partial def MessageData.hasSorry : MessageData → Bool
  | MessageData.ofExpr e          => e.hasSorry
  | MessageData.withContext _ msg => msg.hasSorry
  | MessageData.nest _ msg        => msg.hasSorry
  | MessageData.group msg         => msg.hasSorry
  | MessageData.compose msg₁ msg₂ => msg₁.hasSorry || msg₂.hasSorry
  | MessageData.tagged _ msg      => msg.hasSorry
  | MessageData.node msgs         => msgs.any hasSorry
  | _                             => false

partial def MessageData.hasSyntheticSorry (msg : MessageData) : Bool :=
  visit msg.instantiateMVars
where
  visit : MessageData → Bool
  | MessageData.ofExpr e                => e.hasSyntheticSorry
  | MessageData.withContext _ msg       => visit msg
  | MessageData.withNamingContext _ msg => visit msg
  | MessageData.nest _ msg              => visit msg
  | MessageData.group msg               => visit msg
  | MessageData.compose msg₁ msg₂       => visit msg₁ || visit msg₂
  | MessageData.tagged _ msg            => visit msg
  | MessageData.node msgs               => msgs.any hasSyntheticSorry
  | _                                   => false

def Exception.hasSyntheticSorry : Exception → Bool
  | Exception.error _ msg => msg.hasSyntheticSorry
  | _                     => false

end Lean
