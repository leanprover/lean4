import Lean

namespace Lean
namespace Expr

namespace ReplaceImpl'

abbrev cacheSize : USize := 8192

structure State where
  keys    : Array Expr -- Remark: our "unsafe" implementation relies on the fact that `()` is not a valid Expr
  results : Array Expr

abbrev ReplaceM := StateM State

unsafe def cache (i : USize) (key : Expr) (result : Expr) : ReplaceM Expr := do
  modify fun ⟨keys, results⟩ => { keys := keys.uset i key lcProof, results := results.uset i result lcProof };
  pure result

unsafe def replaceUnsafeM (size : USize) (e : Expr) (f? : (e' : Expr) → sizeOf e' ≤ sizeOf e → Option Expr) : ReplaceM Expr := do
  let rec visit (e : Expr) := do
    let c ← get
    let h := ptrAddrUnsafe e
    let i := h % size
    if ptrAddrUnsafe (c.keys.uget i lcProof) == h then
      pure <| c.results.uget i lcProof
    else match f? e lcProof with
      | some eNew => cache i e eNew
      | none      => match e with
        | Expr.forallE _ d b _   => cache i e <| e.updateForallE! (← visit d) (← visit b)
        | Expr.lam _ d b _       => cache i e <| e.updateLambdaE! (← visit d) (← visit b)
        | Expr.mdata _ b         => cache i e <| e.updateMData! (← visit b)
        | Expr.letE _ t v b _    => cache i e <| e.updateLet! (← visit t) (← visit v) (← visit b)
        | Expr.app f a           => cache i e <| e.updateApp! (← visit f) (← visit a)
        | Expr.proj _ _ b        => cache i e <| e.updateProj! (← visit b)
        | e                      => pure e
  visit e

unsafe def initCache : State :=
  { keys    := mkArray cacheSize.toNat (cast lcProof ()), -- `()` is not a valid `Expr`
    results := mkArray cacheSize.toNat default }

unsafe def replaceUnsafe (e : Expr) (f? : (e' : Expr) → sizeOf e' ≤ sizeOf e → Option Expr) : Expr :=
  (replaceUnsafeM cacheSize e f?).run' initCache

end ReplaceImpl'


local macro "dec " h:ident : term => `(by apply Nat.le_trans _ $h; simp +arith)

@[implemented_by ReplaceImpl'.replaceUnsafe]
def replace' (e0 : Expr) (f? : (e : Expr) → sizeOf e ≤ sizeOf e0 → Option Expr) : Expr :=
  let rec go (e : Expr) (h : sizeOf e ≤ sizeOf e0) : Expr :=
    match f? e h with
    | some eNew => eNew
    | none      => match e with
      | Expr.forallE _ d b _   => let d := go d (dec h); let b := go b (dec h); e.updateForallE! d b
      | Expr.lam _ d b _       => let d := go d (dec h); let b := go b (dec h); e.updateLambdaE! d b
      | Expr.mdata _ b         => let b := go b (dec h); e.updateMData! b
      | Expr.letE _ t v b _    => let t := go t (dec h); let v := go v (dec h); let b := go b (dec h); e.updateLet! t v b
      | Expr.app f a           => let f := go f (dec h); let a := go a (dec h); e.updateApp! f a
      | Expr.proj _ _ b        => let b := go b (dec h); e.updateProj! b
      | e                      => e
  go e0 (Nat.le_refl ..)
end Expr
end Lean

open Lean

def addDecorations (e : Expr) : Expr :=
  e.replace' fun expr h =>
    match expr with
    | Expr.forallE name type body data =>
      let n := name.toString
      let newType := addDecorations type
      let newBody := addDecorations body
      let rest := Expr.forallE name newType newBody data
      some <| mkApp2 (mkConst `SlimCheck.NamedBinder) (mkStrLit n) rest
    | _ => none
decreasing_by all_goals exact Nat.le_trans (by simp +arith) h
