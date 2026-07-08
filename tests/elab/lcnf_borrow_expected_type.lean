module

public section

/-!
Tests that borrow annotations from declaration/let-binding types survive LCNF conversion.
The `@&` annotations live in the forall type, not in the lambda binders, and are based on the
(rather brittle) mdata so LCNF must infer them to a degree.
-/

/--
trace: [Compiler.saveBase] size: 1
    def borrowTop @&xs : Nat :=
      let _x.1 := @List.lengthTR _ xs;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def borrowTop (xs : @& List Nat) : Nat := xs.length

/--
trace: [Compiler.saveBase] size: 3
    def borrowMixed n @&xs m : Nat :=
      let _x.1 := @List.lengthTR _ xs;
      let _x.2 := Nat.add n _x.1;
      let _x.3 := Nat.add _x.2 m;
      return _x.3
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def borrowMixed (n : Nat) (xs : @& List Nat) (m : Nat) : Nat :=
  n + xs.length + m

/--
trace: [Compiler.saveBase] size: 5
    def borrowLet n xs ys : Nat :=
      fun f @&ys : Nat :=
        let _x.1 := @List.lengthTR _ ys;
        let _x.2 := Nat.add _x.1 n;
        return _x.2;
      let _x.3 := f xs;
      let _x.4 := f ys;
      let _x.5 := Nat.add _x.3 _x.4;
      return _x.5
[Compiler.lambdaLifting] size: 2
    def borrowLet._lam_0 n @&ys : Nat :=
      let _x.1 := List.lengthTR._redArg ys;
      let _x.2 := Nat.add _x.1 n;
      return _x.2
[Compiler.lambdaLifting] size: 4
    def borrowLet n xs ys : Nat :=
      let f := borrowLet._lam_0 n;
      let _x.1 := f xs;
      let _x.2 := f ys;
      let _x.3 := Nat.add _x.1 _x.2;
      return _x.3
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
set_option trace.Compiler.lambdaLifting true in
def borrowLet (n : Nat) (xs ys : List Nat) : Nat :=
  let f : (@& List Nat) → Nat := fun ys => ys.length + n
  f xs + f ys

/--
trace: [Compiler.saveBase] size: 2
    def applyTwice f @&a.1 : Nat :=
      let _x.2 := f a.1;
      let _x.3 := f _x.2;
      return _x.3
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def applyTwice (f : Nat → Nat) : (@& Nat) → Nat :=
  let g := f ∘ f
  g

structure Ctx where
  values : List Nat

abbrev MyReaderM (α : Type) := (@& Ctx) → α

@[inline]
def MyReaderM.bind (f : MyReaderM α) (g : α → MyReaderM β) : MyReaderM β :=
  fun ctx => g (f ctx) ctx

instance : Monad MyReaderM where
  pure a := fun _ => a
  bind := MyReaderM.bind

@[inline] def MyReaderM.read : MyReaderM Ctx := fun ctx => ctx

/--
trace: [Compiler.saveBase] size: 2
    def withMyReader α f x @&ctx : α :=
      let _x.1 := f ctx;
      let _x.2 := x _x.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
@[noinline]
def withMyReader (f : Ctx → Ctx) (x : MyReaderM α) : MyReaderM α :=
  fun ctx => x (f ctx)

/--
trace: [Compiler.saveBase] size: 6
    def getLength other @&a.1 : Nat :=
      fun _f.2 ctx : Ctx :=
        let _x.3 := ctx # 0;
        let _x.4 := @List.appendTR _ _x.3 other;
        let _x.5 := Ctx.mk _x.4;
        return _x.5;
      fun _f.6 _y.7 : Nat :=
        let _x.8 := _y.7 # 0;
        let _x.9 := @List.lengthTR _ _x.8;
        return _x.9;
      let _x.10 := @withMyReader _ _f.2 _f.6 a.1;
      return _x.10
-/
#guard_msgs in
set_option trace.Compiler.saveBase true in
def getLength (other : List Nat) : MyReaderM Nat := do
  withMyReader (fun ctx => { ctx with values := ctx.values ++ other }) do
    let ctx ← MyReaderM.read
    return ctx.values.length

structure Pair where
  fst : List Nat
  snd : List Nat

structure Quad where
  left : Pair
  right : Pair

/-- Packs `xs` into a constructor → parameter inferred as owned. -/
@[noinline] def wrap (xs : List Nat) : List (List Nat) := [xs]

/-- Only traverses → parameter stays borrowed. -/
@[noinline] def measuree (xs : List Nat) : Nat := xs.length

/--
trace: [Compiler.explicitRc] size: 22
    def cascadeDemo @&t : tobj :=
      let left := oproj[0] t;
      let right := oproj[1] t;
      let fst := oproj[0] left;
      let snd := oproj[1] left;
      let fst := oproj[0] right;
      let snd := oproj[1] right;
      inc fst;
      let _x.1 := wrap fst;
      let res := List.lengthTR._redArg _x.1;
      dec _x.1;
      let _x.2 := measuree snd;
      let _x.3 := Nat.add res _x.2;
      dec _x.2;
      dec res;
      let _x.4 := measuree fst;
      let _x.5 := Nat.add _x.3 _x.4;
      dec _x.4;
      dec _x.3;
      let _x.6 := measuree snd;
      let _x.7 := Nat.add _x.5 _x.6;
      dec _x.6;
      dec _x.5;
      return _x.7
[Compiler.explicitRc] size: 2
    def cascadeDemo._boxed t : tobj :=
      let res := cascadeDemo t;
      dec[ref] t;
      return res
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def cascadeDemo (t : @&Quad) : Nat :=
  let l := t.left
  let r := t.right
  let res := (wrap l.fst).length
  res + measuree l.snd + measuree r.fst + measuree r.snd

/--
trace: [Compiler.explicitRc] size: 33
    def cascadeDemo' t : tobj :=
      let left := oproj[0] t;
      inc[ref] left;
      let right := oproj[1] t;
      inc[ref] right;
      dec[ref] t;
      let fst := oproj[0] left;
      inc fst;
      let snd := oproj[1] left;
      inc snd;
      dec[ref] left;
      let fst := oproj[0] right;
      inc fst;
      let snd := oproj[1] right;
      inc snd;
      dec[ref] right;
      let _x.1 := wrap fst;
      let res := List.lengthTR._redArg _x.1;
      dec _x.1;
      let _x.2 := measuree snd;
      dec snd;
      let _x.3 := Nat.add res _x.2;
      dec _x.2;
      dec res;
      let _x.4 := measuree fst;
      dec fst;
      let _x.5 := Nat.add _x.3 _x.4;
      dec _x.4;
      dec _x.3;
      let _x.6 := measuree snd;
      dec snd;
      let _x.7 := Nat.add _x.5 _x.6;
      dec _x.6;
      dec _x.5;
      return _x.7
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def cascadeDemo' (t : Quad) : Nat :=
  let l := t.left
  let r := t.right
  let res := (wrap l.fst).length
  res + measuree l.snd + measuree r.fst + measuree r.snd

@[noinline]
public def mkNewProd (x : Prod Nat Nat) (a : Nat) := { x with fst := a }

/--
trace: [Compiler.explicitRc] size: 15
    def preserveTailCall x a : tobj :=
      let zero := 0;
      let isZero := Nat.decEq a zero;
      cases isZero : tobj
      | Bool.true =>
        dec a;
        let fst := oproj[0] x;
        inc fst;
        dec[ref] x;
        return fst
      | Bool.false =>
        let one := 1;
        let n.1 := Nat.sub a one;
        dec a;
        inc n.1;
        let _x.2 := mkNewProd x n.1;
        let _x.3 := preserveTailCall _x.2 n.1;
        return _x.3
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def preserveTailCall (x : @&Prod Nat Nat) (a : Nat) : Nat :=
  match a with
  | 0 => x.fst
  | a + 1 => preserveTailCall (mkNewProd x a) a
