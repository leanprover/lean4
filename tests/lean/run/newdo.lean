import Lean
import Lean.Parser.Term.Basic
import Lean.Elab.Tactic.Do.LetElim
import Std.Tactic.Do
import Init.Control.OptionCps
import Init.Control.StateCps
import Lean.Elab.Do.Control
import Lean.Elab.BuiltinDo
import Lean.Parser.Term

open Lean Parser Meta Elab Do

set_option linter.unusedVariables false

set_option pp.all true in
@[inline]
def ForInNew.forInInv {m} {ρ : Type u} {α : Type v} [ForInNew m ρ α] {σ γ}
    (xs : ρ) (s : σ) (kcons : α → (σ → m γ) → σ → m γ) (knil : σ → m γ)
    [Monad m] [inst : ForInNew.{u,v,v,v} Id ρ α] {ps} [Std.Do.WP m ps] (inv : Std.Do.Invariant (inst.toList xs) σ ps) : m γ :=
  forIn xs s kcons knil

meta def doInvariant := leading_parser
  "invariant " >> withPosition (
    ppGroup (many1 (ppSpace >> termParser argPrec) >> unicodeSymbol " ↦" " =>" (preserveForPP := true)) >> ppSpace >> withForbidden "do" termParser)
syntax (name := doForInvariant) "for " Term.doForDecl ppSpace doInvariant "do " doSeq : doElem

namespace Do

elab_rules : doElem <= dec
  | `(doElem| for $x:ident in $xs invariant $cursorBinder $stateBinders* => $body do $doSeq) => do
    --trace[Elab.do] "cursorBinder: {cursorBinder}"
    let call ← elabDoElem (← `(doElem| for $x:ident in $xs do $doSeq)) dec
    let_expr ForInNew.forIn m ρ α instForIn σ γ xs s kcons knil := call
      | throwError "Internal elaboration error: `for` loop did not elaborate to a call of `Foldable.foldr`."
    call.withApp fun head args => do
    let [u, v, w, x] := head.constLevels!
      | throwError "`Foldable.foldrEta` had wrong number of levels {head.constLevels!}"
    let mi := (← read).monadInfo
    unless ← isLevelDefEq mi.u (mkLevelMax v w) do
      throwError "The universe level of the monadic result type {mi.u} was not the maximum of that of the state tuple {w} and elements {v}. Cannot elaborate invariants for this case."
    unless ← isLevelDefEq mi.v x do
      throwError "The universe level of the result type {mi.v} and that of the continuation result type {x} were different. Cannot elaborate invariants for this case."
    -- First the non-ghost arguments
    let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
    let app := mkConst ``ForInNew.forInInv [u, v, w, x]
    let app := mkApp6 app m ρ α instForIn σ γ
    let app := mkApp4 app xs s kcons knil
    -- Now the ghost arguments
    let instForIn ← Term.mkInstMVar (mkApp3 (mkConst ``ForInNew [u, v, v, v]) (mkConst ``Id [v]) ρ α)
    let ps ← mkFreshExprMVar (mkConst ``Std.Do.PostShape [mi.u])
    let instWP ← Term.mkInstMVar (mkApp2 (mkConst ``Std.Do.WP [mi.u, mi.v]) (← read).monadInfo.m ps)
    let xsToList := mkApp4 (mkConst ``ForInNew.toList [u, v]) ρ α instForIn xs
    let cursor := mkApp2 (mkConst ``List.Cursor [v]) α xsToList
    let assertion := mkApp (mkConst ``Std.Do.Assertion [mi.u]) ps
    let mutVarsTuple ← Term.exprToSyntax s
    let cursorσ := mkApp2 (mkConst ``Prod [v, mi.u]) cursor σ
    let success ← Term.elabFun (← `(fun ($cursorBinder, $mutVarsTuple) $stateBinders* => $body)) (← mkArrow cursorσ assertion)
    let inv := mkApp3 (mkConst ``Std.Do.PostCond.noThrow [mkLevelMax v mi.u]) ps cursorσ success
    return mkApp5 app instMonad instForIn ps instWP inv

#check doo return 42
set_option trace.Elab.do true in
-- set_option trace.Meta.isDefEq true in
set_option trace.Meta.isDefEq.assign true in
#check Id.run (α := Nat) doo
  let mut x := 42
  return x
set_option trace.Elab.do true in
set_option pp.raw false in
#check Id.run (α := Nat) doo
  let mut x ← pure 42
  let y ←
    if true then
      pure 42
    else
      pure 31
  x := x + y
  return x
set_option pp.mvars.delayed false in
set_option trace.Meta.synthInstance true in
set_option trace.Elab.step false in
set_option trace.Elab.do true in
set_option trace.Elab.postpone true in
set_option pp.raw false in
#check doo return 42
#check doo pure (); return 42
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
#check doo let mut x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
#check doo let x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
set_option trace.Elab.do true in
#check Id.run <| ExceptT.run doo
  let e ← try
      let x := 0
      throw "error"
    catch e : String =>
      pure e
  return e

set_option trace.Meta.isDefEq true in
#check fun e => Id.run doo
  let mut x := 0
  let y := 3
  let z ← do
    let mut y ← e
    x := y + 1
    pure y
  let y := y + 3
  pure (x + y + z)

set_option trace.Compiler.saveBase true in
set_option trace.Compiler.specialize.step true in
set_option trace.Elab.do true in
#eval Id.run doo
  let mut x := 42
  for i in [1,2,3] do
    for j in [i:10].toList do
      x := x + i + j
  return x

set_option trace.Elab.do true in
/--
trace: [Elab.do] let x := 1;
    have kbreak := fun s =>
      let x := s;
      pure x;
    ForInNew.forIn [1, 2, 3] x
      (fun i kcontinue s =>
        let x := s;
        have kbreak_1 := fun s_1 =>
          let x_1 := s_1;
          if x_1 > 20 then kbreak x_1 else kcontinue x_1;
        ForInNew.forIn [4, 5, 6] x
          (fun j kcontinue_1 s_1 =>
            let x_1 := s_1;
            have __do_jp := fun x_2 r =>
              if j < 3 then kcontinue_1 x_2 else if j > 6 then kbreak_1 x_2 else kcontinue_1 x_2;
            if j < 5 then
              let x := x_1 + j;
              __do_jp x PUnit.unit
            else __do_jp x_1 PUnit.unit)
          kbreak_1)
      kbreak
-/
#guard_msgs in
example := Id.run doo
  let mut x := 1
  for i in [1,2,3] do
    for j in [4,5,6] do
      if j < 5 then x := x + j
      if j < 3 then continue
      if j > 6 then break
    if x > 20 then break
  return x

set_option trace.Compiler.saveBase true in
set_option trace.Elab.do true in
#eval Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      z := z + i
  return x + y + z

/--
info: (let x := 42;
  let y := 0;
  let z := 1;
  ForInNew.forIn [1, 2, 3] (x, z)
    (fun i kcontinue s =>
      let x := s.fst;
      let z := s.snd;
      let x_1 := x + i;
      have __do_jp := fun z r =>
        let z := z + i;
        kcontinue (x_1, z);
      if x_1 > 10 then
        let z := z + i;
        __do_jp z PUnit.unit
      else __do_jp z PUnit.unit)
    fun s =>
    let x := s.fst;
    let z := s.snd;
    pure (x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check (Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    if x > 10 then z := z + i
    z := z + i
  return x + y + z)

-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.isDefEq.delta true in
-- set_option trace.Meta.isDefEq.assign true in
-- set_option trace.Elab.do true in
/--
info: (let w := 23;
  let x := 42;
  let y := 0;
  let z := 1;
  have kbreak := fun s =>
    let x := s.fst;
    let s := s.snd;
    let y := s.fst;
    let z := s.snd;
    pure (w + x + y + z);
  ForInNew.forIn [1, 2, 3] (x, y, z)
    (fun i kcontinue s =>
      let x := s.fst;
      let s := s.snd;
      let y := s.fst;
      let z := s.snd;
      if x < 20 then
        let y := y - 2;
        kbreak (x, y, z)
      else
        have __do_jp := fun z r =>
          if x > 10 then
            let x := x + 3;
            kcontinue (x, y, z)
          else
            let x := x + i;
            kcontinue (x, y, z);
        if x = 3 then
          let z := z + i;
          __do_jp z PUnit.unit
        else __do_jp z PUnit.unit)
    kbreak).run : Nat
-/
#guard_msgs (info) in
#check Id.run doo
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 44
    def List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 w l b : Nat :=
      jp _jp.3 s.4 : Nat :=
        let x := s.4 # 0;
        let s.5 := s.4 # 1;
        let y := s.5 # 0;
        let z := s.5 # 1;
        let _x.6 := Nat.add w x;
        let _x.7 := Nat.add _x.6 y;
        let _x.8 := Nat.add _x.7 z;
        return _x.8;
      cases l : Nat
      | List.nil =>
        goto _jp.3 b
      | List.cons head.9 tail.10 =>
        let x := b # 0;
        let s.11 := b # 1;
        let y := s.11 # 0;
        jp _jp.12 z : Nat :=
          let _x.13 := 10;
          let _x.14 := Nat.decLt _x.13 x;
          cases _x.14 : Nat
          | Decidable.isFalse x.15 =>
            let x := Nat.add x head.9;
            let _x.16 := @Prod.mk _ _ y z;
            let _x.17 := @Prod.mk _ _ x _x.16;
            let _x.18 := List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 w tail.10 _x.17;
            return _x.18
          | Decidable.isTrue x.19 =>
            let x := Nat.add x _x.1;
            let _x.20 := @Prod.mk _ _ y z;
            let _x.21 := @Prod.mk _ _ x _x.20;
            let _x.22 := List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 w tail.10 _x.21;
            return _x.22;
        let z := s.11 # 1;
        let _x.23 := 20;
        let _x.24 := Nat.decLt x _x.23;
        cases _x.24 : Nat
        | Decidable.isFalse x.25 =>
          let _x.26 := instDecidableEqNat x _x.1;
          cases _x.26 : Nat
          | Decidable.isFalse x.27 =>
            goto _jp.12 z
          | Decidable.isTrue x.28 =>
            let z := Nat.add z head.9;
            goto _jp.12 z
        | Decidable.isTrue x.29 =>
          let y := Nat.sub y _x.2;
          let _x.30 := @Prod.mk _ _ y z;
          let _x.31 := @Prod.mk _ _ x _x.30;
          goto _jp.3 _x.31
[Compiler.saveBase] size: 13
    def Do._example : Nat :=
      let w := 23;
      let x := 42;
      let y := 0;
      let z := 1;
      let _x.1 := 2;
      let _x.2 := 3;
      let _x.3 := @List.nil _;
      let _x.4 := @List.cons _ _x.2 _x.3;
      let _x.5 := @List.cons _ _x.1 _x.4;
      let _x.6 := @List.cons _ z _x.5;
      let _x.7 := @Prod.mk _ _ y z;
      let _x.8 := @Prod.mk _ _ x _x.7;
      let _x.9 := List.newForIn._at_.Do._example.spec_0 _x.2 _x.1 w _x.6 _x.8;
      return _x.9
-/
#guard_msgs in
example := Id.run doo
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z

set_option trace.Elab.do true in
/--
trace: [Elab.do] let x := 42;
    let y := 0;
    have kbreak := fun s =>
      let x := s;
      pure (x + x + x + x);
    ForInNew.forIn [1, 2, 3] x
      (fun i kcontinue s =>
        let x := s;
        have __do_jp := fun x_1 r =>
          if x_1 > 10 then
            let x := x_1 + 3;
            kcontinue x
          else
            if x_1 < 20 then
              let x := x_1 - 2;
              kbreak x
            else
              let x := x_1 + i;
              kcontinue x;
        if x = 3 then
          let x := x + 1;
          __do_jp x PUnit.unit
        else __do_jp x PUnit.unit)
      kbreak
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  let mut y := 0
  for i in [1,2,3] do
    if x = 3 then x := x + 1
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x - 2; break
    x := x + i
  return x + x + x + x

/--
info: (let w := 23;
  let x := 42;
  let y := 0;
  let z := 1;
  do
  let r ←
    forIn [1, 2, 3] ⟨x, y, z⟩ fun i r =>
        let x := r.fst;
        let x_1 := r.snd;
        let y := x_1.fst;
        let z := x_1.snd;
        let __do_jp := fun x y z y_1 =>
          let __do_jp := fun x z y_2 =>
            let __do_jp := fun x y_3 =>
              let x := x + i;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨x, y, z⟩);
            if x > 10 then
              let x := x + 3;
              pure (ForInStep.yield ⟨x, y, z⟩)
            else do
              let y ← pure PUnit.unit
              __do_jp x y;
          if x = 3 then
            let z := z + i;
            do
            let y ← pure PUnit.unit
            __do_jp x z y
          else do
            let y ← pure PUnit.unit
            __do_jp x z y;
        if x < 20 then
          let y := y - 2;
          pure (ForInStep.done ⟨x, y, z⟩)
        else do
          let y_1 ← pure PUnit.unit
          __do_jp x y z y_1
  match r with
    | ⟨x, y, z⟩ => pure (w + x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check (Id.run do
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z)

set_option trace.Elab.do true in
set_option trace.Compiler.saveBase true in
/--
trace: [Elab.do] let x := 42;
    have kbreak := fun s =>
      let x := s;
      let x := x + 13;
      let x := x + 13;
      let x := x + 13;
      let x := x + 13;
      pure x;
    ForInNew.forIn [1, 2, 3] x
      (fun i kcontinue s =>
        let x := s;
        if x = 3 then pure x
        else
          if x > 10 then
            let x := x + 3;
            kcontinue x
          else
            if x < 20 then
              let x := x * 2;
              kbreak x
            else
              let x := x + i;
              kcontinue x)
      kbreak
---
trace: [Compiler.saveBase] size: 29
    def List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 l b : Nat :=
      jp _jp.3 s.4 : Nat :=
        let _x.5 := 13;
        let x := Nat.add s.4 _x.5;
        let x := Nat.add x _x.5;
        let x := Nat.add x _x.5;
        let x := Nat.add x _x.5;
        return x;
      cases l : Nat
      | List.nil =>
        goto _jp.3 b
      | List.cons head.6 tail.7 =>
        let _x.8 := instDecidableEqNat b _x.1;
        cases _x.8 : Nat
        | Decidable.isFalse x.9 =>
          let _x.10 := 10;
          let _x.11 := Nat.decLt _x.10 b;
          cases _x.11 : Nat
          | Decidable.isFalse x.12 =>
            let _x.13 := 20;
            let _x.14 := Nat.decLt b _x.13;
            cases _x.14 : Nat
            | Decidable.isFalse x.15 =>
              let x := Nat.add b head.6;
              let _x.16 := List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 tail.7 x;
              return _x.16
            | Decidable.isTrue x.17 =>
              let x := Nat.mul b _x.2;
              goto _jp.3 x
          | Decidable.isTrue x.18 =>
            let x := Nat.add b _x.1;
            let _x.19 := List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 tail.7 x;
            return _x.19
        | Decidable.isTrue x.20 =>
          return b
[Compiler.saveBase] size: 9
    def Do._example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := List.newForIn._at_.Do._example.spec_0 _x.3 _x.2 _x.7 x;
      return _x.8
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 29
    def List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 l b : Nat :=
      jp _jp.3 s.4 : Nat :=
        let _x.5 := 13;
        let x := Nat.add s.4 _x.5;
        let x := Nat.add x _x.5;
        let x := Nat.add x _x.5;
        let x := Nat.add x _x.5;
        return x;
      cases l : Nat
      | List.nil =>
        goto _jp.3 b
      | List.cons head.6 tail.7 =>
        let _x.8 := instDecidableEqNat b _x.1;
        cases _x.8 : Nat
        | Decidable.isFalse x.9 =>
          let _x.10 := 10;
          let _x.11 := Nat.decLt _x.10 b;
          cases _x.11 : Nat
          | Decidable.isFalse x.12 =>
            let _x.13 := 20;
            let _x.14 := Nat.decLt b _x.13;
            cases _x.14 : Nat
            | Decidable.isFalse x.15 =>
              let x := Nat.add b head.6;
              let _x.16 := List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 tail.7 x;
              return _x.16
            | Decidable.isTrue x.17 =>
              let x := Nat.mul b _x.2;
              goto _jp.3 x
          | Decidable.isTrue x.18 =>
            let x := Nat.add b _x.1;
            let _x.19 := List.newForIn._at_.Do._example.spec_0 _x.1 _x.2 tail.7 x;
            return _x.19
        | Decidable.isTrue x.20 =>
          return b
[Compiler.saveBase] size: 9
    def Do._example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := List.newForIn._at_.Do._example.spec_0 _x.3 _x.2 _x.7 x;
      return _x.8
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Elab.do true in
set_option trace.Compiler.saveBase true in
/--
trace: [Elab.do] let x := 42;
    let y := 0;
    let z := 1;
    ForInNew.forIn [1, 2, 3] (x, z)
      (fun i kcontinue s =>
        let x := s.fst;
        let z := s.snd;
        let x := x + i;
        ForInNew.forIn [i:10].toList z
          (fun j kcontinue s =>
            let z := s;
            let z := z + x + j;
            kcontinue z)
          fun s =>
          let z := s;
          kcontinue (x, z))
      fun s =>
      let x := s.fst;
      let z := s.snd;
      pure (x + y + z)
---
trace: [Compiler.saveBase] size: 8
    def List.newForIn._at_.Do._example.spec_0 x kcontinue.1 l b : Nat :=
      cases l : Nat
      | List.nil =>
        let _x.2 := @Prod.mk _ _ x b;
        let _x.3 := kcontinue.1 _x.2;
        return _x.3
      | List.cons head.4 tail.5 =>
        let _x.6 := Nat.add b x;
        let z := Nat.add _x.6 head.4;
        let _x.7 := List.newForIn._at_.Do._example.spec_0 x kcontinue.1 tail.5 z;
        return _x.7
[Compiler.saveBase] size: 20
    def List.newForIn._at_.List.newForIn._at_.Do._example.spec_1.spec_1 z l b : Nat :=
      cases l : Nat
      | List.nil =>
        let x := b # 0;
        let z := b # 1;
        let _x.1 := Nat.add x z;
        return _x.1
      | List.cons head.2 tail.3 =>
        fun _f.4 x.5 : Nat :=
          let _x.6 := List.newForIn._at_.List.newForIn._at_.Do._example.spec_1.spec_1 z tail.3 x.5;
          return _x.6;
        let x := b # 0;
        let z := b # 1;
        let x := Nat.add x head.2;
        let _x.7 := 10;
        let _x.8 := Nat.sub _x.7 head.2;
        let _x.9 := Nat.add _x.8 z;
        let _x.10 := 1;
        let _x.11 := Nat.sub _x.9 _x.10;
        let _x.12 := Nat.mul z _x.11;
        let _x.13 := Nat.add head.2 _x.12;
        let _x.14 := @List.nil _;
        let _x.15 := List.range'TR.go z _x.11 _x.13 _x.14;
        let _x.16 := List.newForIn._at_.Do._example.spec_0 x _f.4 _x.15 z;
        return _x.16
[Compiler.saveBase] size: 20
    def List.newForIn._at_.Do._example.spec_1 z l b : Nat :=
      cases l : Nat
      | List.nil =>
        let x := b # 0;
        let z := b # 1;
        let _x.1 := Nat.add x z;
        return _x.1
      | List.cons head.2 tail.3 =>
        fun _f.4 x.5 : Nat :=
          let _x.6 := List.newForIn._at_.List.newForIn._at_.Do._example.spec_1.spec_1 z tail.3 x.5;
          return _x.6;
        let x := b # 0;
        let z := b # 1;
        let x := Nat.add x head.2;
        let _x.7 := 10;
        let _x.8 := Nat.sub _x.7 head.2;
        let _x.9 := Nat.add _x.8 z;
        let _x.10 := 1;
        let _x.11 := Nat.sub _x.9 _x.10;
        let _x.12 := Nat.mul z _x.11;
        let _x.13 := Nat.add head.2 _x.12;
        let _x.14 := @List.nil _;
        let _x.15 := List.range'TR.go z _x.11 _x.13 _x.14;
        let _x.16 := List.newForIn._at_.Do._example.spec_0 x _f.4 _x.15 z;
        return _x.16
[Compiler.saveBase] size: 10
    def Do._example : Nat :=
      let x := 42;
      let z := 1;
      let _x.1 := 2;
      let _x.2 := 3;
      let _x.3 := @List.nil _;
      let _x.4 := @List.cons _ _x.2 _x.3;
      let _x.5 := @List.cons _ _x.1 _x.4;
      let _x.6 := @List.cons _ z _x.5;
      let _x.7 := @Prod.mk _ _ x z;
      let _x.8 := List.newForIn._at_.Do._example.spec_1 z _x.6 _x.7;
      return _x.8
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      z := z + x + j
  return x + y + z

/--
info: (let x := 42;
  do
  let r ←
    forIn [1, 2, 3] ⟨none, x⟩ fun i r =>
        let r_1 := r.snd;
        let x := r_1;
        let __do_jp := fun x y =>
          let __do_jp := fun x y =>
            let __do_jp := fun x y =>
              let x := x + i;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨none, x⟩);
            if x < 20 then
              let x := x * 2;
              pure (ForInStep.done ⟨none, x⟩)
            else do
              let y ← pure PUnit.unit
              __do_jp x y;
          if x > 10 then
            let x := x + 3;
            pure (ForInStep.yield ⟨none, x⟩)
          else do
            let y ← pure PUnit.unit
            __do_jp x y;
        if x = 3 then pure (ForInStep.done ⟨some x, x⟩)
        else do
          let y ← pure PUnit.unit
          __do_jp x y
  let x : Nat := r.snd
  let __do_jp : Nat → PUnit → Id Nat := fun x y =>
    let x := x + 13;
    let x := x + 13;
    let x := x + 13;
    let x := x + 13;
    pure x
  match r.fst with
    | none => do
      let y ← pure PUnit.unit
      __do_jp x y
    | some a => pure a).run : Nat
-/
#guard_msgs (info) in
#check (Id.run do
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x)

open Std.Do in
set_option trace.Elab.do true in
#check Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3]
    invariant xs => ⌜xs.pos = 3⌝ do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z

open Std.Do in
#check Id.run <| StateT.run (σ:= Nat) (s:=42) doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3]
    invariant xs s => ⌜xs.pos = s⌝ do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z

#check Id.run do
  let mut a := 0
  for x in [1,2,3], y in [3,4,5], z in [6,7,8] do
    a := a + x + y + z
  return a

example : (Id.run doo pure 42)
        = (Id.run  do pure 42) := by rfl
example : (Id.run doo return 42)
        = (Id.run  do return 42) := by rfl
example {e : Id PUnit} : (Id.run doo e)
                       = (Id.run  do e) := by rfl
example {e : Id PUnit} : (Id.run doo e; return 42)
                       = (Id.run  do e; return 42) := by rfl
example : (Id.run doo let x := 42; return x + 13)
        = (Id.run  do let x := 42; return x + 13) := by rfl
example : (Id.run doo let x ← pure 42; return x + 13)
        = (Id.run  do let x ← pure 42; return x + 13) := by rfl
example : (Id.run doo let mut x := 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x := 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x ← pure 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x)
        = (Id.run  do let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : Nat := Id.run doo let mut foo : Nat = Nat := rfl; pure (foo ▸ 23)
example {e} : (Id.run doo let mut x := 0; let y := 3; let z ← do { let mut y ← e; x := y + 1; pure y }; let y := y + 3; pure (x + y + z))
            = (Id.run  do let mut x := 0; let y := 3; let z ← do { let mut y ← e; x := y + 1; pure y }; let y := y + 3; pure (x + y + z)) := by rfl
example : (Id.run doo let x := 0; let y ← let x := x + 1; pure x)
        = (Id.run doo let x := 0; pure x) := by rfl

-- Test: Nested if-then-else with multiple mutable variables
example : (Id.run doo
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y)
= (Id.run do
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y) := by rfl

-- Test: Multiple reassignments in sequence
example : (Id.run doo
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x)
= (Id.run do
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x) := by rfl

-- Test: Monadic bind with complex RHS
example : (Id.run doo
  let x ← (do let y := 5; pure (y + 3))
  return x * 2)
= (Id.run do
  let x ← (do let y := 5; pure (y + 3))
  return x * 2) := by rfl

-- Test: Mutable variable reassignment through monadic bind
example : (Id.run doo
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x)
= (Id.run do
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x) := by rfl

-- Test: Multiple mutable variables with different reassignment patterns
example : (Id.run doo
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c))
= (Id.run do
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c)) := by rfl

-- Test: Let binding followed by mutable reassignment
example : (Id.run doo
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y))
= (Id.run do
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y)) := by rfl

-- Test: Early return in else branch
example : (Id.run doo
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x)
= (Id.run do
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x) := by rfl

-- Test: Both branches return
example : (Id.run doo
  let mut x := 0
  if true then
    return 1
  else
    return 2)
= (Id.run do
  let mut x := 0
  if true then
    return 1
  else
    return 2) := by rfl

-- Test: Three-level nested if with mutable variables
example : (Id.run doo
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x)
= (Id.run do
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x) := by rfl

-- Test: Mutable variable used in condition
example : (Id.run doo
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x)
= (Id.run do
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x) := by rfl

-- Test: Multiple monadic binds in sequence
example : (Id.run doo
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c))
= (Id.run do
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c)) := by rfl

-- Test: Mutable bind in if condition position
example : (Id.run doo
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x)
= (Id.run do
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x) := by rfl

-- Test: Empty else branch behavior
example : (Id.run doo
  let mut x := 5
  if false then
    x := 10
  return x)
= (Id.run do
  let mut x := 5
  if false then
    x := 10
  return x) := by rfl

-- Test: Nested doo with if and early return
example : (Id.run doo
  let mut x := 10
  let y ← do
    if h : true then
      x := x + 3
      pure 42
    else
      return 13
  return x + y)
= (Id.run do
  let mut x := 10
  let y ← do
    if h : true then
      x := x + 3
      pure 42
    else
      return 13
  return x + y) := by rfl

-- Test: ifCondLet and else if
example : (Id.run doo
  let mut x := 0
  if let false := not true then
    x := 10
  else if let 0 ← pure 42 then
    return 42
  else
    x := 3
  x := x + 13
  return x)
= (Id.run do
  let mut x := 0
  if let false := not true then
    x := 10
  else if let 0 ← pure 42 then
    return 42
  else
    x := 3
  x := x + 13
  return x) := by rfl

-- Test: elabToSyntax and postponement
/--
error: Invalid match expression: The type of pattern variable 'y' contains metavariables:
  ?m.26
-/
#guard_msgs (error) in
example := Id.run doo
  let mut x := 0 -- We should not get an error that fixed elaborator 0 was not registered
  if let some y := none then
    pure 1
  else
    pure 2

-- Test: For loops with break, continue and return
example :
  (Id.run doo
  let mut x := 42
  for i in [0:100].toList do
    if i = 40 then return x
    if i > 20 then x := x + 3; break
    if i < 20 then x := x * 2; continue
    x := x + i
  x := x + 13
  x := x + 13
  return x)
= (Id.run do
  let mut x := 42
  for i in [0:100].toList do
    if i = 40 then return x
    if i > 20 then x := x + 3; break
    if i < 20 then x := x * 2; continue
    x := x + i
  x := x + 13
  x := x + 13
  return x) := by rfl

-- set_option trace.Meta.synthInstance true in
set_option trace.Elab.do true in
-- Test: Nested for loops with break, continue and return
example :
  (Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z)
= (Id.run do
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z) := by rfl

-- Test: Try/catch
example {try_ : Except String Nat} {catch_ : String → Except String Nat} :
  (Id.run <| ExceptT.run (ε:=String) doo
  let x ←
    try try_ -- TODO: investigate why we can't put it on the same line
    catch e => catch_ e
  return x + 23)
= (Id.run <| ExceptT.run (ε:=String) do
  let x ← try try_ catch e => catch_ e
  return x + 23) := by simp

-- Test: Try/catch with throw in continuation (i.e., `tryCatch` is non-algebraic)
example :
  (Id.run <| ExceptT.run (ε:=String) doo
  try pure ()
  catch e => pure ()
  throw (α:=Nat) "error")
= throw (α:=Nat) "error" := by rfl

#check (Id.run <| ExceptT.run (ε:=String) doo
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
      return ()
    else
      x := 5
  catch e =>
    x := x + 1)

#check (Id.run <| ExceptT.run (ε:=String) do
  let mut x := 0
  try
    if true then
      throw "error"
      return ()
    else
      pure ()
  catch e =>
    pure ())

-- Try/catch with reassignment
example :
  (Id.run <| ExceptT.run (ε:=String) doo
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
    else
      x := 5
  catch e =>
    x := x + 1
  return x)
= (Id.run <| ExceptT.run (ε:=String) do
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
    else
      x := 5
  catch e =>
    x := x + 1
  return x) := by rfl

#check (Id.run <| StateT.run' (σ := Nat) (s := 42) <| ExceptT.run (ε:=String) doo
  try
    pure ()
  finally
    set 0
  get)

-- Try/finally
example {s} :
  (Id.run <| StateT.run' (σ := Nat) (s := s) <| ExceptT.run (ε:=String) doo
  try
    e
  finally
    set 0
  get)
= (Id.run <| StateT.run' (σ := Nat) (s := s) <| ExceptT.run (ε:=String) do
  try
    e
  finally
    set 0
  get) := by simp

-- Try/catch with return, break and continue
example :
  let f n :=
      (Id.run <| ExceptT.run (ε:=String) doo
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 15 then break
          if i = 25 then continue
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
    = (Id.run <| ExceptT.run (ε:=String) do
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 15 then break
          if i = 25 then continue
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
  f 0 ∧ f 10 ∧ f 20 ∧ f 30 ∧ f 31 ∧ f 45 ∧ f 1023948 := by trivial

-- Try/catch with return and continue
example :
  let f n :=
      (Id.run <| ExceptT.run (ε:=String) doo
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 25 then continue
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
    = (Id.run <| ExceptT.run (ε:=String) do
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 25 then continue
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
  f 0 ∧ f 10 ∧ f 20 ∧ f 30 ∧ f 31 ∧ f 45 ∧ f 1023948 := by trivial

-- Try/catch with return and break
example :
  let f n :=
      (Id.run <| ExceptT.run (ε:=String) doo
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 15 then break
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
    = (Id.run <| ExceptT.run (ε:=String) do
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 5 then return x
          if i = 15 then break
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
  f 0 ∧ f 10 ∧ f 20 ∧ f 30 ∧ f 31 ∧ f 45 ∧ f 1023948 := by trivial

-- Try/catch with break
example :
  let f n :=
      (Id.run <| ExceptT.run (ε:=String) doo
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 15 then break
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
    = (Id.run <| ExceptT.run (ε:=String) do
      let mut x := 0
      for i in [n:n+10].toList do
        try
          if i = 15 then break
          if i = 35 then throw "error"
          x := x + i
        catch _ =>
          x := x + 1
      return x)
  f 0 ∧ f 10 ∧ f 20 ∧ f 30 ∧ f 31 ∧ f 45 ∧ f 1023948 := by trivial

-- Parallel for loops
example :
  let f n m :=
    (Id.run doo
      let mut a := 0
      for h : x in [1,2,3], y in [0:n], z in [0:m] do
        have : x < 5 := by grind
        a := a + x + y + z
      return a)
    = (Id.run do
      let mut a := 0
      for h : x in [1,2,3], y in [0:n], z in [0:m] do
        have : x < 5 := by grind
        a := a + x + y + z
      return a)
  f 3 3 ∧ f 1 4 ∧ f 4 2 ∧ f 5 5 := by trivial

set_option backward.do.legacy false in
example {f : Nat → Nat → Id Unit} :
  (Id.run do f (← e₁) (← e₂); es)
  =
  (Id.run do let x ← e₁; let y ← e₂; f x y; es)
  := by rfl

set_option backward.do.legacy false in
example {g : Nat → Id Unit} {h : Nat → Id Nat} :
  (Id.run do let x := g (← h (← e₁)); es)
  =
  (Id.run do let x ← e₁; let y ← h x; g y; es)
  := by rfl


/-!
Postponing Monad instance resolution appropriately
-/

/--
error: typeclass instance problem is stuck
  Pure ?m.9

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
example := doo return 42
/--
error: typeclass instance problem is stuck
  Bind ?m.14

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Bind` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
example := doo let x <- ?z; ?y
/--
error: typeclass instance problem is stuck
  Pure ?m.12

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
example := do return 42
/--
error: typeclass instance problem is stuck
  Bind ?m.16

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Bind` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
example := do let x <- ?z; ?y

-- This tests that inferred types are correctly propagated outwards.
example {e : Id Nat} := doo if true then e else pure 13
-- We do want to be able to `#check` the following example (including the last `pure`) without an
-- expected monad, ...
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
-- As well as fully resolve all instances in the following example where the expected monad is
-- known. The next example wouldn't work without `Id.run`.
example := Id.run doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 42; x := x - 7; let x := x + 4; return x + 13)

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
-/
#guard_msgs (error) in
example := (Id.run doo pure true; pure ())

/--
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
---
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure true} else {pure false}; pure ())

/--
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure ()} else {pure false}; pure ())

-- Additional error tests

/-- error: undeclared mutable variable `foo` -/
#guard_msgs (error) in
example := (Id.run doo foo := 42; pure ())

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 1; if true then {let mut x := 2; pure ()} else {pure ()}; pure x)

-- Regression test cases of what's currently broken in the do elaborator:
example : Unit := (Id.run do  let n ← if true then pure 3 else pure 42)
example : Unit := (Id.run doo let n ← if true then pure 3 else pure 42)
example := (Id.run do  let mut x := 0; x ← return 10)
example := (Id.run doo let mut x := 0; x ← return 10)

/--
info: let x := 0;
let y := 0;
if true = true then pure 3
else
  let x := x + 5;
  let y_1 := 3;
  pure (x + y) : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    return 3
  else
    x := x + 5
    let y := 3
  return x + y

/--
info: let x := 0;
let y := 0;
have __do_jp := fun x r => pure (x + y);
if true = true then
  let x := x + 7;
  let y := 3;
  __do_jp x PUnit.unit
else
  let x := x + 5;
  __do_jp x PUnit.unit : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    x := x + 7
    let y := 3
  else
    x := x + 5
  return x + y


set_option trace.Elab.do true in
/--
trace: [Elab.do] let x := 42;
    have kbreak := fun s =>
      let x := s;
      let x := x + 13;
      let x := x + 13;
      let x := x + 13;
      let x := x + 13;
      pure x;
    ForInNew.forIn [1, 2, 3] x
      (fun i kcontinue s =>
        let x := s;
        if x = 3 then pure x
        else
          if x > 10 then
            let x := x + 3;
            kcontinue x
          else
            if x < 20 then
              let x := x * 2;
              kbreak x
            else
              let x := x + i;
              kcontinue x)
      kbreak
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Elab.do true in
example := Id.run doo
  let mut x := 42
  return x

example : Id Nat := do
  let x := 42
  x + ?x
where finally
case x => exact 13
