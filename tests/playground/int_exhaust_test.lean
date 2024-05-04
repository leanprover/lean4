import Lean.Util.TestNormalForms
import Lean.Meta.Tactic.Simp.BuiltinSimprocs
import Lean.Meta.LitValues

open Lean
open Lean.Elab.Command (CommandElab)
open Lean.Test.NormalForms

inductive NumType where
  | prop
  | nat
  | int
deriving DecidableEq, Hashable, Inhabited, Repr

protected def NumType.render [Monad M] [MonadQuotation M] (v : NumType) : M Term := do
  match v with
  | prop => `(Prop)
  | nat => `(Nat)
  | int => `(Int)

inductive  DivMode where
  | divNat
  | edivInt
  | tdivInt
  | fdivInt
  | bdivInt
  deriving DecidableEq, Repr

def DivMode.typeOf (m : DivMode) : NumType :=
  match m with
  | divNat => .nat
  | edivInt => .int
  | fdivInt => .int
  | tdivInt => .int
  | bdivInt => .int

inductive NumTerm where
  | var (d : VarDecl NumType)
  | lit (n : Nat) (tp : NumType)
  | natCast (x : NumTerm)
  | add (x y : NumTerm) (tp : NumType)
  | sub (x y : NumTerm) (tp : NumType)
  | neg (x : NumTerm)
  | mul (x y : NumTerm) (tp : NumType)
  | div (x y : NumTerm) (m : DivMode)
  | mod (x y : NumTerm) (m : DivMode)
  | eq (x y : NumTerm) (tp : NumType)
  | le (x y : NumTerm) (tp : NumType)
  | lt (x y : NumTerm) (tp : NumType)
  | true | false
  deriving BEq, Inhabited, Repr

namespace NumTerm

open NumType

partial def map (f : NumTerm → NumTerm) (v : NumTerm) : NumTerm :=
  match v with
  | var _ | lit _ _ => v
  | natCast x => natCast (f x)
  | add x y tp => add (f x) (f y) tp
  | sub x y tp => sub (f x) (f y) tp
  | neg x => neg (f x)
  | mul x y tp => mul (f x) (f y) tp
  | div x y op => div (f x) (f y) op
  | mod x y op => mod (f x) (f y) op
  | eq x y tp => eq (f x) (f y) tp
  | le x y tp => le (f x) (f y) tp
  | lt x y tp => lt (f x) (f y) tp
  | true => true
  | false => false

protected def typeOf (v : NumTerm) : NumType :=
  match v with
  | var d => d.type
  | lit _ tp => tp
  | natCast _ => .int
  | add _ _ tp | sub _ _ tp | mul _ _ tp => tp
  | neg _ => .int
  | div _ _ op | mod _ _ op => op.typeOf
  | eq .. | le .. | lt .. | true | false => .prop

protected def render [Monad M] [MonadQuotation M] (v : NumTerm) : M Term := do
  match v with
  | var d => pure d.ident
  | lit n tp => `(($(Syntax.mkNumLit (toString n)) : $(← tp.render)))
  | natCast x => `(($(←x.render).cast : Int))
  | add x y tp => `((($(←x.render) + $(←y.render)) : $(← tp.render)))
  | sub x y tp => `((($(←x.render) - $(←y.render)) : $(← tp.render)))
  | mul x y tp => `((($(←x.render) * $(←y.render)) : $(← tp.render)))
  | neg x => `(- $(←x.render))
  | div x y op =>
    match op with
    | .divNat  => `($(←x.render) / $(←y.render))
    | .edivInt => `($(←x.render) / $(←y.render))
    | .fdivInt => `(Int.fdiv $(←x.render) $(←y.render))
    | .tdivInt => `(Int.div  $(←x.render) $(←y.render))
    | .bdivInt => `(Int.bdiv $(←x.render) $(←y.render))
  | mod x y op =>
    match op with
    | .divNat  => `($(←x.render) % $(←y.render))
    | .edivInt => `($(←x.render) % $(←y.render))
    | .fdivInt => `(Int.fmod $(←x.render) $(←y.render))
    | .tdivInt => `(Int.mod  $(←x.render) $(←y.render))
    | .bdivInt => `(Int.bmod $(←x.render) $(←y.render))
  | eq x y _ => `($(←x.render) = $(←y.render))
  | le x y _ => `($(←x.render) ≤ $(←y.render))
  | lt x y _ => `($(←x.render) < $(←y.render))
  | true => `(True)
  | false => `(False)

instance : GenTerm NumTerm NumType where
  render := NumTerm.render
  mkVar := NumTerm.var

def intLit (i : Int) : NumTerm :=
  if i < 0 then
    neg (lit ((- i).toNat) .int)
  else
    lit i.toNat .int

def mkConstProp (b : Bool) : NumTerm := cond b .true .false

def mkLit (i : Int) (tp : NumType) : NumTerm :=
  if i < 0 then
    match tp with
    | .prop => panic! "prop literal not allowed"
    | .nat => panic! "Negative number passed into nat"
    | .int => neg (lit ((- i).toNat) .int)
  else
    lit i.toNat tp

def asIntLit (i : NumTerm) : Option Int :=
  match i with
  | .lit n _ => some (n : Int)
  | .neg (.lit n .int) => some (- (n : Int))
  | _ => none

/--
Returns nat term or literal equal to input term if input
term is a literal or has form `natToInt _`.
-/
def intAtNat (x : NumTerm) : Option NumTerm :=
  match x with
  | lit xn .int => some (lit xn .nat)
  | natCast x => some x
  | _ => none

def isPos (x : NumTerm) : Bool :=
  match x with
  | lit xn .nat => xn > 0
  | _ => Bool.false

partial def simp (v : NumTerm) : NumTerm :=
  let v := map simp v
  match v with
  | natCast x =>
    (match x with
    | lit n _ => lit n .int
    | add x y _ => simp <| add (natCast x) (natCast y) .int
    | mul x y _ => simp <| mul (natCast x) (natCast y) .int
    | div x y _ => simp <| div (natCast x) (natCast y) .edivInt
    | mod x y _ => simp <| mod (natCast x) (natCast y) .edivInt
    | var _ | sub .. | neg _ | natCast _
      | eq .. | le .. | lt .. | true | false => v)
  | add x y tp =>
    match x, y with
    | x, lit 0 _ => x
    | lit 0 _, y => y
    | _, _ => Id.run <| do
      if let .sub xa xb _ := x then
        if tp = .int ∧ xb == y then
          return xa
      if let (some i, some j) := (asIntLit x, asIntLit y) then
        return (mkLit (i+j) tp)
      pure v
  | sub x y tp =>
    match x, y, tp with
    | x, lit 0 _, _ => x
    | lit 0 _, _, .nat => lit 0 .nat
    | lit 0 _, y, .int => simp (neg y)
    | x, y, _ => Id.run <| do
      match tp with
      | .prop =>
        panic! "sub applied to prop"
      | .nat =>
        if let (lit xo _, lit yo _) := (x, y) then
          return lit (xo - yo) .nat
        if let (lit xo _, add yb (lit yo _) _) := (x, y) then
          let r :=
            if xo > yo then
              sub (lit (xo - yo) nat) yb nat
            else
              lit 0 nat
          return r
        if let (add xb (lit xo _) _, lit yo _) := (x, y) then
          let r :=
            if xo > yo then
              add xb (lit (xo - yo) nat) nat
            else if xo < yo then
              sub xb (lit (yo - xo) nat) nat
            else
              xb
          return r
        if let (add xb (lit xo _) _, add yb (lit yo _) _) := (x, y) then
          let r :=
            if xo > yo then
              sub (add xb (lit (xo - yo) nat) nat) yb nat
            else if xo < yo then
              sub xb (add yb (lit (yo - xo) nat) nat) nat
            else
              sub xb yb nat
          return r
      | .int =>
        if let (some i, some j) := (asIntLit x, asIntLit y) then
          return mkLit (i - j) .int
      if let .add xa xb _ := x then
        if xb == y then
          return xa
      if x == y then
        return .lit 0 tp
      pure v
  | neg x =>
    match x with
    | lit n _ => intLit (- (Int.ofNat n))
    | neg x => x
    | _ => v
  | mul x y tp =>
    match x, y with
    | _, lit 0 _ => y
    | lit 0 _, _ => x
    | _, lit 1 _ => x
    | lit 1 _, _ => y
    | lit i _, lit j _ => lit (i*j) tp
    | _, _ => Id.run <| do
      if let (some i, some j) := (asIntLit x, asIntLit y) then
        return (mkLit (i * j) tp)
      pure v
  | div x y op =>
    if let (some x, some y) := (asIntLit x, asIntLit y) then
      match op with
      | .divNat => lit (Nat.div x.toNat y.toNat) .nat
      | .edivInt => intLit (Int.ediv x y)
      | .fdivInt => intLit (Int.fdiv x y)
      | .tdivInt => intLit (Int.div  x y)
      | .bdivInt => intLit (Int.bdiv x y.toNat)
    else if let lit 0 _ := x then
      x
    else if let lit 0 _ := y then
      lit 0 op.typeOf
    else if let lit 1 _ := y then
      x
    else Id.run <| do
      if let add xa xb _tp := x then
        if let .lit i _ := y then
          if op ∈ [.divNat] ∧ i ≠ 0 then
            if xa == y then
              return simp (.add (.div xb y op) (.lit 1 op.typeOf) op.typeOf)
            else if xb == y then
              return simp (.add (.div xa y op) (.lit 1 op.typeOf) op.typeOf)
      if let sub xa xb _tp := x then
          if op = .divNat ∧ xb == y then
            return simp (.sub (.div xa y op) (.lit 1 op.typeOf) op.typeOf)
      if let mod _ n mOp := x then
        if op = .divNat ∧ mOp = .divNat ∧ n == y then
          return .lit 0 .nat
      if let neg xn := x then
        match op with
        | .tdivInt =>
          return simp (neg (div xn y op))
        | _ =>
          pure ()
      if let neg yn := y then
        match op with
        | .edivInt | .tdivInt =>
          return simp (neg (div x yn op))
        | _ =>
          pure ()
      if let mul xa xb _ := x then
       if let .lit i _ := y then
          if i ≠ 0 then
            if xa == y then
              return xb
            if xb == y then
              return xa
      pure v
  | mod x n op =>
    if let (some x, some n) := (asIntLit x, asIntLit n) then
      match op with
      | .divNat => lit (Nat.mod x.toNat n.toNat) .nat
      | .edivInt => intLit (Int.emod x n)
      | .fdivInt => intLit (Int.fmod x n)
      | .tdivInt => intLit (Int.mod  x n)
      | .bdivInt => intLit (Int.bmod x n.toNat)
    else if let lit 0 _ := x then
      x
    else if let lit 0 _ := n then
      x
    else if let lit 1 _ := n then
      lit 0 op.typeOf
    else if x == n then
      lit 0 op.typeOf
    else Id.run do
      if let add xa xb _tp := x then
        if op ∈ [.divNat, .edivInt] then
          if xa == n then
            return simp (.mod xb n op)
          else if xb == n then
            return simp (.mod xa n op)
          if let mul xba xbb _tp := xb then
            if xba == n || xbb == n then
              return simp (.mod xa n op)
      if let sub xa xb _tp := x then
        if op ∈ [.edivInt] then
          if xa == n then
            return simp (.mod (.neg xb) n op)
          else if xb == n then
            return simp (.mod xa n op)
          if let mul xba xbb _tp := xb then
            if xba == n || xbb == n then
              return simp (.mod xa n op)
      if let mul xa xb tp := x then
        if xa == n || xb == n then
          return lit 0 tp
      if let mod xn xd xop := x then
        let rop : Option NumTerm :=
          match op, xop with
          | .divNat,  .divNat  => do guard (n == xd); some (mod xn n .divNat)
          | .edivInt, .bdivInt => do guard (n == natCast xd); some (mod xn n .edivInt)
          | .edivInt, _        => do guard (n == xd); some (mod xn n .edivInt)
          | .tdivInt, .edivInt => do guard (n == xd); some (mod xn n .edivInt)
          | .tdivInt, .tdivInt => do guard (n == xd); some (mod xn n .tdivInt)
          | .fdivInt, .edivInt => do guard (n == xd); some (mod xn n .fdivInt)
          | .fdivInt, .fdivInt => do guard (n == xd); some (mod xn n .fdivInt)
          | .bdivInt, .bdivInt => do guard (n == xd); some (mod xn n .bdivInt)
          | .bdivInt, _        => do guard (natCast n == xd); some (mod xn n .bdivInt)
          | _, _ => none
        if let some r := rop then
            return simp r
      if let neg yn := n then
        match op with
        | .edivInt | .tdivInt =>
          return simp (mod x yn op)
        | _ =>
          pure ()
      return v
  | eq x y _ => Id.run do
      if let (some i, some j) := (asIntLit x, asIntLit y) then
        return mkConstProp (i = j)
      if x == y then
        return NumTerm.true
      pure v
  | le x y _ => Id.run do
      if let (some i, some j) := (asIntLit x, asIntLit y) then
        return mkConstProp (i ≤ j)
--      if let (some xn, some yn) := (intAtNat x, intAtNat y) then
--        return (le xn yn .nat)
      if x == y then
        return NumTerm.true
      pure v
  | lt x y tp => Id.run do
      if let (some i, some j) := (asIntLit x, asIntLit y) then
        return mkConstProp (i < j)
      if let (lit 0 .int, natCast yn) := (x, y) then
        return simp (lt (lit 0 .nat) yn .nat)
      if let (natCast xn, natCast yn) := (x, y) then
        return simp (lt xn yn .nat)
      if tp = .nat then
        if x == y then
          return NumTerm.false
        if let add yb (lit yo _) _ := y then
          if x == yb then
            return mkConstProp (yo > 0)
        if let (lit xo _, add yb (lit yo _) _) := (x, y) then
          let r := if xo < yo then NumTerm.true else lt (lit (xo - yo) .nat) yb .nat
          return r
        if let (add xb (lit xo _) _, lit yo _) := (x, y) then
          let r :=
            if xo < yo then
              lt xb (lit (yo - xo) .nat) .nat
            else
              NumTerm.false
          return r
        if let (add xb (lit xo _) _, add yb (lit yo _) _) := (x, y) then
          let r :=
            if xo < yo then
              lt xb (add yb (lit (yo - xo) .nat) .nat) .nat
            else if xo > yo then
              lt (add xb (lit (xo - yo) .nat) .nat) yb .nat
            else
              lt xb yb .nat
          return r
        if let (lit 0 _, mul y1 y2 _) := (x, y) then
          if isPos y1 then
            return lt (lit 0 nat) y2 nat
          if isPos y2 then
            return lt (lit 0 nat) y1 nat
      pure v
  | true | false | lit _ _ | var _ => v

partial def simpv (u : NumTerm) : NumTerm :=
  let v := simp u
  if v.typeOf == u.typeOf then
    v
  else
    panic! s!"simp result changed types:\n  Input: {repr u}\n  Out:   {repr v}"

def litOp (n : Nat) (tp : NumType) := mkOp [] tp fun _ => lit n tp
def binOp (op : NumTerm → NumTerm → NumType → NumTerm) (tp : NumType) :=
  mkOp [tp, tp] tp fun a => op (a[0]!) (a[1]!) tp
def binRel (op : NumTerm → NumTerm → NumType → NumTerm) (tp : NumType) :=
  mkOp [tp, tp] .prop fun a => op (a[0]!) (a[1]!) tp
def negOp : Op NumType NumTerm := mkOp [.int] .int fun a => neg (a[0]!)
def divOp (op : DivMode) (dtp := op.typeOf) := let tp := op.typeOf; mkOp [tp, dtp] tp fun a => div (a[0]!) (a[1]!) op
def modOp (op : DivMode) (dtp := op.typeOf) := let tp := op.typeOf; mkOp [tp, dtp] tp fun a => mod (a[0]!) (a[1]!) op
def natToIntOp := mkOp [NumType.nat] .int fun x => natCast x[0]!

end NumTerm

open NumTerm

syntax:lead (name := intTestElab) "#intTest" : command

@[command_elab intTestElab]
def elabIntTest : CommandElab := fun _stx => do
  let types : List NumType := [.prop, .nat, .int]
  let ops := [
      litOp 0 .nat,
      litOp 1 .nat,
      litOp 2 .nat,
      litOp 0 .int,
      litOp 1 .int,
      litOp 2 .int,
      natToIntOp,
      binOp add .nat, binOp add .int,
      binOp sub .nat, binOp sub .int,
      binOp mul .nat, binOp mul .int,
      negOp,
      divOp .divNat, divOp .edivInt, divOp .fdivInt, divOp .tdivInt, divOp .bdivInt .nat,
      modOp .divNat, modOp .edivInt, modOp .fdivInt, modOp .tdivInt, modOp .bdivInt .nat,
      binRel eq .nat, binRel eq .int,
      binRel le .nat, binRel le .int,
      binRel lt .nat, binRel lt .int,
  ]
  let vars : List (NumType × CoreM Command) := [
      (.nat, `(variable (n : Nat))),
      (.int, `(variable (i : Int)))
  ]
  let stats : GenStats := { maxTermSize := 6, maxDepth := 3, maxVarCount := 2 }
  testNormalForms types ops vars NumTerm.simpv stats

set_option pp.coercions false
set_option pp.explicit true
set_option maxHeartbeats 100000000
#intTest

variable (m n : Nat)

/-

  @LT.lt Nat instLTNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n0 (@OfNat.ofNat Nat 2 (instOfNatNat 2))) reduces to
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n0 (@OfNat.ofNat Nat 2 (instOfNatNat 2)))
but is expected to reduce to
  True

-/

set_option trace.Meta.Tactic.simp.rewrite true

#check_tactic n < n + 1 ~> True by simp

#check_tactic 0 < n + 2 ~> True by
  simp

#check_simp 1 < n + 2 !~>


#print Nat.mul_pos_iff_of_pos_left
#check_tactic 0 < n + 2 ~> True by simp

#check_tactic 0 < 2 * n ~> 0 < n by simp



#check_tactic (@OfNat.ofNat Int 0 (@instOfNat 0)) < (@Nat.cast Int _ n0) ~> m < n by
  simp

set_option trace.Meta.Tactic.simp.rewrite true

#print Int.ofNat_pos

#check_tactic ((0 : Int) < @Nat.cast Int _ n) ~> 0 < n by
  simp


#check_simp ((1 : Int) < @Nat.cast Int _ n) !~> 1 < n.cast

#check_tactic ((0 : Int) < (n : Int)) ~> 0 < n by
  simp


--set_option pp.notation fals

example : ((1 : Nat) < (n : Int)) := by
  simp

#check_tactic ((1 : Nat) < (n : Int)) ~> 1 < n by
  simp

#check_tactic (n < n + 2) ~> True by
  simp



--#check_tactic (1 < (n : Int)) ~> 1 < n by
--  simp

/-

-/
