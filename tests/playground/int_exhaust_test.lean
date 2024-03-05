import Lean.Util.TestNormalForms
import Lean.Meta.Tactic.Simp.BuiltinSimprocs
import Lean.Meta.LitValues

open Lean
open Lean.Elab.Command (CommandElab)
open Lean.Test.NormalForms

inductive NumType where
  | nat
  | int
deriving DecidableEq, Hashable, Inhabited, Repr

protected def NumType.render [Monad M] [MonadQuotation M] (v : NumType) : M Term := do
  match v with
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
  | natToInt (x : NumTerm)
  | intToNat (x : NumTerm)
  | add (x y : NumTerm) (tp : NumType)
  | sub (x y : NumTerm) (tp : NumType)
  | neg (x : NumTerm)
  | mul (x y : NumTerm) (tp : NumType)
  | div (x y : NumTerm) (m : DivMode)
  | mod (x y : NumTerm) (m : DivMode)
  deriving BEq, Inhabited, Repr

namespace NumTerm

open NumType

partial def map (f : NumTerm → NumTerm) (v : NumTerm) : NumTerm :=
  match v with
  | var _ | lit _ _ => v
  | natToInt x => natToInt (f x)
  | intToNat x => intToNat (f x)
  | add x y tp => add (f x) (f y) tp
  | sub x y tp => sub (f x) (f y) tp
  | neg x => neg (f x)
  | mul x y tp => mul (f x) (f y) tp
  | div x y op => div (f x) (f y) op
  | mod x y op => mod (f x) (f y) op

protected def typeOf (v : NumTerm) : NumType :=
  match v with
  | var d => d.type
  | lit _ tp => tp
  | natToInt _ => .int
  | intToNat _ => .nat
  | add _ _ tp => tp
  | sub _ _ tp => tp
  | neg _ => .int
  | mul _ _ tp => tp
  | div _ _ op => op.typeOf
  | mod _ _ op => op.typeOf

protected def render [Monad M] [MonadQuotation M] (v : NumTerm) : M Term := do
  match v with
  | var d => pure d.ident
  | lit n tp => `(($(Syntax.mkNumLit (toString n)) : $(←tp.render)))
  | natToInt x => `((($(←x.render) : Nat) : Int))
  | intToNat x => `((($(←x.render) : Int) : Nat))
  | add x y tp => `((($(←x.render) + $(←y.render)) : $(←tp.render)))
  | sub x y _ => `($(←x.render) - $(←y.render))
  | neg x => `(- $(←x.render))
  | mul x y _ => `($(←x.render) * $(←y.render))
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

instance : GenTerm NumTerm NumType where
  render := NumTerm.render
  mkVar := NumTerm.var

def intLit (i : Int) : NumTerm :=
  if i < 0 then
    neg (lit ((- i).toNat) .int)
  else
    lit i.toNat .int

def mkLit (i : Int) (tp : NumType) : NumTerm :=
  if i < 0 then
    match tp with
    | .nat => panic! "Negative number passed into nat"
    | .int => neg (lit ((- i).toNat) .int)
  else
    lit i.toNat tp

def asIntLit (i : NumTerm) : Option Int :=
  match i with
  | .lit n _ => some (n : Int)
  | .neg (.lit n .int) => some (- (n : Int))
  | _ => none

partial def simp (v : NumTerm) : NumTerm :=
  let v := map simp v
  match v with
  | natToInt x =>
    (match x with
    | lit n _ => lit n .int
    | add x y _ => add (natToInt x) (natToInt y) .int
    | mul x y _ => mul (natToInt x) (natToInt y) .int
    | div x y _ => div (natToInt x) (natToInt y) .edivInt
    | mod x y _ => mod (natToInt x) (natToInt y) .edivInt
    | var _ | sub _ _ _ | neg _ | intToNat _ | natToInt _ => v)
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
        if xd == n then
          let rop :=
            match op, xop with
            | .divNat, .divNat => some .divNat
            | .edivInt, _ => some .edivInt
            | .tdivInt, .edivInt => some .edivInt
            | .tdivInt, .tdivInt => some .tdivInt
            | .fdivInt, .edivInt => some .fdivInt
            | .fdivInt, .fdivInt => some .fdivInt
            | .bdivInt, _ => some .bdivInt
            | _, _ => none
          if let some rop := rop then
            return simp (mod xn n rop)
      if let neg yn := n then
        match op with
        | .edivInt | .tdivInt | .bdivInt =>
          return simp (mod x yn op)
        | _ =>
          pure ()
      return v
  | _ => v

partial def simpv (u : NumTerm) : NumTerm :=
  let v := simp u
  if v.typeOf == u.typeOf then
    v
  else
    panic! s!"simp result changed types:\n  Input: {repr u}\n  Out:   {repr v}"

def litOp (n : Nat) (tp : NumType) := mkOp [] tp fun _ => lit n tp
def addOp (tp : NumType) := mkOp [tp, tp] tp fun a => add (a[0]!) (a[1]!) tp
def subOp (tp : NumType) := mkOp [tp, tp] tp fun a => sub (a[0]!) (a[1]!) tp
def negOp : Op NumType NumTerm := mkOp [.int] .int fun a => neg (a[0]!)
def mulOp (tp : NumType) := mkOp [tp, tp] tp fun a => mul (a[0]!) (a[1]!) tp
def divOp (op : DivMode) (dtp := op.typeOf) := let tp := op.typeOf; mkOp [tp, dtp] tp fun a => div (a[0]!) (a[1]!) op
def modOp (op : DivMode) (dtp := op.typeOf) := let tp := op.typeOf; mkOp [tp, dtp] tp fun a => mod (a[0]!) (a[1]!) op

end NumTerm

open NumTerm

syntax:lead (name := intTestElab) "#intTest" : command

@[command_elab intTestElab]
def elabIntTest : CommandElab := fun _stx => do
  let types : List NumType := [.nat, .int]
  let ops := [
      litOp 0 .nat,
      litOp 1 .nat,
      litOp 2 .nat,
      litOp 0 .int,
      litOp 1 .int,
      litOp 2 .int,
      addOp .nat, addOp .int,
      subOp .nat, subOp .int,
      negOp,
      mulOp .nat, mulOp .int,
      divOp .divNat, divOp .edivInt, divOp .fdivInt, divOp .tdivInt, divOp .bdivInt .nat,
      modOp .divNat, modOp .edivInt, modOp .fdivInt, modOp .tdivInt, modOp .bdivInt .nat,
  ]
  let vars : List (NumType × CoreM Command) := [
      (.nat, `(variable (n : Nat))),
      (.int, `(variable (i : Int)))
  ]
  let stats : GenStats := { maxTermSize := 6, maxDepth := 3, maxVarCount := 2 }
  testNormalForms types ops vars NumTerm.simpv stats

set_option maxHeartbeats 100000000
#intTest
