import Lean

/-!
Tests inductive types with more constructors than fit into the constructor object tag. Unless all
constructors of the type are unboxed scalars, those with index at least 243 store it in an
additional object field: allocation, pattern matching with and without default alternatives,
`ctorIdx`, in-place and copying updates, changing the constructor of an object, decidable equality,
multi-threaded marking, static literals, sharing, and compaction. The sizes cover both sides of the
threshold of 243 constructors, and one type combines the additional field with spill objects.
-/

open Lean

set_option genInjectivity false
set_option genSizeOfSpec false

def check (label : String) (ok : Bool) : IO Unit :=
  IO.println s!"{label}: {ok}"

/--
`many_ctors T n off m k` defines an inductive type `T` with constructors `c0`, ..., `c(n-1)` and a
test `T.test`. Depending on `(i + off) % 3`, the constructor `ci` has no fields, a `Nat` field, or
`m` `Nat` fields followed by a `String` and a `UInt8`; the last shape is replaced by the second one
for `i < k`.
-/
macro "many_ctors " name:ident n:num off:num m:num k:num : command => do
  let n := n.getNat
  let off := off.getNat
  let m := m.getNat
  let k := k.getNat
  let kind (i : Nat) : Nat :=
    if (i + off) % 3 == 2 then (if i ≥ k then 2 else 1) else (i + off) % 3
  let id (s : String) := mkIdent (name.getId.str s)
  let c (i : Nat) := mkIdent (name.getId.str s!"c{i}")
  let xs := (Array.range m).map fun j => mkIdent (.mkSimple s!"x{j}")
  let x0 := xs[0]!
  let sum ← xs.foldlM (fun acc x => `($acc + $x)) (← `(0))
  let ctors ← (Array.range n).mapM fun i =>
    let c := mkIdent (.mkSimple s!"c{i}")
    match kind i with
    | 0 => `(Parser.Command.ctor| | $c:ident)
    | 1 => `(Parser.Command.ctor| | $c:ident (x : Nat))
    | _ => `(Parser.Command.ctor| | $c:ident ($xs* : Nat) (s : String) (b : UInt8))
  let mkCtor (i : Nat) (base : Term) : MacroM Term := do
    match kind i with
    | 0 => `($(c i))
    | 1 => `($(c i) $base)
    | _ =>
      let args ← (Array.range m).mapM fun j => `($base + $(quote j))
      `($(c i) $args* (toString $base) 7)
  let pat (i : Nat) : MacroM Term := do
    match kind i with
    | 0 => `($(c i))
    | 1 => `($(c i) x)
    | _ => `($(c i) $xs* s b)
  let anyPat (i : Nat) : MacroM Term := do
    if kind i == 0 then `($(c i)) else `($(c i) ..)
  let makeAlts ← (Array.range n).mapM fun i => do
    `(Parser.Term.matchAltExpr| | $(quote i) => $(← mkCtor i (← `(base))))
  let makeAlts := makeAlts.push (← `(Parser.Term.matchAltExpr| | _ => $(← mkCtor 0 (← `(base)))))
  let valAlts ← (Array.range n).mapM fun i => do
    let rhs ← match kind i with
      | 0 => `($(quote (1000 * i)))
      | 1 => `($(quote (1000 * i)) + x)
      | _ => `($(quote (1000 * i)) + $sum + s.length + b.toNat)
    `(Parser.Term.matchAltExpr| | $(← pat i) => $rhs)
  let bumpAlts ← (Array.range n).mapM fun i => do
    let rhs ← match kind i with
      | 0 => `($(c i))
      | 1 => `($(c i) (x + 1))
      | _ => `($(c i) ($x0 + 1) $(xs.extract 1 m)* s b)
    `(Parser.Term.matchAltExpr| | $(← pat i) => $rhs)
  let canRot (i : Nat) : Bool := i + 3 < n && kind (i + 3) == kind i
  let rotAlts ← (Array.range n).mapM fun i => do
    let j := if canRot i then i + 3 else i
    let rhs ← match kind i with
      | 0 => `($(c j))
      | 1 => `($(c j) x)
      | _ => `($(c j) $xs* s b)
    `(Parser.Term.matchAltExpr| | $(← pat i) => $rhs)
  -- the first constructor with a field
  let low := if kind 0 != 0 then 0 else 1
  let file := s!"_tmp_ctor_many_ctors_{name.getId}.olean"
  `(inductive $name where
      $ctors:ctor*

    @[noinline] def $(id "make") (i base : Nat) : $name :=
      match i with
      $makeAlts:matchAlt*

    def $(id "lit") : $name :=
      $(← mkCtor (n - 1) (← `(0)))

    def $(id "kind") (i : Nat) : Nat :=
      if (i + $(quote off)) % 3 == 2 then (if i ≥ $(quote k) then 2 else 1) else (i + $(quote off)) % 3

    def $(id "expected") (i base : Nat) : Nat :=
      1000 * i +
        match ($(id "kind") i) with
        | 0 => 0
        | 1 => base
        | _ => $(quote m) * base + $(quote (m * (m - 1) / 2)) + (toString base).length + 7

    @[noinline] def $(id "val") (t : $name) : Nat :=
      match t with
      $valAlts:matchAlt*

    @[noinline] def $(id "bump") (t : $name) : $name :=
      match t with
      $bumpAlts:matchAlt*

    /-- Changes the constructor to the one three positions later if that one has the same fields. -/
    @[noinline] def $(id "rot") (t : $name) : $name :=
      match t with
      $rotAlts:matchAlt*

    @[noinline] def $(id "few") (t : $name) : Nat :=
      match t with
      | $(← anyPat low) => 1
      | $(← anyPat (n - 1)) => 2
      | $(← anyPat (n - 2)) => 3
      | $(← anyPat (n - 3)) => 4
      | _ => 5

    @[noinline] def $(id "onlyLast") (t : $name) : Nat :=
      match t with
      | $(← pat (n - 1)) => 1
      | _ => 0

    @[noinline] def $(id "onlyLow") (t : $name) : Nat :=
      match t with
      | $(← anyPat low) => 1
      | _ => 0

    unsafe def $(id "roundtrip") (ts : Array $name) : IO Nat := do
      let data : ModuleData := { (default : ModuleData) with entries := #[(`entry, ts.map unsafeCast)] }
      saveModuleData $(quote file) `CtorManyCtors data
      let (data, region) ← readModuleData $(quote file)
      let some (_, entries) := data.entries[0]? | throw (IO.userError "missing entry")
      let ts' : Array $name := entries.map unsafeCast
      let r := ts'.foldl (· + $(id "val") ·) 0
      region.free
      IO.FS.removeFile $(quote file)
      return r

    unsafe def $(id "test") : IO Unit := do
      IO.println $(quote (toString name.getId))
      let n := $(quote n)
      for (label, base) in [("small", 5), ("heap", 2 ^ 70)] do
        let mut make := true
        let mut idx := true
        let mut shared := true
        let mut unique := true
        let mut rot := true
        let mut alts := true
        let mut total := 0
        let mut bumps := 0
        for i in [0:n] do
          let e := $(id "expected") i base
          let d := if $(id "kind") i == 0 then 0 else 1
          let r := if i + 3 < n && $(id "kind") (i + 3) == $(id "kind") i then 3000 else 0
          let t := $(id "make") i base
          make := make && $(id "val") t == e
          idx := idx && t.ctorIdx == i
          shared := shared && $(id "val") ($(id "bump") t) == e + d && $(id "val") ($(id "rot") t) == e + r
          -- `u` is unshared
          let mut u := $(id "make") i base
          for _ in [0:3] do
            u := $(id "bump") u
          unique := unique && $(id "val") u == e + 3 * d
          rot := rot && $(id "val") ($(id "rot") u) == e + 3 * d + r
          let few := if i == $(quote low) then 1 else if i + 1 == n then 2 else if i + 2 == n then 3 else if i + 3 == n then 4 else 5
          alts := alts && $(id "few") t == few && $(id "onlyLast") t == (if i + 1 == n then 1 else 0) &&
            $(id "onlyLow") t == (if i == $(quote low) then 1 else 0)
          shared := shared && $(id "val") t == e
          total := total + e
          bumps := bumps + d
        check s!"{label} make" make
        check s!"{label} ctorIdx" idx
        check s!"{label} shared" shared
        check s!"{label} unique" unique
        check s!"{label} rot" rot
        check s!"{label} alts" alts
        let ts := (Array.range n).map ($(id "make") · base)
        let task := Task.spawn fun _ => ts.foldl (fun acc t => acc + $(id "val") ($(id "bump") t)) 0
        check s!"{label} task" (task.get == total + bumps)
        check s!"{label} after task" (ts.foldl (· + $(id "val") ·) 0 == total)
        check s!"{label} shareCommon" ((Lean.ShareCommon.shareCommon ts).foldl (· + $(id "val") ·) 0 == total)
        let roundtrip := $(id "roundtrip")
        check s!"{label} compact" ((← roundtrip ts) == total)
      check "literal" ($(id "val") $(id "lit") == $(id "expected") (n - 1) 0)
      check "bump literal" ($(id "val") ($(id "bump") $(id "lit")) == $(id "expected") (n - 1) 0 + (if $(id "kind") (n - 1) == 0 then 0 else 1))
      check "ctorIdx literal" ($(id "lit").ctorIdx == n - 1))

-- 243 constructors, the most without an additional field
many_ctors T243 243 0 2 0
-- constructor 243 is the only one with an additional field and has no other fields
many_ctors T244 244 0 2 0
-- constructor 243 has other fields
many_ctors U244 244 1 2 0
many_ctors T245 245 0 2 0
many_ctors T300 300 1 2 0
many_ctors U300 300 2 2 0
-- constructor 245 needs both the additional field and a spill object
many_ctors S246 246 0 255 243

deriving instance DecidableEq for T300

/-- `big_enum E n` defines an inductive type `E` with `n` constructors without fields. -/
macro "big_enum " name:ident n:num : command => do
  let ctors ← (Array.range n.getNat).mapM fun i =>
    `(Parser.Command.ctor| | $(mkIdent (.mkSimple s!"c{i}")):ident)
  `(inductive $name where
      $ctors:ctor*)

-- represented by unboxed scalars
big_enum E300 300

@[noinline] def E300.get (i : Nat) : E300 :=
  if i == 243 then .c243 else if i == 299 then .c299 else .c0

unsafe def main : IO Unit := do
  T243.test
  T244.test
  U244.test
  T245.test
  T300.test
  U300.test
  S246.test
  let mut eq := true
  for i in [0:300] do
    let t := T300.make i (2 ^ 70)
    eq := eq && decide (t = T300.make i (2 ^ 70)) && !decide (t = T300.make ((i + 7) % 300) (2 ^ 70)) &&
      !decide (t = T300.bump t) == (T300.kind i != 0)
  check "T300 decEq" eq
  check "enum ctorIdx" ((E300.get 243).ctorIdx == 243 && (E300.get 299).ctorIdx == 299 && (E300.get 0).ctorIdx == 0)
  check "enum boxed ctorIdx" ([E300.get 243, E300.get 299].map (·.ctorIdx) == [243, 299])
  check "enum match" ((match E300.get 243 with | .c243 => 1 | .c299 => 2 | _ => 3) == 1)
