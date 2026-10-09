import Lean

/-!
Tests constructors with more object fields than fit into one constructor object, which are stored in
a chain of spill objects: allocation, projections, scalar fields, pattern matching, in-place and
copying updates, freeing, multi-threaded marking, static literals, sharing, and compaction. The
sizes cover both sides of the threshold of 255 object fields and more than one spill object.
-/

open Lean

set_option genInjectivity false
set_option genSizeOfSpec false

def check (label : String) (ok : Bool) : IO Unit :=
  IO.println s!"{label}: {ok}"

/--
`big_structure S n` defines a structure `S` with `n + 2` object fields (`n` of type `Nat`, a
`String`, and an optional promise) followed by three scalar fields, and a test `S.test`.
-/
macro "big_structure " name:ident n:num : command => do
  let n := n.getNat
  let id (s : String) := mkIdent (name.getId.str s)
  let fld (s : String) := mkIdent (.mkSimple s)
  let nats := (Array.range n).map fun i => fld s!"n{i}"
  let projs := nats.map fun f => mkIdent (name.getId ++ f.getId)
  let args ← (Array.range n).mapM fun i => `(base + $(quote i))
  let lits := (Array.range n).map fun i => (quote i : Term)
  let sum ← projs.foldlM (fun acc p => `($acc + $p s)) (← `(0))
  let first := nats[0]!
  let last := nats.back!
  let expected ← `($(quote n) * base + $(quote (n * (n - 1) / 2)))
  let file := s!"_tmp_ctor_many_fields_{name.getId}.olean"
  `(structure $name where
      ($nats* : Nat)
      ($(fld "str") : String)
      ($(fld "promise") : Option (IO.Promise Unit))
      ($(fld "byte") : UInt8)
      ($(fld "word") : USize)
      ($(fld "float") : Float)

    @[noinline] def $(id "make") (base : Nat) (label : String) : $name :=
      $(id "mk") $args* label none 1 2 3.5

    def $(id "lit") : $name :=
      $(id "mk") $lits* "lit" none 4 5 6.5

    @[noinline] def $(id "sum") (s : $name) : Nat :=
      $sum

    @[noinline] def $(id "ends") (s : $name) : Nat :=
      match s with
      | ⟨$nats,*, _, _, _, _, _⟩ => $first + $last

    @[noinline] def $(id "bump") (s : $name) (i : Nat) : $name :=
      { s with
        $first:ident := $(projs[0]!) s + i
        $last:ident := $(projs.back!) s + 2 * i
        $(fld "str"):ident := $(id "str") s ++ "!"
        $(fld "byte"):ident := $(id "byte") s + 1
        $(fld "word"):ident := $(id "word") s + 3
        $(fld "float"):ident := $(id "float") s + 0.5 }

    def $(id "expected") (base : Nat) : Nat :=
      $expected

    /-- Returns a task that finishes once a promise stored in a dead structure has been freed. -/
    def $(id "dropped") : IO (Task (Option Unit)) := do
      let p ← IO.Promise.new
      let res := p.result?
      let s := { $(id "make") 0 "p" with $(fld "promise"):ident := some p }
      check "promise" ($(id "sum") s == $(id "expected") 0)
      return res

    unsafe def $(id "roundtrip") (s : $name) : IO Nat := do
      let data : ModuleData := { (default : ModuleData) with entries := #[(`entry, #[unsafeCast s])] }
      saveModuleData $(quote file) `CtorManyFields data
      let (data, region) ← readModuleData $(quote file)
      let some (_, #[entry]) := data.entries[0]? | throw (IO.userError "missing entry")
      let s' : $name := unsafeCast entry
      let r := $(id "sum") s' + ($(id "str") s').length
      region.free
      IO.FS.removeFile $(quote file)
      return r

    unsafe def $(id "test") : IO Unit := do
      IO.println $(quote (toString name.getId))
      let s := $(id "make") 100 "s"
      check "make" ($(id "sum") s == $(id "expected") 100)
      check "match" ($(id "ends") s == 200 + $(quote (n - 1)))
      check "scalars" ($(id "str") s == "s" && $(id "byte") s == 1 && $(id "word") s == 2 && $(id "float") s == 3.5)
      -- `t` is unshared from the second iteration on
      let mut t := s
      for i in [0:10] do
        t := $(id "bump") t i
      check "update" ($(id "sum") t == $(id "expected") 100 + 135)
      check "update scalars" ($(id "str") t == "s!!!!!!!!!!" && $(id "byte") t == 11 && $(id "word") t == 32 && $(id "float") t == 8.5)
      check "original" ($(id "sum") s == $(id "expected") 100 && $(id "str") s == "s" && $(id "byte") s == 1)
      let u := $(id "make") (2 ^ 70) "u"
      check "heap fields" ($(id "sum") ($(id "bump") u 1) == $(id "expected") (2 ^ 70) + 3)
      let task := Task.spawn fun _ => $(id "sum") ($(id "bump") u 2)
      check "task" (task.get == $(id "expected") (2 ^ 70) + 6)
      check "after task" ($(id "sum") u == $(id "expected") (2 ^ 70))
      let dropped ← $(id "dropped"):ident
      check "free" (← IO.wait dropped).isNone
      check "literal" ($(id "sum") $(id "lit") == $(id "expected") 0 && $(id "str") $(id "lit") == "lit" && $(id "float") $(id "lit") == 6.5)
      check "shareCommon'" ($(id "sum") (ShareCommon.shareCommon' t) == $(id "expected") 100 + 135)
      check "shareCommon" ($(id "sum") (Lean.ShareCommon.shareCommon t) == $(id "expected") 100 + 135)
      check "shareCommon literal" ($(id "sum") (Lean.ShareCommon.shareCommon $(id "lit")) == $(id "expected") 0)
      let roundtrip := $(id "roundtrip")
      check "compact" ((← roundtrip t) == $(id "expected") 100 + 135 + 11)
      check "compact heap fields" ((← roundtrip u) == $(id "expected") (2 ^ 70) + 1)
      check "compact literal" ((← roundtrip $(id "lit")) == $(id "expected") 0 + 3))

/--
`big_inductive T n` defines an inductive type `T` with two constructors of `n` object fields each
and a test `T.test` exercising reuse across them.
-/
macro "big_inductive " name:ident n:num : command => do
  let n := n.getNat
  let id (s : String) := mkIdent (name.getId.str s)
  let ctor (s : String) := mkIdent (.mkSimple s)
  let xs := (Array.range n).map fun i => mkIdent (.mkSimple s!"x{i}")
  let args ← (Array.range n).mapM fun i => `(base + $(quote i))
  let lits := (Array.range n).map fun i => (quote i : Term)
  let sum ← xs.foldlM (fun acc x => `($acc + $x)) (← `(0))
  let expected ← `($(quote n) * base + $(quote (n * (n - 1) / 2)))
  `(inductive $name where
      | $(ctor "a"):ident ($xs* : Nat)
      | $(ctor "b"):ident ($xs* : Nat)
      | $(ctor "c"):ident (x : Nat)

    @[noinline] def $(id "make") (base : Nat) : $name :=
      $(id "a") $args*

    def $(id "lit") : $name :=
      $(id "b") $lits*

    @[noinline] def $(id "flip") : $name → $name
      | $(id "a") $xs* => $(id "b") $xs*
      | $(id "b") $xs* => $(id "a") $xs*
      | $(id "c") x => $(id "c") (x + 1)

    @[noinline] def $(id "sum") : $name → Nat
      | $(id "a") $xs* => 1 + $sum
      | $(id "b") $xs* => 2 + $sum
      | $(id "c") x => x

    def $(id "expected") (base : Nat) : Nat :=
      $expected

    def $(id "test") : IO Unit := do
      IO.println $(quote (toString name.getId))
      let t := $(id "make") (2 ^ 70)
      check "make" ($(id "sum") t == 1 + $(id "expected") (2 ^ 70))
      check "flip shared" ($(id "sum") ($(id "flip") t) == 2 + $(id "expected") (2 ^ 70))
      check "original" ($(id "sum") t == 1 + $(id "expected") (2 ^ 70))
      check "flip unique" ($(id "sum") ($(id "flip") ($(id "flip") ($(id "flip") t))) == 2 + $(id "expected") (2 ^ 70))
      check "literal" ($(id "sum") $(id "lit") == 2 + $(id "expected") 0)
      check "shareCommon literal" ($(id "sum") (Lean.ShareCommon.shareCommon $(id "lit")) == 2 + $(id "expected") 0)
      check "flip literal" ($(id "sum") ($(id "flip") $(id "lit")) == 1 + $(id "expected") 0))

-- 254 object fields
big_structure S252 252
-- 255 object fields, the most that fit into one constructor object
big_structure S253 253
-- 256 object fields, the fewest that need a spill object
big_structure S254 254
-- three spill objects
big_structure S900 900

big_inductive T254 254
big_inductive T255 255
big_inductive T256 256
-- 254 fields in each of the constructor object and the spill object
big_inductive T508 508
-- one field in a second spill object
big_inductive T509 509
big_inductive T700 700

unsafe def main : IO Unit := do
  S252.test
  S253.test
  S254.test
  S900.test
  T254.test
  T255.test
  T256.test
  T508.test
  T509.test
  T700.test
